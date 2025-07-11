from __future__ import annotations

import argparse
import csv
import dataclasses
import enum
import multiprocessing
import os
import re
import statistics
import subprocess
import threading
import traceback
import typing
from dataclasses import dataclass
from pathlib import Path

SELFIE_DIR = Path(__file__).parent.parent.parent

ROTOR = SELFIE_DIR.joinpath("rotor")
BITME = SELFIE_DIR.joinpath("tools/bitme.py")
SAMPLES_DIR = SELFIE_DIR.joinpath("examples/symbolic")

if not ROTOR.is_file():
    raise Exception(
        f"rotor binary not found at {ROTOR}; please compile it using 'make rotor'"
    )


@dataclass
class RotorConfig:
    target_exit_code: int
    bytes_to_read: int
    heap_allowance: int
    stack_allowance: int
    machine_32bit: bool
    machine_riscuonly: bool


# rotor configuration used for sample collection
# TODO: allow each sample to specify its own options
ROTOR_CONFIG = RotorConfig(1, 1, 128, 2048, False, True)


def compile_rotor(config: RotorConfig, sample: Path):
    # Check if the sample specifies its own number of input bytes
    with sample.open("r") as f:
        m = re.match("analyzor-input-bytes: ([0-9]+)", f.read())
        if m:
            config = dataclasses.replace(config, bytes_to_read=int(m.group(1)))

    model = sample.with_name(f"{sample.stem}-rotorized.btor2")
    model.unlink(missing_ok=True)

    args = [
        ROTOR,
        "-c",
        sample,
        "-",
        str(config.target_exit_code),
        "-bytestoread",
        str(config.bytes_to_read),
        "-heapallowance",
        str(config.heap_allowance),
        "-stackallowance",
        str(config.stack_allowance),
    ]

    if config.machine_32bit:
        args.insert(1, "-m32")
    if config.machine_riscuonly:
        args.append("-riscuonly")

    proc = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if proc.returncode != 0:
        print()
        print(f"Failed to compile sample '{sample}'!")
        print(f"Command Line: {" ".join(map(str, proc.args))}")
        print()
        print(proc.stdout.decode())
        print()
        proc.check_returncode()

    assert model.is_file(), f"rotor model '{model}' doesn't exist after compilation"

    return model


@dataclass
class BitmeConfig:
    bvdd_mode: BitmeBVDDMode
    satsolver: BitmeSatSolver
    max_propagate_bits: int
    max_array_flatten_bits: int
    timeout: float


class BitmeBVDDMode(enum.StrEnum):
    BVDD = enum.auto()
    ROABVDD = enum.auto()
    CFLOBVDD = enum.auto()

    def __repr__(self) -> str:
        return repr(self.name)


class BitmeSatSolver(enum.StrEnum):
    NONE = enum.auto()
    Z3 = enum.auto()
    BITWUZLA = enum.auto()

    def __repr__(self) -> str:
        return repr(self.name)


@dataclass
class BitmeResult:
    runtime_secs: float
    memory_usage_kb: float
    bad_state: str
    bad_step: int
    bad_input: bytes

    def __str__(self) -> str:
        return f"runtime: {self.runtime_secs:.2f}secs, memory usage: {self.memory_usage_kb / 1024:.2f}MB, reached bad state '{self.bad_state}' after {self.bad_step} steps with input '{self.bad_input.hex()}'"


def run_bitme(config: BitmeConfig, model: Path) -> BitmeResult:
    BVDD_FLAGS = {
        BitmeBVDDMode.BVDD: "--use-BVDD",
        BitmeBVDDMode.ROABVDD: "--use-ROABVDD",
        BitmeBVDDMode.CFLOBVDD: "--use-CFLOBVDD",
    }
    SATSOLVER_FLAGS = {
        BitmeSatSolver.NONE: "",  # - default mode
        BitmeSatSolver.Z3: "--use-Z3",
        BitmeSatSolver.BITWUZLA: "--use-bitwuzla",
    }

    args = [
        BITME,
        "-analyzor",
        BVDD_FLAGS[config.bvdd_mode],
        SATSOLVER_FLAGS[config.satsolver],
        "-propagate",
        str(config.max_propagate_bits),
        "-array",
        str(config.max_array_flatten_bits),
        model,
    ]

    proc = subprocess.Popen(
        args=[a for a in args if a != ""],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        stdin=subprocess.DEVNULL,
    )

    try:
        # Jank way to have an wait4 with a timeout
        ret: tuple = ()
        stdout = b""

        def read_thread():
            nonlocal stdout
            assert proc.stdout is not None
            stdout = proc.stdout.read()

        def wait_thread():
            nonlocal ret
            ret = os.wait4(proc.pid, 0)

        wt = threading.Thread(target=wait_thread)
        rt = threading.Thread(target=read_thread)
        wt.start()
        rt.start()

        wt.join(config.timeout)
        if wt.is_alive():
            raise TimeoutError(f"bitme timed out after {config.timeout}secs")
        else:
            rt.join()

        _, retcode, rusage = ret
    finally:
        proc.kill()

    if config.satsolver == BitmeSatSolver.Z3:
        assert (
            not b"Z3 is not available" in stdout
        ), "Z3 is not installed; BitmeSatSolver.Z3 is unavailable"
    elif config.satsolver == BitmeSatSolver.BITWUZLA:
        assert (
            not b"bitwuzla is not available" in stdout
        ), "bitwuzla is not installed; BitmeSatSolver.BITWUZLA is unavailable"

    if retcode != 0:
        print()
        print(f"bitme errored while running model '{model}'!")
        print(f"Command Line: {" ".join(map(str, args))}")
        print()
        print(stdout.decode())
        print()
        raise subprocess.CalledProcessError(retcode, proc.args)

    analyzor_data: dict[str, str] = {}
    for line in stdout.splitlines():
        if line.startswith(b"analyzor#"):
            key, val = line[9:].decode().split("=", maxsplit=1)
            analyzor_data[key] = val

    bad_input = bytearray()
    while True:
        inp = analyzor_data.get(f"input:input-buffer-{len(bad_input)}", None)
        if inp is not None:
            bad_input.append(int(inp))
        else:
            break

    return BitmeResult(
        runtime_secs=rusage.ru_utime,
        memory_usage_kb=rusage.ru_maxrss,
        bad_state=analyzor_data["bad"],
        bad_step=int(analyzor_data["step"]),
        bad_input=bytes(bad_input),
    )


class Arguments:
    num_workers: int
    average_of: int
    samples: list[Path]
    out_file: Path

    bvdd_modes: list[BitmeBVDDMode]
    satsolvers: list[BitmeSatSolver]
    max_propagate_bits: list[int]
    max_array_flatten_bits: (
        list[int] | None
    )  # None means inherit value of max_propagate_bits
    machine_32bit: bool
    machine_fullriscv: bool
    timeout: float


cpus = os.cpu_count()
assert cpus is not None

ap = argparse.ArgumentParser(
    description="bitme process_cpu_count / sample collection tool"
)
ap.add_argument(
    "-w",
    "--num-workers",
    default=cpus // 2,
    dest="num_workers",
    type=int,
)
ap.add_argument("-v", "--average-of", dest="average_of", default=1, type=int)
ap.add_argument("-o", "--out-file", dest="out_file", type=Path)
ap.add_argument(
    "samples",
    nargs=argparse.REMAINDER,
    type=Path,
)

ap.add_argument(
    "-b",
    "--bvdd-mode",
    action="append",
    dest="bvdd_modes",
    type=BitmeBVDDMode,
    required=True,
)
ap.add_argument(
    "-s",
    "--sat-solver",
    action="append",
    dest="satsolvers",
    type=BitmeSatSolver,
    required=True,
)
ap.add_argument(
    "-p",
    "--max-propagate-bits",
    action="append",
    dest="max_propagate_bits",
    type=int,
    required=True,
)
ap.add_argument(
    "-a",
    "--max-array-flatten-bits",
    action="append",
    dest="max_array_flatten_bits",
    type=int,
)
ap.add_argument(
    "-3",
    "--32-bit",
    action="store_true",
    dest="machine_32bit",
)
ap.add_argument(
    "-f",
    "--full-riscv",
    action="store_true",
    dest="machine_fullriscv",
)
ap.add_argument(
    "-t",
    "--timeout",
    dest="timeout",
    default=900,
    type=float,
)

args: Arguments = typing.cast(Arguments, ap.parse_args())

ROTOR_CONFIG.machine_32bit = args.machine_32bit
ROTOR_CONFIG.machine_riscuonly = not args.machine_fullriscv

if len(args.samples) == 0:
    args.samples = [SAMPLES_DIR]

samples: list[Path] = []
for sample in args.samples:
    if sample.is_file():
        samples.append(sample)
    elif sample.is_dir():
        samples.extend(map(SAMPLES_DIR.joinpath, sample.glob("*.c")))
    else:
        print(f"Sample file '{sample}' doesn't exist!")
        exit(1)


@dataclass
class BenchmarkResult:
    sample: str
    runtime_secs: float
    memory_usage_kb: float
    bad_state: str
    bad_step: int
    bad_input: str  # hex-string


@dataclass
class FailedBenchmarkResult:
    sample: str


bitme_config: BitmeConfig


def run_sample(sample: Path) -> BenchmarkResult | FailedBenchmarkResult:
    try:
        runs = []
        for run_num in range(1, args.average_of + 1):
            print(f"[W:{os.getpid()}] Running sample '{sample.name}' run {run_num}...")

            model = compile_rotor(ROTOR_CONFIG, sample)
            result = run_bitme(bitme_config, model)
            runs.append(result)

            print(
                f"[W:{os.getpid()}] Finished running sample '{sample.name}' run {run_num}; benchmark result: {result}"
            )

            if run_num > 1:
                assert (
                    result.bad_state == runs[0].bad_state
                    and result.bad_step == runs[0].bad_step
                    and result.bad_input == runs[0].bad_input
                ), f"diverging bitme result on run {run_num}"

        benchmark = BenchmarkResult(
            sample=sample.name,
            runtime_secs=statistics.fmean(r.runtime_secs for r in runs),
            memory_usage_kb=statistics.fmean(r.memory_usage_kb for r in runs),
            bad_state=runs[0].bad_state,
            bad_step=runs[0].bad_step,
            bad_input=runs[0].bad_input.hex(),
        )

        if args.average_of > 1:
            aggr_result = BitmeResult(
                runtime_secs=benchmark.runtime_secs,
                memory_usage_kb=benchmark.memory_usage_kb,
                bad_state=benchmark.bad_state,
                bad_step=benchmark.bad_step,
                bad_input=bytes.fromhex(benchmark.bad_input),
            )
            print(
                f"[W:{os.getpid()}] Finished all runs of sample '{sample.name}'; aggregated benchmark results: {aggr_result}"
            )

        return benchmark
    except KeyboardInterrupt:
        raise
    except Exception as err:
        print(
            f"[W:{os.getpid()}] Error while running sample '{sample.name}': {type(err).__name__}: {err}"
        )
        traceback.print_exc()

        with open("errors.txt", "a+") as f:
            f.write(
                f"Error while running sample '{sample.name}' with bitme config {bitme_config}: {type(err).__name__}: {err}\n"
            )

        return FailedBenchmarkResult(sample.name)


def run_samples():
    print(
        f"Running {len(samples)} samples using {args.num_workers} worker processes (taking average of {args.average_of} runs per sample)"
    )
    print(f"bitme config: {bitme_config}")
    print()

    with multiprocessing.Pool(processes=args.num_workers) as p:
        try:
            benchmarks = list(p.map(run_sample, samples))
        except KeyboardInterrupt:
            exit()

    out_file = args.out_file or Path("bitme-data.csv")
    out_file = out_file.with_stem(
        f"{out_file.stem}-b{bitme_config.bvdd_mode.name}-s{bitme_config.satsolver.name}-p{bitme_config.max_propagate_bits}-a{bitme_config.max_array_flatten_bits}-v{args.average_of}"
    )

    print()
    print(
        f"Finished running {len(samples)} samples; saving {len(benchmarks)} benchmark results to {out_file}"
    )
    print()

    with open(out_file, "w") as f:
        writer = csv.DictWriter(
            f, fieldnames=[f.name for f in dataclasses.fields(BenchmarkResult)]
        )
        writer.writeheader()
        writer.writerows(dataclasses.asdict(b) for b in benchmarks)


for mode in args.bvdd_modes:
    for satsolver in args.satsolvers:
        for max_propagate_bits in args.max_propagate_bits:
            for max_array_flatten_bits in args.max_array_flatten_bits or [
                max_propagate_bits
            ]:
                bitme_config = BitmeConfig(
                    bvdd_mode=mode,
                    satsolver=satsolver,
                    max_propagate_bits=max_propagate_bits,
                    max_array_flatten_bits=max_array_flatten_bits,
                    timeout=args.timeout,
                )
                run_samples()
