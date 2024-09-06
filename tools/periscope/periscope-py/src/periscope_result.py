import json
from typing import Optional
import jsonpickle
from os import listdir
from os.path import isfile


class HyperfineResult:
    command: str
    mean: float
    stddev: float
    median: float
    user: float
    system: float
    min: float
    max: float
    times: list[float]
    exit_codes: list[int]

    def __init__(
        self,
        command,
        mean,
        stddev,
        median,
        user,
        system,
        min,
        max,
        times,
        exit_codes,
    ) -> None:
        self.command = command
        self.mean = mean
        self.stddev = stddev
        self.median = median
        self.user = user
        self.system = system
        self.min = min
        self.max = max
        self.times = times
        self.exit_codes = exit_codes


def to_hyperfine_result(input: dict) -> HyperfineResult:
    command, mean, stddev, median, user, system, min, max, times, exit_codes = (
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
    )
    if "command" in input:
        command = input["command"]
    if "mean" in input:
        mean = input["mean"]
    if "stddev" in input:
        stddev = input["stddev"]
    if "median" in input:
        median = input["median"]
    if "user" in input:
        user = input["user"]
    if "system" in input:
        system = input["system"]
    if "min" in input:
        min = input["min"]
    if "max" in input:
        max = input["max"]
    if "times" in input:
        times = input["times"]
    if "exit_codes" in input:
        exit_codes = input["exit_codes"]
    if (
        command is None
        or mean is None
        or stddev is None
        or median is None
        or user is None
        or system is None
        or min is None
        or max is None
        or times is None
        or exit_codes is None
    ):
        raise Exception("Invalid JSON format for HyperfineResult")
    else:
        return HyperfineResult(
            command, mean, stddev, median, user, system, min, max, times, exit_codes
        )


class Hyperfine:
    results: list[HyperfineResult]

    def __init__(self, results) -> None:
        self.results = results


def to_hyperfine(input: dict) -> Hyperfine:
    results = []
    if "results" in input:
        results = [to_hyperfine_result(res) for res in input["results"]]

    return Hyperfine(results)


class PeriscopeProp:
    kind: str
    name: str
    node: int
    idx: int

    def __init__(self, kind, name, node, idx) -> None:
        self.kind = kind
        self.name = name
        self.node = node
        self.idx = idx


def to_prop(input: dict) -> PeriscopeProp:
    kind, name, node, idx = (None, None, None, None)

    if "kind" in input:
        kind = input["kind"]

    if "name" in input:
        name = input["name"]

    if "node" in input:
        node = input["node"]

    if "idx" in input:
        idx = input["idx"]

    if kind is None or name is None or node is None or idx is None:
        raise Exception("Invalid JSON format for PeriscopeProp")
    else:
        return PeriscopeProp(kind, name, node, idx)


class PeriscopeResult:
    props: list[PeriscopeProp]
    steps: Optional[int]
    hyperfine: Hyperfine
    wc_raw: int
    wc_btormc_dump: int

    def __init__(self, props, steps, hyperfine, wc_raw, wc_btormc_dump):
        self.props = props
        self.steps = steps
        self.hyperfine = hyperfine
        self.wc_raw = wc_raw
        self.wc_btormc_dump = wc_btormc_dump


def to_per_result(input: dict) -> PeriscopeResult:
    props, steps, hyperfine, wc_raw, wc_btormc_dump = (
        [],
        None,
        None,
        None,
        None,
    )

    if "props" in input:
        props = [to_prop(prop) for prop in input["props"]]

    if "steps" in input:
        steps = input["steps"]

    if "hyperfine" in input:
        hyperfine = to_hyperfine(input["hyperfine"])

    if "wc_raw" in input:
        wc_raw = input["wc_raw"]

    if "wc_btormc_dump" in input:
        wc_btormc_dump = input["wc_btormc_dump"]

    if props is None or hyperfine is None or wc_raw is None or wc_btormc_dump is None:
        raise Exception("Invalid JSON format for PeriscopeResult")
    else:
        return PeriscopeResult(props, steps, hyperfine, wc_raw, wc_btormc_dump)


class PeriscopeResultEnum:
    Success: Optional[PeriscopeResult]
    Failed: Optional[PeriscopeResult]


class BenchResult:
    name: str
    results: PeriscopeResult
    failed: bool

    def __init__(self, name: str, results: dict, failed: bool):
        self.name = name
        self.results = to_per_result(results)
        self.failed = failed

    def hyperfine_results(self) -> list[HyperfineResult]:
        return self.results.hyperfine.results


def to_bench_result(name: str, pre: dict) -> BenchResult:
    if "Success" in pre:
        return BenchResult(name, pre["Success"], False)
    elif "Failed" in pre:
        return BenchResult(name, pre["Failed"], True)
    else:
        raise Exception("Invalid JSON format for bench result")


def results_from_file(path: str) -> list[BenchResult]:
    with open(path, encoding="utf-8") as f:
        results_file = json.load(f)

    test = jsonpickle.decode(
        json.dumps(results_file),
        classes=(
            PeriscopeResult,
            PeriscopeResultEnum,
            PeriscopeProp,
            Hyperfine,
            HyperfineResult,
        ),
    )

    if isinstance(test, dict):
        return [to_bench_result(name, pre) for name, pre in test.items()]
    else:
        raise Exception("Invalid JSON format")
