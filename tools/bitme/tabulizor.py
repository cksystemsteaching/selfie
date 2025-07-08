import csv
import glob
import re
import dataclasses


@dataclasses.dataclass(frozen=True)
class BitmeConfig:
    bvdd_mode: str
    satsolver: str
    max_propagate_bits: int
    max_array_flatten_bits: int


@dataclasses.dataclass
class BenchmarkResult:
    runtime_secs: float
    memory_usage_kb: float


samples: dict[str, dict[BitmeConfig, BenchmarkResult]] = dict()

for f in glob.iglob("bitme-data-*.csv"):
    m = re.match("bitme-data-b(.*)-s(.*)-p(.*)-a(.*)-v(.*).csv", f)
    assert m
    b, s, p, a, _ = m.groups()
    cfg = BitmeConfig(b, s, int(p), int(a))

    with open(f, "r") as f:
        for r in csv.DictReader(f):
            if r["bad_step"]:
                res = BenchmarkResult(
                    runtime_secs=float(r["runtime_secs"]),
                    memory_usage_kb=float(r["memory_usage_kb"]),
                )
                samples.setdefault(r["sample"], dict())[cfg] = res

per_bvdd: dict[str, dict[str, dict[BitmeConfig, BenchmarkResult]]] = dict()
for sample, r in samples.items():
    for cfg, res in r.items():
        per_bvdd.setdefault(
            f"{cfg.bvdd_mode}{cfg.max_propagate_bits}", dict()
        ).setdefault(sample, dict())[cfg] = res

BNUM = [
    "ROABVDD0",
    "ROABVDD1",
    "ROABVDD8",
    "CFLOBVDD8",
]
SAMPLES = list(samples.keys())

print("overview:")
for idx, bvdd in enumerate(BNUM):
    print("\\addplot[point meta=explicit,scatter,only marks,mark=*] coordinates {", end="")
    for sample, r in per_bvdd[bvdd].items():
        if sample.startswith("cflobvdd"):
            continue
        for cfg, res in r.items():
            if cfg.max_array_flatten_bits == (0 if bvdd[-1] in ["0", "1"] else 8):
                print(f"({idx+1},{res.runtime_secs}) [{SAMPLES.index(sample)}]", end=" ")
                break
    print("};")

print()

for bvdd in BNUM:
    print(f"per-array {bvdd}:")
    for sample, r in per_bvdd[bvdd].items():
        if sample.startswith("cflobvdd"):
            continue
        per_arr: dict[int, float] = dict()
        for cfg, res in r.items():
            per_arr[cfg.max_array_flatten_bits] = res.runtime_secs
        if not per_arr:
            continue

        print("\\addplot[point meta=explicit,scatter,mark=*] coordinates {", end="")
        for a in range(0, 8 + 1):
            if a in per_arr:
                print(f"({a},{per_arr[a]}) [{SAMPLES.index(sample)}]", end=" ")
        print("};")
    print()


def cflobvdd_plot(name, metric):
    print()
    print(f"{name} ({metric}):")

    for col, bvdd in [
        ("red", "ROABVDD8"),
        ("blue", "CFLOBVDD8"),
    ]:
        per_v: dict[int, float] = dict()
        for sample, r in per_bvdd[bvdd].items():
            if not sample.startswith(name):
                continue
            for cfg, res in r.items():
                if cfg.max_array_flatten_bits == 8:
                    if metric == "runtime":
                        per_v[int(sample[-3])] = res.runtime_secs
                    elif metric == "memory":
                        per_v[int(sample[-3])] = res.memory_usage_kb / 1024
                    else:
                        assert False

        print(f"\\addplot[color={col},mark=*] coordinates {{", end="")
        for a in range(0, 8 + 1):
            if a in per_v:
                print(f"({a},{per_v[a]})", end=" ")
        print("};")


cflobvdd_plot("cflobvdd-multi-input", "runtime")
cflobvdd_plot("cflobvdd-multi-input", "memory")
cflobvdd_plot("cflobvdd-bit-inversion", "runtime")
cflobvdd_plot("cflobvdd-bit-inversion", "memory")