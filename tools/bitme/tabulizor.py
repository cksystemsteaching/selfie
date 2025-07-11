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

for f in glob.iglob("bitme-data-b*-s*-p*-a*-v*.csv"):
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

BTS = [
    ("ROABVDD0", "green,mark=x", "SMT"),
    ("ROABVDD1", "cyan,mark=+", "constant propagation"),
    ("ROABVDD8", "red,mark=*", "ROABVDD domain propagation"),
    ("CFLOBVDD8", "blue,mark=o", "CFLOBVDD domain propagation"),
]
SAMPLES = list(samples.keys())

print("overview:")
for bvdd, style, legend in BTS:
    vs: list[float] = list()
    for sample, r in per_bvdd[bvdd].items():
        if sample.startswith("cflobvdd"):
            continue
        for cfg, res in r.items():
            if cfg.max_array_flatten_bits == (0 if bvdd[-1] in ["0", "1"] else 8):
                vs.append(res.runtime_secs)
    vs.sort()

    print(f"\\addplot[{style}] coordinates {{", end=" ")
    print(f"(0,0) ", end=" ")
    for idx, v in enumerate(vs):
        print(f"({v},{idx+1})", end=" ")
    print(f"({1000},{len(vs)})", end=" ")
    print("};")
    print(f"\\addlegendentry{{{legend}}};")

def sec_overview(templ):
    print()
    print(f"secondary overview ({templ}):")

    for bvdd, _, _ in BTS:
        vs: list[float] = list()
        for sample, r in per_bvdd[bvdd].items():
            if sample.startswith("cflobvdd"):
                continue
            for cfg, res in r.items():
                if cfg.max_array_flatten_bits == (0 if bvdd[-1] in ["0", "1"] else 8):
                    vs.append(res.runtime_secs)
        vs.sort()

        print(f"\\addplot[dashed,no markers,color=gray,forget plot] coordinates {{", end=" ")
        print(f"(0,0) ", end=" ")
        for idx, v in enumerate(vs):
            print(f"({v},{idx+1})", end=" ")
        print(f"({1000},{len(vs)})", end=" ")
        print("};")

    samples2: dict[str, dict[BitmeConfig, BenchmarkResult]] = dict()

    for f in glob.iglob(f"{templ}-b*-s*-p*-a*-v*.csv"):
        m = re.match(f"{templ}-b(.*)-s(.*)-p(.*)-a(.*)-v(.*).csv", f)
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
                    samples2.setdefault(r["sample"], dict())[cfg] = res

    per_bvdd2: dict[str, dict[str, dict[BitmeConfig, BenchmarkResult]]] = dict()
    for sample, r in samples2.items():
        for cfg, res in r.items():
            per_bvdd2.setdefault(
                f"{cfg.bvdd_mode}{cfg.max_propagate_bits}", dict()
            ).setdefault(sample, dict())[cfg] = res

    for bvdd, style, legend in BTS:
        vs: list[float] = list()
        for sample, r in per_bvdd2[bvdd].items():
            if sample.startswith("cflobvdd"):
                continue
            for cfg, res in r.items():
                if cfg.max_array_flatten_bits == (0 if bvdd[-1] in ["0", "1"] else 8):
                    vs.append(res.runtime_secs)
        vs.sort()

        print(f"\\addplot[{style}] coordinates {{", end=" ")
        print(f"(0,0) ", end=" ")
        for idx, v in enumerate(vs):
            print(f"({v},{idx+1})", end=" ")
        print(f"({1000},{len(vs)})", end=" ")
        print("};")
        print(f"\\addlegendentry{{{legend}}};")

sec_overview("bitme-data-rotorF")
sec_overview("bitme-data-rotor3")

print()
print(f"per-array (cnt):")
for bvdd, style, legend in BTS:
    arr_cnts: dict[int, int] = dict()
    for sample, r in per_bvdd[bvdd].items():
        for cfg, res in r.items():
            if not sample.startswith("cflobvdd"):
                arr_cnts[cfg.max_array_flatten_bits] = (
                    arr_cnts.get(cfg.max_array_flatten_bits, 0) + 1
                )

    print(f"\\addplot[{style}] coordinates {{", end=" ")
    for a in [0, 4, 8]:
        print(f"({a},{arr_cnts.get(a, 0)})", end=" ")
    print("};")
    print(f"\\addlegendentry{{{legend}}};")

print()
print(f"per-array (avg):")
for bvdd, style, legend in BTS:
    arr_avg: dict[int, list[float]] = dict()
    for sample, r in per_bvdd[bvdd].items():
        for cfg, res in r.items():
            if not sample.startswith("cflobvdd"):
                arr_avg.setdefault(cfg.max_array_flatten_bits, []).append(
                    res.runtime_secs
                )

    print(f"\\addplot[{style}] coordinates {{", end=" ")
    for a in [0, 4, 8]:
        if a in arr_avg:
            print(f"({a},{sum(arr_avg[a]) / len(arr_avg[a])})", end=" ")
    print("};")
    print(f"\\addlegendentry{{{legend}}};")


def cflobvdd_plot(name, metric):
    print()
    print(f"{name} ({metric}):")

    for bvdd, style, legend in BTS:
        if "domain propagation" not in legend:
            continue

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

        print(f"\\addplot[{style}] coordinates {{", end="")
        for a in range(0, 8 + 1):
            if a in per_v:
                print(f"({a},{per_v[a]})", end=" ")
        print("};")


cflobvdd_plot("cflobvdd-multi-input", "runtime")
cflobvdd_plot("cflobvdd-multi-input", "memory")
cflobvdd_plot("cflobvdd-bit-inversion", "runtime")
cflobvdd_plot("cflobvdd-bit-inversion", "memory")
