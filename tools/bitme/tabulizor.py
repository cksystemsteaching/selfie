import csv
import glob
import re
import dataclasses
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker


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

### FIGURE 1: -propagate / -array vs runtime (per BVDD type)

per_bvdd: dict[str, dict[str, dict[BitmeConfig, BenchmarkResult]]] = dict()
for sample, r in samples.items():
    for cfg, res in r.items():
        per_bvdd.setdefault(cfg.bvdd_mode, dict()).setdefault(sample, dict())[cfg] = res

BVDD_COLORS = {
    "BVDD": "green",
    "ROABVDD": "blue",
    "CFLOBVDD": "purple",
}

for bvdd, r in per_bvdd.items():
    avg_pts: dict[int, list[float]] = dict()
    for sample, r in r.items():
        pts = []
        for cfg, res in r.items():
            x = cfg.max_propagate_bits
            y = res.runtime_secs

            pts.append((x, y))
            avg_pts.setdefault(x, []).append(y)

        pts.sort()
        plt.plot(
            [p[0] for p in pts],
            [p[1] for p in pts],
            marker="o",
            label=f"{bvdd} - {sample}",
            alpha=0.1,
            color=BVDD_COLORS[bvdd],
        )

    pts = []
    for x, ys in avg_pts.items():
        pts.append((x, sum(ys) / len(ys)))

    pts.sort()
    plt.plot(
        [p[0] for p in pts],
        [p[1] for p in pts],
        label=f"{bvdd} - MED",
        color=BVDD_COLORS[bvdd],
    )

plt.xlabel("-propagate / -array")
plt.ylabel("Runtime (s)")
plt.gca().yaxis.set_major_formatter(ticker.FormatStrFormatter("%.fs"))
plt.show()

del per_bvdd["BVDD"]

### FIGURE 2: per-sample BVDD comparison (for p8, absolute differences)
sample_names = [
    s for s, r in samples.items() if any(res.max_propagate_bits == 8 for res in r)
]

for i, (bvdd, r) in enumerate(per_bvdd.items()):
    for j, sample in enumerate(sample_names):
        for cfg, res in r[sample].items():
            if cfg.max_propagate_bits == 8:
                plt.bar(
                    [j + i * 0.25],
                    [res.runtime_secs],
                    0.25,
                    label=bvdd,
                    color=BVDD_COLORS[bvdd],
                )

plt.ylabel("Runtime (s)")
plt.xticks(range(len(sample_names)), sample_names, rotation=-20)
plt.gca().yaxis.set_major_formatter(ticker.FormatStrFormatter("%.fs"))
plt.show()

### FIGURE 3: per-sample BVDD comparison (for p8, absolute differences)

for i, sample in enumerate(sample_names):
    bvdd_vals: dict[str, float] = dict()
    for cfg, res in samples[sample].items():
        if cfg.max_propagate_bits == 8:
            bvdd_vals[cfg.bvdd_mode] = res.runtime_secs

    assert "ROABVDD" in bvdd_vals and "CFLOBVDD" in bvdd_vals
    plt.bar([i], [bvdd_vals["CFLOBVDD"] / bvdd_vals["ROABVDD"] * 100], 0.5)

plt.axhline(y=100, linestyle="--")
plt.ylabel("Runtime rel. diff. ROABVDD / CFLOBVDD")
plt.xticks(range(len(sample_names)), sample_names, rotation=-20)
plt.gca().yaxis.set_major_formatter(ticker.FormatStrFormatter("%.f%%"))
plt.show()
