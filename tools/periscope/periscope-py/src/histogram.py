import argparse

from matplotlib import figure, pyplot as plt
import numpy as np

from periscope_result import BenchResult


def cmp_wc(labels: list[str], periscope_results: list[BenchResult]):
    def compare(i, j):
        wc_i = periscope_results[i].wc
        wc_j = periscope_results[j].wc
        if wc_i == wc_j:
            return labels[i] < labels[j]
        else:
            return wc_i - wc_j

    return compare


def plot_histogram(
    args: argparse.Namespace,
    periscope_results: list[BenchResult],
    figure: figure.Figure,
    of_dump: bool,
):
    labels = [b.name for b in periscope_results]
    all_times = [b.times for pr in periscope_results for b in pr.hyperfine_results()]

    t_min = np.min(list(map(np.min, all_times)))
    t_max = np.max(list(map(np.max, all_times)))

    if of_dump:
        wcs = [pr.results.wc_btormc_dump for pr in periscope_results]
    else:
        wcs = [pr.results.wc_raw for pr in periscope_results]

    times = list(map(np.min, all_times))

    _ = figure.subplots(1, 1)
    cmap = plt.get_cmap("rainbow")
    colors = [cmap(val / len(times)) for val in range(len(times))]
    plt.bar(x=times, height=wcs, label=labels, color=colors, width=5)

    plt.title("Solving time and model size")
    plt.xlabel("Time [s]")

    if of_dump:
        plt.ylabel("Model Size after btormc dump [#chars]")
    else:
        plt.ylabel("Model Size [#chars]")

    plt.xticks(np.arange(np.floor(t_min), np.floor(t_max), step=10))
    plt.xticks(
        list(map(np.min, all_times)),
        labels,
        rotation=65,
        minor=True,
    )

    for xtick, color in zip(plt.gca().get_xticklabels(which="minor"), colors):
        xtick.set_color(color)
