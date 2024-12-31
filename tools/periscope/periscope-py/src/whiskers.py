import argparse
import functools
import pathlib

from matplotlib import figure
import matplotlib.pyplot as plt

from periscope_result import BenchResult


def cmp_median(medians: list[float], labels: list[str]):
    def compare(i, j):
        med_cmp = medians[i] - medians[j]
        if med_cmp == 0:
            return labels[i] < labels[j]
        else:
            return med_cmp

    return compare


def plot_whiskers(
    args: argparse.Namespace,
    periscope_results: list[BenchResult],
    figure: figure.Figure,
):
    labels = [b.name for b in periscope_results]
    times = [b.times for pr in periscope_results for b in pr.hyperfine_results()]

    if args.sort_by == "median":
        medians = [b.median for pr in periscope_results for b in pr.hyperfine_results()]
        indices = sorted(
            range(len(labels)),
            key=functools.cmp_to_key(cmp_median(medians, labels)),
        )
        labels = [labels[i] for i in indices]
        times = [times[i] for i in indices]

    _ = figure.subplots(1, 1)
    plt.subplots(figsize=(20, 12), constrained_layout=True)
    boxplot = plt.boxplot(times, vert=True, patch_artist=True)
    cmap = plt.get_cmap("rainbow")
    colors = [cmap(val / len(times)) for val in range(len(times))]

    for patch, color in zip(boxplot["boxes"], colors):
        patch.set_facecolor(color)

    if args.title:
        plt.title(args.title)
    # plt.legend(handles=boxplot["boxes"], labels=labels, loc="best", fontsize="medium")
    plt.title("Solving time and model size")
    plt.ylabel("Time [s]")
    plt.ylim(0, None)
    plt.xticks(list(range(1, len(labels) + 1)), labels, rotation=65)
