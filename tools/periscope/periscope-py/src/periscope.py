#!/usr/bin/env python

"""This program shows `hyperfine` benchmark results as a box and whisker plot.

Quoting from the matplotlib documentation:
    The box extends from the lower to upper quartile values of the data, with
    a line at the median. The whiskers extend from the box to show the range
    of the data. Flier points are those past the end of the whiskers.
"""

import argparse
from logging import error

from os import listdir
from os.path import isfile, join

import matplotlib
import matplotlib.pyplot as plt

import whiskers
import cmp_bars
import histogram
import periscope_result


def main(args: argparse.Namespace):
    figure = plt.figure(figsize=(20, 15), constrained_layout=True)

    matplotlib.rcParams.update({"font.size": 16})

    match args.type:
        case "whisker":
            periscope_results = periscope_result.results_from_file(args.path)
            whiskers.plot_whiskers(args, periscope_results, figure)
        case "cmp-bars":
            figure = plt.figure(figsize=(20, 15), constrained_layout=True)

            if isfile(args.path):
                error(f"'{args.path}' is not a directory.")

            files_with_results = {}
            for file in listdir(args.path):
                periscope_file = periscope_result.results_from_file(
                    join(args.path, file)
                )
                files_with_results[file] = periscope_file

            cmp_bars.plot_cmp_bars(args, files_with_results, figure)
        case "histogram":
            figure = plt.figure(figsize=(20, 15), constrained_layout=True)
            periscope_results = periscope_result.results_from_file(args.path)
            histogram.plot_histogram(args, periscope_results, figure, of_dump=False)
        case "histogram-after-dump":
            periscope_results = periscope_result.results_from_file(args.path)
            histogram.plot_histogram(args, periscope_results, figure, of_dump=True)
        case _:
            print("Unknown type passed.")
            return

    if args.output:
        plt.savefig(args.output)
    else:
        plt.show()


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "path", help="JSON file or path with json files with benchmark results"
    )
    parser.add_argument("--title", help="Plot Title")
    parser.add_argument("--sort-by", choices=["median", "wc"], help="Sort method")
    parser.add_argument(
        "--scale", choices=["linear", "log"], help="Scaling of the plog"
    )
    parser.add_argument(
        "--type",
        choices=["whisker", "cmp-bars", "histogram", "histogram-after-dump"],
        help="Creates a histogram with word count of \
        (dump of ) the model on y axis and the time on x axis \
        for each file.",
    )
    parser.add_argument("-o", "--output", help="Save image to the given filename.")

    return parser.parse_args()


if __name__ == "__main__":
    args = parse_args()
    main(args)
