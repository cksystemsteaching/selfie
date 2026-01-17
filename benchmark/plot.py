#!/usr/bin/env python3

"""
Generate a python script that produces, for a given csv file, a png file that
depicts a 2d graph where the x-axis is derived from the content of the first
column of the csv file. The y-axis is derived from the content of the remaining
columns. Show a separate graph for each remaining column using a unique color
and add a legend derived from the remaining column names. Show the legend as
title on top. Label the y-axis "#solved instances" and use integers only.
make background white. Derive the name of the png file from the name of the csv file.
Format long legends into a multi-line legend that is not wider than the chart.
Add unique dot types for each graph. Only label x-axis if there are data points.
Add prompt as comment.
"""

import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator
import sys
import os
import textwrap
import itertools

def generate_graph(csv_file):
    # Check if file exists
    if not os.path.exists(csv_file):
        print(f"Error: The file '{csv_file}' was not found.")
        return

    # Derive output filename
    base_name = os.path.splitext(csv_file)[0]
    output_file = f"{base_name}.png"

    try:
        # Read the CSV
        df = pd.read_csv(csv_file)

        # Validation
        if len(df.columns) < 2:
            print("Error: CSV must have at least two columns.")
            return

        x_col = df.columns[0]
        y_cols = df.columns[1:]

        # Setup Plot
        fig, ax = plt.subplots(figsize=(10, 6))

        # Set background to white
        fig.patch.set_facecolor('white')
        ax.set_facecolor('white')

        # Define a list of distinct markers
        marker_list = ['o', 's', '^', 'D', 'v', '<', '>', 'p', '*', 'h', 'X', 'd']
        marker_cycle = itertools.cycle(marker_list)

        # Plot Data
        for col in y_cols:
            current_marker = next(marker_cycle)
            ax.plot(df[x_col], df[col], label=col, marker=current_marker)

        # Formatting Y-Axis
        ax.set_ylabel("#solved instances")
        ax.yaxis.set_major_locator(MaxNLocator(integer=True)) # Integers only

        # Formatting X-Axis
        ax.set_xlabel(x_col)
        # Force ticks to appear ONLY at the data points present in the X column
        ax.set_xticks(df[x_col])

        # --- LEGEND FORMATTING ---
        handles, labels = ax.get_legend_handles_labels()

        # Wrap long label text
        labels = [ '\n'.join(textwrap.wrap(l, 25)) for l in labels ]

        # Limit columns to max 4
        max_legend_cols = 4
        actual_cols = min(len(labels), max_legend_cols)

        # Place legend as title on top
        ax.legend(handles, labels,
                  loc='lower center',
                  bbox_to_anchor=(0.5, 1.05),
                  ncol=actual_cols,
                  frameon=False,
                  fontsize='medium',
                  borderaxespad=0)
        # -------------------------

        plt.tight_layout()

        # Save
        plt.savefig(output_file, dpi=300, bbox_inches='tight')
        print(f"Graph saved successfully to '{output_file}'")

    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python plot_csv.py <path_to_csv_file>")
    else:
        generate_graph(sys.argv[1])