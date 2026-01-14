#!/usr/bin/env python3

import subprocess
import sys
import argparse
import csv
import os

def get_script_lines(script_path):
    """
    Reads a script and returns a list of command objects.
    Each object tracks the command string and its completion status.
    """
    try:
        with open(script_path, 'r') as f:
            raw_lines = f.readlines()
    except FileNotFoundError:
        print(f"Error: The file '{script_path}' was not found.")
        sys.exit(1)

    # We store a dict for each line to track state mutable
    commands = [
        {'cmd': line.strip(), 'done': False}
        for line in raw_lines
        if line.strip() and not line.strip().startswith('#')
    ]
    return commands

def process_script_at_timeout(script_lines, timeout):
    """
    Iterates through the script lines.
    - If a line is already 'done', we skip execution and count it.
    - If not, we run it. If it finishes, we mark it 'done' and count it.

    Returns the total count of finished lines (previous + new).
    """
    total_finished = 0

    for line_obj in script_lines:
        # Optimization: If already done in a previous (smaller) timeout,
        # skip execution but increment count.
        if line_obj['done']:
            total_finished += 1
            continue

        # If not done, attempt to run it
        try:
            subprocess.run(
                line_obj['cmd'],
                shell=True,
                executable='/bin/bash',
                timeout=timeout,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL
            )
            # If we reach here, it finished successfully
            line_obj['done'] = True
            total_finished += 1

        except subprocess.TimeoutExpired:
            # It failed to finish; do not increment count, do not mark done
            pass

    return total_finished

def main():
    parser = argparse.ArgumentParser(description="Benchmark multiple bash scripts with optimized incremental timeouts.")
    parser.add_argument("scripts", nargs='+', help="List of bash script files to test")
    parser.add_argument("--output", "-o", required=True, help="Path to the output CSV file")
    parser.add_argument("--start", type=float, required=True, help="Starting timeout in seconds")
    parser.add_argument("--end", type=float, required=True, help="Ending timeout in seconds")
    parser.add_argument("--step", type=float, required=True, help="Timeout increment in seconds")

    args = parser.parse_args()

    if args.start > args.end:
        print("Error: Start timeout cannot be greater than end timeout.")
        sys.exit(1)
    if args.step <= 0:
        print("Error: Step must be positive.")
        sys.exit(1)

    # 1. Initialize State
    # Dictionary mapping: filename -> list of {'cmd': str, 'done': bool}
    scripts_state = {}
    print("Loading scripts and initializing state...")
    for script_file in args.scripts:
        lines = get_script_lines(script_file)
        scripts_state[script_file] = lines
        print(f" -> Loaded '{script_file}' ({len(lines)} executable lines)")

    results = []

    print(f"\nStarting optimized benchmark: {args.start}s to {args.end}s (step {args.step}s)...")

    current_timeout = args.start

    # 2. Main Execution Loop
    while current_timeout <= args.end + (args.step / 10000.0):
        print(f"Testing timeout: {current_timeout:.2f}s...", end='', flush=True)

        row = [current_timeout]

        for script_file in args.scripts:
            # Pass the mutable list of line objects
            # The function will update 'done' statuses in-place
            count = process_script_at_timeout(scripts_state[script_file], current_timeout)
            row.append(count)

        results.append(row)
        print(" Done.")

        current_timeout += args.step

    # 3. Write Data
    headers = ['Timeout (s)'] + [os.path.basename(s) for s in args.scripts]

    try:
        with open(args.output, 'w', newline='') as csvfile:
            writer = csv.writer(csvfile)
            writer.writerow(headers)
            writer.writerows(results)
        print(f"\nSuccess! Data written to '{args.output}'.")
    except IOError as e:
        print(f"\nError writing to file: {e}")

if __name__ == "__main__":
    main()