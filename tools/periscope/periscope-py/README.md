# PeRISCope - Python script for results visualisation

This is a simple Python script for generating plots of benchmarking results
produced by [`periscope-rs`](../periscope-rs).

## Usage

Make sure you installed all required dependencies:

```sh
pip install -r requirements.txt
```

After that, run the main script file with `--help` flag to get more information: 

```sh
python src/periscope.py --help
```

## Example usage: 

```sh
# Generate a plot with bars for each configuration, overall sort-by median time,
# and scale the y-axis logarithmically. Plot results contained in `results_dir`
# and save the plot to test.png file.
python src/periscope.py --sort-by median --scale log --type cmp-bars -o test.png results_dir
```
