#!/usr/bin/env python3
"""
Unified test runner with execution modes:
- Default: Run all tests
- -u/--unit: Unit tests only
- -i/--integration: Integration tests only

Specific argument for pytest can also be passed.
"""
import argparse
import subprocess
import sys
from pathlib import Path

def run_tests(test_paths: list, extra_args: list = None):
    """Execute pytest with given paths and arguments."""
    cmd = [
        sys.executable, "-m", "pytest",
        "-v",
        "--durations=5",
        *test_paths,
        *(extra_args or [])
    ]
    result = subprocess.run(cmd, cwd=Path(__file__).parent)
    return result.returncode

def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group()
    group.add_argument("-u", "--unit", action="store_true", help="Run only unit tests")
    group.add_argument("-i", "--integration", action="store_true", help="Run only integration tests")
    args, pytest_args = parser.parse_known_args()

    test_paths = []
    if args.unit:
        test_paths.append("tests/unit/")
    elif args.integration:
        test_paths.append("tests/integration/")
    else:  # Default: run both
        test_paths.extend(["tests/unit/", "tests/integration/"])

    sys.exit(run_tests(test_paths, pytest_args))

if __name__ == "__main__":
    main()