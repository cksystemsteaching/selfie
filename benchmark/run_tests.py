#!/usr/bin/env python3
"""Run BT integration tests locally."""
import subprocess
import sys
from pathlib import Path

def main():
    project_root = Path(__file__).parent
    test_cmd = [
        sys.executable, "-m", "pytest",
        "tests/", "-v",
        "--durations=5"  # Show slowest tests
    ]
    
    print(f"Running tests in: {project_root}")
    result = subprocess.run(test_cmd, cwd=project_root)
    sys.exit(result.returncode)

if __name__ == "__main__":
    main()