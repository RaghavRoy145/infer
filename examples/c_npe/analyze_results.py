#!/usr/bin/env python3
"""
Analyze provenfix results for small-progs tests.
Checks which test files have corresponding detail.txt files.
"""

import os
from pathlib import Path
from typing import List, Tuple

def get_test_files(test_dir: Path) -> List[str]:
    """Get all .c test files from the directory."""
    if not test_dir.exists():
        raise FileNotFoundError(f"Test directory not found: {test_dir}")

    return [f.stem for f in test_dir.glob("*.c")]

def check_results(test_names: List[str], results_dir: Path) -> Tuple[List[str], List[str]]:
    """Check which tests have detail.txt files."""
    with_details = []
    without_details = []

    for test_name in test_names:
        detail_file = results_dir / f"{test_name}_detail.txt"
        if detail_file.exists():
            with_details.append(test_name)
        else:
            without_details.append(test_name)

    return with_details, without_details

def main():
    base_dir = Path(__file__).parent
    test_dir = base_dir / "small-progs"
    results_dir = base_dir / "provenfix-results/small-programs/infer_small_progs_results"

    print("Analyzing Provenfix Results")
    print("=" * 60)
    print(f"Test directory: {test_dir}")
    print(f"Results directory: {results_dir}")
    print()

    # Get all test files
    test_names = sorted(get_test_files(test_dir))
    print(f"Found {len(test_names)} test files (.c)")
    print()

    # Check for detail.txt files
    with_details, without_details = check_results(test_names, results_dir)

    # Report missing files
    if without_details:
        print("Tests WITHOUT detail.txt files:")
        print("-" * 60)
        for test in without_details:
            print(f"  ✗ {test}")
        print()

    # Report tests with details
    print("Tests WITH detail.txt files:")
    print("-" * 60)
    for test in with_details:
        detail_file = results_dir / f"{test}_detail.txt"
        size = detail_file.stat().st_size
        print(f"  ✓ {test:<30} ({size:,} bytes)")
    print()

    # Summary
    print("Summary:")
    print("=" * 60)
    print(f"Total test files:           {len(test_names)}")
    print(f"With detail.txt:            {len(with_details)}")
    print(f"WITHOUT detail.txt:         {len(without_details)}")
    print(f"Coverage:                   {len(with_details)/len(test_names)*100:.1f}%")

    return 0 if len(without_details) == 0 else 1

if __name__ == "__main__":
    exit(main())