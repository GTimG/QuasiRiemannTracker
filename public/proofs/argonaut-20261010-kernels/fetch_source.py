#!/usr/bin/env python3
"""Fetch the exact original Argonaut release without executing its build scripts.

Usage: python3 fetch_source.py --output EMPTY_DIRECTORY
The retained original helper checks the release size and SHA256 before extraction.
"""
from pathlib import Path
import runpy

runpy.run_path(str(Path(__file__).resolve().parent /
                  'source-reproduction/reproducibility/fetch_original.py'),
               run_name='__main__')
