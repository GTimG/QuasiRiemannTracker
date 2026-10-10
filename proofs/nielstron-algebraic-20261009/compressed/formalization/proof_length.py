#!/usr/bin/env python3
"""Print this QRH package's exact LeanLeanBench source-token count."""
from pathlib import Path
import sys

project = Path(__file__).resolve().parent
workspace = project.parents[1]
sys.path.insert(0, str(workspace / "tools"))
from count_lean_tokens import metric_module

if len(sys.argv) != 1:
    raise SystemExit("proof_length.py takes no arguments")
print(metric_module(workspace / "lean-lean").measure_repository_lean_tokens(project))
