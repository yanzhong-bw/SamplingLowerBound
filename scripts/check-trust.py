#!/usr/bin/env python3
"""Reject proof holes and locally introduced axioms before invoking Lean."""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
sources = [root / "SamplingLowerBounds.lean", *sorted((root / "SamplingLowerBounds").glob("*.lean"))]
for source in sources:
    text = source.read_text()
    # This intentionally also rejects these tokens in comments, keeping the
    # source policy simple; the kernel dependency audit is the definitive gate.
    hole = re.search(r"\b(sorry|sorryAx|admit|unsafe|native_decide)\b", text)
    extension = re.search(r"^\s*(?:(?:private|protected|noncomputable)\s+)*(axiom|axioms|constant|constants)\s", text, re.M)
    if hole or extension:
        print(f"Forbidden trust extension in {source.relative_to(root)}", file=sys.stderr)
        sys.exit(1)
print(f"PASS: checked {len(sources)} Lean source files for proof holes and trust extensions.")
