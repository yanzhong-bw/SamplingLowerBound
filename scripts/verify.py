#!/usr/bin/env python3
"""Build the project and inspect the kernel dependencies of audited results."""

import argparse
from pathlib import Path
import re
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Lake executable")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    source_check = subprocess.run([sys.executable, "scripts/check-trust.py"], cwd=root)
    if source_check.returncode:
        return source_check.returncode
    build = subprocess.run([args.lake, "build"], cwd=root, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(build.stdout, end="", flush=True)
    if build.returncode:
        return build.returncode
    audit = subprocess.run([args.lake, "env", "lean", "Audit.lean"], cwd=root,
                           text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT)
    print(audit.stdout, end="", flush=True)
    if audit.returncode:
        return audit.returncode
    expected = len(re.findall(r"^#print axioms ",
                             (root / "Audit.lean").read_text(), re.MULTILINE))
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", audit.stdout,
                        re.DOTALL)
    independent = audit.stdout.count("does not depend on any axioms")
    if len(groups) + independent != expected or not expected:
        print("ERROR: incomplete axiom-audit output", file=sys.stderr)
        return 1
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    observed = {entry.strip() for group in groups for entry in group.split(",")
                if entry.strip()}
    unexpected = observed - allowed
    if unexpected:
        print("ERROR: unexpected axioms: " + ", ".join(sorted(unexpected)),
              file=sys.stderr)
        return 1
    complete_audit = subprocess.run(
        [args.lake, "env", "lean", "TrustAudit.lean"], cwd=root,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(complete_audit.stdout, end="")
    if complete_audit.returncode:
        return complete_audit.returncode
    print(f"PASS: {expected} audited declarations; only standard Lean axioms.")
    print("Scope and external inputs: see FORMALIZATION_SCOPE.md and ExternalInputs.lean.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
