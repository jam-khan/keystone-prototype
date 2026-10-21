"""Fail CI if a principal theorem acquires an unexpected proof axiom."""

import re
import subprocess

from experiments.gather import ROOT


def main() -> None:
    result = subprocess.run(["lake", "env", "lean", "Keystone/Audit.lean"],
                            cwd=ROOT, capture_output=True, text=True, check=True, timeout=30)
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", result.stdout)
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / "Keystone/Audit.lean").read_text(), re.M)
    if [name for name, _ in reports] != expected or not reports:
        raise AssertionError(f"incomplete axiom audit: {result.stdout}")
    allowed = {"propext", "Quot.sound", "Classical.choice"}
    for name, axioms in reports:
        unexpected = {axiom.strip() for axiom in axioms.split(",") if axiom.strip()} - allowed
        if unexpected:
            raise AssertionError(f"{name} trusts unexpected axioms: {unexpected}")
    print(f"Axiom audit: {len(reports)} principal theorems use only standard Lean axioms.")


if __name__ == "__main__":
    main()
