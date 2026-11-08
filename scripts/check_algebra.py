#!/usr/bin/env python3
"""Check audit coverage, then build the pure algebra and its kernel audits."""

from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parent.parent


def main():
    audit = ROOT / "KFOL/Audit.lean"
    imports = set(re.findall(r"^import all ([\w.]+)$", audit.read_text(), re.M))
    sources = [ROOT / "KFOL.lean", ROOT / "Paper.lean", *sorted((ROOT / "KFOL").rglob("*.lean"))]
    expected = {".".join(path.relative_to(ROOT).with_suffix("").parts)
                for path in sources if path != audit}
    if imports != expected:
        raise SystemExit(f"Audit coverage mismatch: missing={expected - imports}, extra={imports - expected}")
    # The independent algebra build must succeed without importing the paper.
    subprocess.run(["lake", "build", "KFOL.Algebra"], cwd=ROOT, check=True)
    subprocess.run(["lake", "build", "Paper", "KFOL.Audit"], cwd=ROOT, check=True)
    subprocess.run(["lake", "env", "lean", "-DwarningAsError=true",
                    "tests/SyntaxComparison.lean"], cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
