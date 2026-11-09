#!/usr/bin/env python3
"""Check source coverage, pure imports and the complete authored axiom closure."""

from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent


def main():
    audit = ROOT / "KFOL/Audit.lean"
    imports = set(re.findall(r"^import all ([\w.]+)$", audit.read_text(), re.M))
    sources = [ROOT / "KFOL.lean", ROOT / "Paper.lean", *sorted((ROOT / "KFOL").rglob("*.lean"))]
    expected = {".".join(path.relative_to(ROOT).with_suffix("").parts)
                for path in sources if path != audit}
    if imports != expected:
        raise SystemExit(f"Audit coverage mismatch: missing={expected - imports}, extra={imports - expected}")
    subprocess.run([sys.executable, "scripts/check_inventory.py"], cwd=ROOT, check=True)
    # The independent algebra build must succeed without importing the paper.
    subprocess.run(["lake", "build", "KFOL.Algebra", "KFOL.Audit.Algebra"], cwd=ROOT, check=True)
    subprocess.run(["lake", "build", "Paper", "KFOL.Audit"], cwd=ROOT, check=True)
    # Exercise the actual boundary check in a deliberately contaminated environment.
    with tempfile.TemporaryDirectory(prefix="kfol-import-audit-") as tmp:
        negative = Path(tmp) / "NegativeAudit.lean"
        source = (ROOT / "KFOL/Audit/Algebra.lean").read_text()
        source = source.replace("module\n", "module\nimport KFOL.Complexity.Language\n", 1)
        negative.write_text(source)
        result = subprocess.run(["lake", "env", "lean", str(negative)], cwd=ROOT,
                                capture_output=True, text=True)
        diagnostic = result.stdout + result.stderr
        if result.returncode == 0 or "Algebra audit: forbidden transitive import" not in diagnostic:
            raise SystemExit(f"Negative import-boundary check failed:\n{diagnostic}")
    for test in sorted((ROOT / "tests").glob("*.lean")):
        subprocess.run(["lake", "env", "lean", "-DwarningAsError=true",
                        str(test.relative_to(ROOT))], cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
