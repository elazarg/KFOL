#!/usr/bin/env python3
"""Rebuild/audit the immutable external obstruction, outside KFOL's imports.

Supply an isolated checkout/archive at the revision in open-game-v1.json,
with its pinned Lake dependencies available. No worktree or sibling mutation
is required. Sources and package pins are checked before invoking Lean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    if checkout == (ROOT.parent / "GameTheory").resolve():
        raise SystemExit("Use an isolated checkout; the sibling GameTheory checkout is read-only.")
    manifest = json.loads((ROOT / "notes/integration/open-game-v1.json").read_text())
    for name, expected in manifest["source_hashes"].items():
        source = checkout / name
        if not source.is_file() or hashlib.sha256(source.read_bytes()).hexdigest() != expected:
            raise SystemExit(f"External pinned source mismatch: {name}")
    packages = json.loads((checkout / "lake-manifest.json").read_text())["packages"]
    for package in packages:
        if package["type"] != "git":
            continue
        repository = checkout / ".lake/packages" / package["name"]
        actual = subprocess.check_output(["git", "-C", str(repository), "rev-parse", "HEAD"], text=True).strip()
        if actual != package["rev"]:
            raise SystemExit(f"External dependency revision mismatch: {package['name']}")
    subprocess.run(["lake", "build", manifest["module"]], cwd=checkout, check=True)
    allowed = "#[``propext, ``Classical.choice, ``Quot.sound]"
    names = ",\n      ".join("`" + name for name in manifest["theorems"])
    source = f'''import {manifest["module"]}
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean in
run_cmd do
  for name in #[{names}] do
    for axiomName in (← collectAxioms name) do
      unless {allowed}.contains axiomName do
        throwError "External obstruction audit: forbidden axiom {{axiomName}} in {{name}}"
'''
    with tempfile.TemporaryDirectory(prefix="kfol-open-game-audit-") as tmp:
        audit = Path(tmp) / "Audit.lean"
        audit.write_text(source)
        subprocess.run(["lake", "env", "lean", str(audit)], cwd=checkout, check=True)
    print(f"External obstruction: pinned sources, {len(manifest['theorems'])} theorem closures checked.")


if __name__ == "__main__":
    main()
