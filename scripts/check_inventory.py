#!/usr/bin/env python3
"""Validate current claim evidence; archived milestones refer to their own commit."""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent.parent
INVENTORY = ROOT / "notes/formalization-claims.json"


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def check_artifacts(value):
    """Check every current fingerprint and written declaration location."""
    checked = 0
    if isinstance(value, dict):
        source = value.get("path", value.get("source"))
        if isinstance(source, str) and "sha256" in value:
            path = ROOT / source
            require(path.is_file(), f"Missing evidence source: {source}")
            text = path.read_text()
            require(digest(text) == value["sha256"], f"Stale evidence fingerprint: {source}")
            lines = text.splitlines()
            for declaration in value.get("declarations", []):
                line = declaration["line"]
                name = declaration["name_as_written"]
                require(0 < line <= len(lines) and name in lines[line - 1],
                        f"Stale declaration location: {source}:{line}: {name}")
            checked += 1
        checked += sum(check_artifacts(item) for item in value.values())
    elif isinstance(value, list):
        checked += sum(check_artifacts(item) for item in value)
    return checked


def main():
    inventory = json.loads(INVENTORY.read_text())
    claims = inventory["claims"]
    prose = inventory["main_prose_obligations"]
    require(len({row["id"] for row in claims + prose}) == len(claims) + len(prose),
            "Duplicate claim or prose obligation identifier")
    for claim in claims:
        text = (ROOT / claim["source"]).read_text()
        statement = claim["statement_latex"]
        require(digest(statement) == claim["statement_sha256"],
                f"Corrupt statement snapshot: {claim['id']}")
        require(statement in text, f"Changed or missing statement: {claim['id']}")
        require(text[:text.index(statement)].count("\n") + 1 == claim["line"],
                f"Stale statement line: {claim['id']}")
    summary = inventory["summary"]
    require(dict(Counter(row["status"] for row in claims)) == summary["evidence_status_counts"],
            "Evidence status summary does not match claims")
    require(dict(Counter(row["scope"] for row in claims)) == summary["scope_counts"],
            "Scope summary does not match claims")
    require(len(prose) == summary["main_prose_obligations"], "Prose total mismatch")
    require(sum(row["required"] for row in prose) == summary["required_main_prose_obligations"],
            "Required prose total mismatch")
    paper = (ROOT / "Paper.lean").read_text()
    declarations = set(re.findall(r"^theorem (\w+)\b", paper, re.M))
    referenced = set()
    for row in claims + prose:
        public = row.get("public_declarations", [])
        require(len(public) == len(set(public)), f"Duplicate public declaration: {row['id']}")
        for name in public:
            if name.startswith("KFOL.Paper."):
                referenced.add(name.removeprefix("KFOL.Paper."))
                require(name.removeprefix("KFOL.Paper.") in declarations,
                        f"Missing public theorem: {row['id']}: {name}")
    require(declarations <= referenced, f"Unmapped public statements: {declarations - referenced}")
    for declaration in declarations:
        require(f"#print axioms KFOL.Paper.{declaration}" in paper,
                f"Missing public axiom guard: {declaration}")
    artifacts = check_artifacts(inventory)
    print(f"Inventory: {len(claims)} statement snapshots, {len(prose)} prose obligations, "
          f"{artifacts} evidence fingerprints, {len(declarations)} public statements checked.")


if __name__ == "__main__":
    main()
