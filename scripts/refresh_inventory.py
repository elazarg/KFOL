#!/usr/bin/env python3
"""Refresh locations/fingerprints of unchanged statements and current evidence.

This never promotes a claim's status or changes its mathematical statement.
Changes to a statement or removal of an evidence source require manual review.
Historical milestone evidence is deliberately left at its archived commit.
"""

from collections import Counter
import json
from pathlib import Path
import re

from check_inventory import INVENTORY, ROOT, digest, require


def declaration_matches(text, pattern, namespace):
    matches = list(re.finditer(pattern, text, re.M))
    if not namespace:
        return matches
    scopes = []
    locations = {}
    offset = 0
    for line in text.splitlines(keepends=True):
        stripped = line.strip()
        opened = re.fullmatch(r"namespace ([\w.]+)", stripped)
        section = re.fullmatch(r"(?:noncomputable )?section(?: (\w+))?", stripped)
        ended = re.fullmatch(r"end(?: ([\w.]+))?", stripped)
        if opened:
            scopes.append(("namespace", opened[1]))
        elif section or stripped.endswith("public section"):
            scopes.append(("section", section[1] if section else None))
        elif ended:
            if ended[1]:
                for index in range(len(scopes) - 1, -1, -1):
                    if scopes[index][1] == ended[1]:
                        scopes = scopes[:index]
                        break
            elif scopes:
                scopes.pop()
        locations[offset] = ".".join(name for kind, name in scopes if kind == "namespace")
        offset += len(line)
    return [match for match in matches if locations.get(match.start()) == namespace]


def refresh(value):
    if isinstance(value, dict):
        source = value.get("path", value.get("source"))
        if isinstance(source, str) and "sha256" in value:
            path = ROOT / source
            require(path.is_file(), f"Evidence source needs review: {source}")
            text = path.read_text()
            old_lines = text.splitlines()
            for declaration in value.get("declarations", []):
                name = declaration["name_as_written"]
                # Resolve a written declaration, not arbitrary mentions or uses.
                pattern = (r"^(?:@\[[^\n]*\][ \t]*)?(?:private )?(?:noncomputable )?"
                           r"(?:theorem|def|abbrev|inductive|structure) "
                           + re.escape(name) + r"(?=[\s{(:])")
                matches = declaration_matches(text, pattern, declaration.get("namespace"))
                require(bool(matches), f"Missing evidence declaration: {source}: {name}")
                if len(matches) > 1:
                    line = declaration["line"]
                    require(0 < line <= len(old_lines) and re.match(pattern, old_lines[line - 1]),
                            f"Ambiguous declaration needs review: {source}: {name}")
                else:
                    declaration["line"] = text[:matches[0].start()].count("\n") + 1
            value["sha256"] = digest(text)
        for child in value.values():
            refresh(child)
    elif isinstance(value, list):
        for child in value:
            refresh(child)


def main():
    inventory = json.loads(INVENTORY.read_text())
    for claim in inventory["claims"]:
        text = (ROOT / claim["source"]).read_text()
        statement = claim["statement_latex"]
        require(statement in text, f"Statement changed; review required: {claim['id']}")
        require(digest(statement) == claim["statement_sha256"], f"Corrupt snapshot: {claim['id']}")
        claim["line"] = text[:text.index(statement)].count("\n") + 1
    refresh(inventory)
    inventory["summary"]["evidence_status_counts"] = dict(sorted(Counter(
        row["status"] for row in inventory["claims"]).items()))
    INVENTORY.write_text(json.dumps(inventory, indent=2) + "\n")
    print("Refreshed unchanged statement locations and current evidence fingerprints; statuses retained.")


if __name__ == "__main__":
    main()
