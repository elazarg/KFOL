#!/usr/bin/env python3
"""Copy each document's labels into the snapshot the other document reads.

main.tex and tr.tex refer to each other's results. Each reads the other's numbers
from a committed file, so it builds alone, on Overleaf for instance. Pages and titles
are dropped, because nothing prints them and they would change with every edit. A link
to the other document goes to its entry in the bibliography.
"""
from pathlib import Path

DOCUMENTS = {"main": "GershuniOwnedChoice2026", "tr": "GershuniOwnedChoiceTR2026"}
PREFIX = r"\newlabel{"


def groups(text):
    """The top-level brace groups of text."""
    found, depth, start = [], 0, 0
    for index, char in enumerate(text):
        if char == "{":
            start = index + 1 if depth == 0 else start
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                found.append(text[start:index])
    return found


def snapshot(name, bibkey):
    lines = []
    for line in Path(f"build/{name}.aux").read_text().splitlines():
        if not line.startswith(PREFIX):
            continue
        label, payload = groups(line)
        parts = groups(payload)
        if label.endswith("@cref"):
            lines.append(rf"\newlabel{{{label}}}{{{{{parts[0]}}}{{[1][0][]0}}{{}}{{}}{{}}}}")
        elif len(parts) == 5:
            lines.append(rf"\newlabel{{{label}}}{{{{{parts[0]}}}{{0}}{{}}{{cite.{bibkey}}}{{}}}}")
    header = f"% Generated from {name}.tex by scripts/export_labels.py. Do not edit."
    return "\n".join([header, *sorted(lines)]) + "\n"


for name, bibkey in DOCUMENTS.items():
    path = Path(f"sections/labels-{name}.tex")
    text = snapshot(name, bibkey)
    if not path.exists() or path.read_text() != text:
        path.write_text(text)
        print(f"updated {path}")
