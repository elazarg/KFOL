#!/usr/bin/env python3
"""Export/check JSON and Markdown indexes of Paper/Report theorem-type definitions.

The Lean stage visits theorem TYPES and recursively visits project-owned
non-proof definitions and inductive constructors. It does not inspect theorem
proof bodies and does not unfold external declarations. Python adds source
fingerprints and deterministic per-theorem slices. This is a definition review
index, separate from the whole-project proof/axiom audit.

Usage:
  python3 scripts/export_definition_surface.py
  python3 scripts/export_definition_surface.py --check --no-build
  python3 scripts/export_definition_surface.py --markdown --no-build
  python3 scripts/export_definition_surface.py --check --entrypoint Report
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
ENTRYPOINTS = ("Paper", "Report")
DEFAULT_ENTRYPOINT = "Paper"
DEFAULT_OUTPUT = ROOT / "notes/paper-definition-surface.json"
EXTRACTOR = ROOT / "scripts/DefinitionSurface.lean"

POLICY = {
    "roots": "Every top-level theorem declared in namespace KFOL.Paper in Paper.lean; traverse its type, never its proof body.",
    "project_expansion": "Recursively traverse declaration types, non-proof definition/opaque bodies, and reachable inductive constructor types in modules KFOL.* or Paper.",
    "proof_erasure": "Lean.Meta.isProof erases proof-valued subterms with local binders in scope, including proof-only helper definitions. Proposition expressions themselves remain: predicates and hypotheses contribute their mathematical definitions.",
    "inductives": "Reachable inductive declarations include their constructors and mutual inductive declarations. Kernel-generated recursors are indexed by their types; their computation rules are supplied by Lean's inductive kernel.",
    "external_boundary": "Record directly referenced external constants and their declared types without unfolding their definitions or traversing the external dependency closure.",
    "purpose": "A reproducible index for reviewing the mathematical meaning of public statements. It does not establish that a definition matches the manuscript, replace human review, or replace the independent source/import/axiom audits.",
}


def default_output(entrypoint: str) -> Path:
    return DEFAULT_OUTPUT if entrypoint == DEFAULT_ENTRYPOINT else ROOT / "notes/report-definition-surface.json"


def entrypoint_policy(entrypoint: str) -> dict[str, str]:
    policy = dict(POLICY)
    policy["roots"] = (f"Every top-level theorem declared in namespace KFOL.{entrypoint} "
                       f"in {entrypoint}.lean; traverse its type, never its proof body.")
    modules = "KFOL.* or Paper" if entrypoint == "Paper" else "KFOL.*, Paper or Report"
    policy["project_expansion"] = ("Recursively traverse declaration types, non-proof definition/opaque bodies, "
                                   f"and reachable inductive constructor types in modules {modules}.")
    return policy


def reproduction(entrypoint: str) -> str:
    command = "python3 scripts/export_definition_surface.py --check"
    return command if entrypoint == DEFAULT_ENTRYPOINT else f"{command} --entrypoint {entrypoint}"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def source_record(path: Path) -> dict:
    if not path.is_file():
        raise RuntimeError(f"Missing reviewed source: {path}")
    return {"path": str(path.relative_to(ROOT)), "sha256": digest(path)}


def external_family(module: str) -> str:
    if module.startswith("GameTheory."):
        return "GameTheory"
    if module.startswith("Complexity."):
        return "ComplexityLib/Cslib interface"
    if module.startswith("Cslib."):
        return "Cslib"
    if module.startswith("Mathlib."):
        return "mathlib"
    if module.startswith(("Init.", "Lean.", "Std.")):
        return "Lean/Std"
    return module.split(".")[0] or "kernel"


def enrich(raw: dict, entrypoint: str = DEFAULT_ENTRYPOINT) -> dict:
    if entrypoint not in ENTRYPOINTS:
        raise ValueError(f"Unknown entrypoint: {entrypoint}")
    if raw.get("entrypoint", entrypoint) != entrypoint:
        raise RuntimeError(f"Raw graph entrypoint mismatch: expected {entrypoint}, got {raw['entrypoint']}")
    namespace = f"KFOL.{entrypoint}."
    roots = sorted(raw["roots"])
    expected = sorted(namespace + name for name in
                      re.findall(r"^theorem (\w+)\b", (ROOT / f"{entrypoint}.lean").read_text(), re.M))
    if roots != expected:
        raise RuntimeError(f"Public theorem coverage mismatch: missing={set(expected)-set(roots)}, extra={set(roots)-set(expected)}")
    nodes = {node["name"]: node for node in raw["project_declarations"]}
    if len(nodes) != len(raw["project_declarations"]):
        raise RuntimeError("Duplicate project declaration in semantic graph")
    externals = {node["name"]: node for node in raw["external_interfaces"]}
    for root in roots:
        node = nodes.get(root)
        if node is None or node["module"] != entrypoint or node["kind"] != "theorem":
            raise RuntimeError(f"Invalid {entrypoint} theorem root: {root}")
    sources = sorted({node["module"] for node in nodes.values()})
    allowed_modules = {"KFOL", "Paper"} | ({"Report"} if entrypoint == "Report" else set())
    if any(module not in allowed_modules and not module.startswith("KFOL.") for module in sources):
        raise RuntimeError(f"Unexpected project source module in {entrypoint} surface: {sources}")
    source_records = {module: source_record(source_path(module)) for module in sources}
    declaration_indexes = {}
    for module in sources:
        index_path = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".ilean")
        if not index_path.is_file():
            raise RuntimeError(f"Missing declaration location index: {index_path}; build {entrypoint} first")
        declaration_indexes[module] = json.loads(index_path.read_text())["decls"]
    for name, node in nodes.items():
        if node["theorem_proof_traversed"]:
            raise RuntimeError(f"Theorem proof was traversed: {name}")
        if node["kind"] == "theorem" and node["definition_body_traversed"]:
            raise RuntimeError(f"Theorem proof body entered definition graph: {name}")
        for dependency in node["project_dependencies"]:
            if dependency not in nodes:
                raise RuntimeError(f"Incomplete project closure: {name} -> {dependency}")
        for dependency in node["external_dependencies"]:
            if dependency not in externals:
                raise RuntimeError(f"Missing external boundary declaration: {dependency}")
        node["source"] = source_records[node["module"]]["path"]
        # Constructors, fields, match auxiliaries and recursors share the
        # nearest enclosing written declaration's source location. The exact
        # graph still keeps their separate kernel declarations and dependencies.
        index = declaration_indexes[node["module"]]
        anchor = name
        while anchor and anchor not in index:
            anchor = anchor.rpartition(".")[0]
        if anchor:
            start_line, start_column, end_line, end_column, *_ = index[anchor]
            node["source_anchor"] = {
                "declaration": anchor, "line": start_line, "column": start_column,
                "end_line": end_line, "end_column": end_column,
                "exact_declaration": anchor == name,
            }
        else:
            node["source_anchor"] = None
    slices = []
    all_reached: set[str] = set()
    for root in roots:
        reached: set[str] = set()
        boundary: set[str] = set()
        pending = [root]
        while pending:
            name = pending.pop()
            if name in reached:
                continue
            reached.add(name)
            pending.extend(nodes[name]["project_dependencies"])
            boundary.update(nodes[name]["external_dependencies"])
        all_reached.update(reached)
        semantic = sorted(name for name in reached if nodes[name]["kind"] != "theorem")
        slices.append({
            "theorem": root,
            "type": nodes[root]["type"],
            "location": nodes[root]["location"],
            "direct_type_dependencies": nodes[root]["type_dependencies"],
            "semantic_project_declarations": semantic,
            "project_modules": sorted({nodes[name]["module"] for name in semantic}),
            "external_interfaces": sorted(boundary),
        })
    if all_reached != set(nodes):
        raise RuntimeError("Report contains declarations unreachable from public theorem types")
    modules = []
    for module in sources:
        members = [node for node in nodes.values() if node["module"] == module]
        modules.append({
            "module": module,
            **source_records[module],
            "central_definition_file": module.startswith("KFOL.Definitions."),
            "kind_counts": dict(sorted(Counter(node["kind"] for node in members).items())),
            "declarations": sorted(node["name"] for node in members),
        })
    boundary_groups: dict[str, list[str]] = defaultdict(list)
    for name, node in externals.items():
        node["family"] = external_family(node["module"])
        boundary_groups[node["family"]].append(name)
    review_units = defaultdict(list)
    for name, node in nodes.items():
        if node["kind"] != "theorem":
            anchor = node["source_anchor"]
            review_units[(node["source"], anchor["declaration"] if anchor else name)].append(name)
    summary = {
        "public_theorem_types": len(roots),
        "project_declarations": len(nodes),
        "semantic_project_declarations": sum(node["kind"] != "theorem" for node in nodes.values()),
        "kind_counts": dict(sorted(Counter(node["kind"] for node in nodes.values()).items())),
        "project_source_files": len(sources),
        "central_definition_files": sum(module.startswith("KFOL.Definitions.") for module in sources),
        "external_boundary_constants": len(externals),
        "external_boundary_by_family": {family: len(names) for family, names in sorted(boundary_groups.items())},
        "proof_valued_subterms_erased": sum(node["proof_subterms_erased"] for node in nodes.values()),
        "theorem_proof_bodies_traversed": 0,
        "source_review_groups": len(review_units),
        "written_semantic_review_units": sum(nodes[members[0]]["source_anchor"] is not None
                                              for members in review_units.values()),
        "semantic_declarations_without_source_anchor": sum(
            node["kind"] != "theorem" and node["source_anchor"] is None for node in nodes.values()),
    }
    return {
        "schema_version": 1,
        "entrypoint": entrypoint,
        "title": f"{entrypoint} theorem-type definition surface",
        "traversal_policy": entrypoint_policy(entrypoint),
        "reproduction": reproduction(entrypoint),
        "generator_sources": [source_record(EXTRACTOR), source_record(Path(__file__))],
        "build_inputs": [source_record(ROOT / name) for name in ("lean-toolchain", "lake-manifest.json")],
        "summary": summary,
        "review_order": [
            f"Read each public theorem's literal type in {entrypoint}.lean and its per-theorem slice below.",
            "Review central KFOL/Definitions files, then the extra semantic definitions reached in algorithm/round/machine files. Source fingerprints and exact declaration edges identify that complete project surface.",
            "Review the imported GameTheory and ComplexityLib/Cslib boundary types separately. External boundary entries are interfaces, not a claim that their full definition closure was audited here.",
            "Use the existing whole-project axiom/import audit for proof dependencies; they are deliberately absent from this report.",
        ],
        "module_index": modules,
        "source_review_units": [
            {"source": source, "declaration_group": anchor,
             "written_declaration": anchor if nodes[members[0]]["source_anchor"] else None,
             "location": nodes[members[0]]["source_anchor"],
             "kernel_declarations": sorted(members)}
            for (source, anchor), members in sorted(review_units.items())
        ],
        "theorem_surfaces": slices,
        "project_declarations": [nodes[name] for name in sorted(nodes)],
        "external_interfaces": [externals[name] for name in sorted(externals)],
    }


def markdown(report: dict) -> str:
    summary = report["summary"]
    entrypoint = report.get("entrypoint", DEFAULT_ENTRYPOINT)
    rows = [
        f"# {entrypoint} theorem-type definition surface", "",
        f"{summary['public_theorem_types']} public theorem types reach "
        f"{summary['semantic_project_declarations']} project semantic declarations in "
        f"{summary['project_source_files']} source files. "
        f"{summary['central_definition_files']} of those files are under `KFOL/Definitions`. "
        f"Generated declarations are grouped into {summary['written_semantic_review_units']} written source review units; "
        f"{summary['semantic_declarations_without_source_anchor']} derived declarations have file-level locations. "
        "Theorem proof bodies are excluded.", "",
        "This is a review index. Definitions still require human review against the manuscript; "
        "the separate proof/axiom and import audits remain necessary.", "",
        "| Source | Reachable declarations | Central definitions |", "| --- | ---: | --- |",
    ]
    for module in sorted(report["module_index"], key=lambda node: (-len(node["declarations"]), node["module"])):
        rows.append(f"| [{module['path']}](../{module['path']}) | {len(module['declarations'])} | "
                    f"{'yes' if module['central_definition_file'] else ''} |")
    rows += ["", "External interfaces are recorded without unfolding them:", ""]
    rows.extend(f"- {family}: {count} boundary constants." for family, count in
                summary["external_boundary_by_family"].items())
    rows += ["", "Review per public theorem:", "",
             "| Public theorem | Semantic declarations | Project modules |",
             "| --- | ---: | ---: |"]
    for surface in report["theorem_surfaces"]:
        line = surface["location"]["line"] if surface["location"] else 1
        label = surface["theorem"].removeprefix(f"KFOL.{entrypoint}.")
        rows.append(f"| [{label}](../{entrypoint}.lean#L{line}) | "
                    f"{len(surface['semantic_project_declarations'])} | {len(surface['project_modules'])} |")
    rows += ["", "The JSON contains every theorem's complete project slice, exact declaration/type/body edges, "
             "external interface types, declaration locations and source fingerprints.", "",
             f"Reproduce with `{reproduction(entrypoint)}`.", ""]
    return "\n".join(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the committed JSON is stale")
    parser.add_argument("--entrypoint", choices=ENTRYPOINTS, default=DEFAULT_ENTRYPOINT,
                        help="public theorem module to audit (default: Paper)")
    parser.add_argument("--no-build", action="store_true", help="use already current Paper and Report builds")
    parser.add_argument("--markdown", action="store_true", help="print a Markdown review index")
    parser.add_argument("--output", type=Path,
                        help="JSON output path (default: notes/<entrypoint>-definition-surface.json)")
    parser.add_argument("--raw", type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.output is None:
        args.output = default_output(args.entrypoint)
    if args.raw:
        raw = json.loads(args.raw.read_text())
    else:
        if not args.no_build:
            subprocess.run(["lake", "build", "Paper", "Report"], cwd=ROOT, check=True)
        with tempfile.TemporaryDirectory(prefix="kfol-definition-surface-") as temporary:
            raw_path = Path(temporary) / "surface.json"
            environment = dict(os.environ, KFOL_DEFINITION_SURFACE_RAW=str(raw_path),
                               KFOL_DEFINITION_SURFACE_ENTRYPOINT=args.entrypoint)
            subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", str(EXTRACTOR.relative_to(ROOT))],
                           cwd=ROOT, env=environment, check=True)
            raw = json.loads(raw_path.read_text())
    report = enrich(raw, args.entrypoint)
    output = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    markdown_output = markdown(report)
    markdown_path = args.output.with_suffix(".md")
    if args.check:
        if (not args.output.is_file() or args.output.read_text() != output or
                not markdown_path.is_file() or markdown_path.read_text() != markdown_output):
            raise SystemExit(f"{args.entrypoint} definition surface JSON/Markdown is stale; run "
                             f"python3 scripts/export_definition_surface.py --entrypoint {args.entrypoint}")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output)
        markdown_path.write_text(markdown_output)
    if args.markdown:
        print(markdown_output, end="")
    else:
        summary = report["summary"]
        label = "Definition surface" if args.entrypoint == DEFAULT_ENTRYPOINT else f"{args.entrypoint} definition surface"
        print(f"{label}: {summary['public_theorem_types']} public types, "
              f"{summary['semantic_project_declarations']} semantic project declarations, "
              f"{summary['project_source_files']} source files, "
              f"{summary['external_boundary_constants']} external interfaces; no theorem proofs traversed.")


if __name__ == "__main__":
    main()
