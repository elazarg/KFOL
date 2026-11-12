#!/usr/bin/env python3
"""Check literal public façades and immutable relocation of the old signatures.

This lexical check complements Lean's namespace axiom audits. It never treats
an inferred declaration type or a shortened public alias as a complete claim.
The relocation baseline is Paper.lean at commit 51e9725. Its canonical
name/signature-hash corpus and source hash are pinned in this checker, so a
manifest edited together with weakened library statements still fails. Source
archives and shallow checkouts do not need the old Git object: when available,
that object supplies an additional exact-text historical cross-check.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
ENTRYPOINTS = ("Paper", "Report")
BASELINE_COMMIT = "51e9725"
BASELINE_SOURCE_SHA256 = "d5be4a316a8a8006172feffe3dac2e7ae869069b169e1cacc5f1ab54214066cd"
BASELINE_CORPUS_SHA256 = "ba50e3b37077081fe316775e21694555024c92a5bbfbc865b130bac90451a69f"
MANIFEST = ROOT / "notes/audit-relocations.json"
LIBRARY = ROOT / "KFOL/Results/Certificates.lean"
NAME = r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*"
THEOREM = re.compile(r"^[ \t]*(?:(?:public|private|protected)\s+)?theorem\s+(" + NAME + r")\b", re.M)
SEPARATOR = re.compile(r" :=(?: by)?\n")
COMMAND = re.compile(r"^[ \t]*(?:namespace\b|section\b|end\b|open\b|universe\b|variable\b|noncomputable\s+section\b|theorem\b|(?:public|private|protected)\s+theorem\b|#|@\[)", re.M)
FORBIDDEN_DECLARATION = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|unsafe|partial|local|scoped)\s+)*"
    r"(def|abbrev|axiom|constant|constants|opaque|instance|inductive|coinductive|structure|class|lemma|example|"
    r"mutual|macro|macro_rules|syntax|elab|elab_rules|initialize|builtin_initialize|declare_syntax_cat|"
    r"notation|infix|infixl|infixr|prefix|postfix|export|attribute)\b", re.M)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def read_source(path: Path) -> str:
    return path.read_bytes().decode("utf-8")


def mask_noncode(text: str, *, strings: bool = True) -> str:
    """Mask nested Lean comments/strings without changing offsets or newlines."""
    chars = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            require(depth == 0, "Unclosed Lean comment")
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            if not strings:
                continue
        else:
            i += 1
            continue
        for j in range(start, min(i, len(text))):
            if chars[j] != "\n":
                chars[j] = " "
    return "".join(chars)


@dataclass(frozen=True)
class Theorem:
    name: str
    full_name: str
    signature: str
    proof: str
    line: int


def theorem_declarations(text: str) -> dict[str, Theorem]:
    """Preserve the COMPLETE header after its name, before the proof separator.

    The separator intentionally requires end-of-line, so same-line let/letI
    bindings inside the proposition do not truncate its return type.
    """
    code = mask_noncode(text)
    scopes: list[tuple[str, str]] = []
    namespace_at: dict[int, str] = {}
    events = re.compile(r"^[ \t]*(namespace\s+(" + NAME + r")|section(?:\s+(" + NAME +
                        r"))?|end(?:\s+(" + NAME + r"))?)\s*$", re.M)
    matches = list(THEOREM.finditer(code))
    positions = iter(events.finditer(code))
    event = next(positions, None)
    for match in matches:
        while event and event.start() < match.start():
            if event.group(2):
                scopes.append(("namespace", event.group(2)))
            elif event.group(1).lstrip().startswith("section"):
                scopes.append(("section", event.group(3) or ""))
            elif scopes:
                if event.group(4):
                    require(scopes[-1][1].split(".")[-1] == event.group(4).split(".")[-1],
                            f"Mismatched namespace/section end: {event.group(0).strip()}")
                scopes.pop()
            event = next(positions, None)
        namespace_at[match.start()] = ".".join(name for kind, name in scopes if kind == "namespace")
    result = {}
    for index, match in enumerate(matches):
        next_start = matches[index+1].start() if index+1 < len(matches) else len(text)
        separator = SEPARATOR.search(code, match.end(), next_start)
        require(separator is not None, f"Missing complete signature/proof separator: {match.group(1)}")
        following = COMMAND.search(code, separator.end())
        proof_end = following.start() if following else len(text)
        namespace = namespace_at[match.start()]
        name = match.group(1)
        full_name = f"{namespace}.{name}" if namespace else name
        require(full_name not in result, f"Duplicate theorem declaration: {full_name}")
        result[full_name] = Theorem(name, full_name, text[match.end():separator.start()],
                                    text[separator.end():proof_end], text[:match.start()].count("\n")+1)
    return result


def library_declarations() -> dict[str, Theorem]:
    result = {}
    sources = [*sorted((ROOT / "KFOL/Results").rglob("*.lean")),
               ROOT / "KFOL/Strategic/Quantified/Fold.lean",
               ROOT / "KFOL/Core/RelationalInterpolation.lean",
               ROOT / "KFOL/Core/FourValuation.lean",
               ROOT / "KFOL/Core/LocalNormalForm.lean",
               ROOT / "KFOL/Core/ProfileEnvelope.lean",
               ROOT / "KFOL/Core/TernaryInterpolation.lean",
               ROOT / "KFOL/Core/MinorantPatches.lean",
               ROOT / "KFOL/Core/MinorantFivePatches.lean",
               ROOT / "KFOL/Core/FivePointInterpolation.lean",
               ROOT / "KFOL/Core/CrownObstruction.lean",
               ROOT / "KFOL/Core/CrownPatches.lean",
               ROOT / "KFOL/Core/CyclicPersistence.lean",
               ROOT / "KFOL/Core/AtomicObserver.lean",
               ROOT / "KFOL/Core/AtomicAmalgamation.lean",
               ROOT / "KFOL/Core/Bichain.lean",
               ROOT / "KFOL/Core/BichainFiber.lean",
               ROOT / "KFOL/Core/Hypergraphs.lean",
               ROOT / "KFOL/Core/FiniteRelationObstruction.lean",
               ROOT / "KFOL/Core/CrownFullSyntax.lean",
               ROOT / "KFOL/Core/SourceCertificates.lean",
               ROOT / "KFOL/Core/Peeling.lean",
               ROOT / "KFOL/Core/SourcePeeling.lean",
               ROOT / "KFOL/Core/OwnerEliminationComplete.lean",
               ROOT / "KFOL/Core/ColoredGraphRealization.lean",
               ROOT / "KFOL/Core/ColoredGraphGuards.lean",
               *sorted((ROOT / "KFOL/Query").rglob("*.lean"))]
    for path in sources:
        for name, declaration in theorem_declarations(read_source(path)).items():
            require(name not in result, f"Duplicate library theorem: {name}")
            result[name] = declaration
    return result


def named_library_application(proof: str) -> str:
    """A named library theorem with optional simple explicit arguments.

    Arguments may be names, numerals, underscores, or parenthesized named
    arguments. Nested proof construction, lambdas and tactic blocks fail.
    """
    proof = mask_noncode(proof, strings=False).strip()
    head = re.match(r"@?(" + NAME + r")", proof)
    require(head is not None, "Public proof must name one library theorem")
    name = head.group(1)
    require("." in name, "Public proof must use a qualified library theorem name")
    if not name.startswith("KFOL."):
        name = "KFOL." + name
    rest = proof[head.end():].strip()
    universe = re.match(r"^\.\{[\w', \t\n]+\}", rest)
    if universe:
        rest = rest[universe.end():].strip()
    atom = rf"(?:{NAME}|\d+|_)"
    argument = re.compile(rf"(?:{atom}|\(\s*(?:{NAME}\s*:=\s*)?{atom}\s*\))")
    forbidden = re.compile(r"\b(by|fun|let|have|show|match|if|calc|do|where)\b")
    require(not forbidden.search(rest), f"Public proof constructs a proof instead of applying {name}")
    while rest:
        match = argument.match(rest)
        require(match is not None, f"Unsupported proof assembly after {name}: {rest}")
        rest = rest[match.end():]
        require(not rest or rest[0].isspace(), f"Public proof must be one library theorem application: {name}")
        rest = rest.strip()
    return name


def literal_return_type(signature: str) -> str:
    """Locate the written result type outside parameter binders."""
    code = mask_noncode(signature)
    closing = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    stack = []
    for i, character in enumerate(code):
        if character in closing:
            stack.append(closing[character])
        elif stack and character == stack[-1]:
            stack.pop()
        elif character == ":" and not stack:
            result = code[i+1:].strip()
            require(bool(result) and not re.fullmatch(r"(?:_|\?[\w']*)", result),
                    "Public theorem must write its complete return type")
            return result
    raise SystemExit("Public theorem lacks a literal complete return type")


def check_facade(entrypoint: str, libraries: dict[str, Theorem] | None = None) -> dict[str, Theorem]:
    path = ROOT / f"{entrypoint}.lean"
    text = read_source(path)
    code = mask_noncode(text)
    forbidden = FORBIDDEN_DECLARATION.search(code)
    require(forbidden is None, f"{entrypoint}.lean authors a forbidden declaration: {forbidden.group(1) if forbidden else ''}")
    allowed_variables = {
        "Paper": {"variable {Role : Type u} {Var : Type v}",
                  "variable [Fintype Role] [DecidableEq Role]"},
        "Report": set(),
    }
    for variable in re.findall(r"^[ \t]*variable[^\n]*", code, re.M):
        require(" ".join(variable.split()) in allowed_variables[entrypoint],
                f"Unreviewed section variable/assumption in {entrypoint}.lean: {variable.strip()}")
    require(not re.search(r"^[ \t]*(?:variables|parameter|parameters|include|omit)\b", code, re.M),
            f"Hidden section assumptions in {entrypoint}.lean")
    require(not re.search(r"^[ \t]*(?:private|protected|public)\s+theorem\b", code, re.M),
            f"Public entrypoint theorem modifiers must be declared by the file section: {entrypoint}.lean")
    declarations = theorem_declarations(text)
    require(bool(declarations), f"No public theorems in {entrypoint}.lean")
    require(len(re.findall(r"\btheorem\b", code)) == len(declarations),
            f"Unrecognized theorem declaration syntax in {entrypoint}.lean")
    require(all(name.startswith(f"KFOL.{entrypoint}.") and name.count(".") == 2 for name in declarations),
            f"Unexpected theorem namespace in {entrypoint}.lean")
    commands = re.findall(r"^[ \t]*#([^\n]*)", code, re.M)
    require(commands == [f"audit_namespace KFOL.{entrypoint}"],
            f"{entrypoint}.lean must have exactly one #audit_namespace KFOL.{entrypoint} command")
    require("public import KFOL.Audit.Namespace" in code, f"Missing namespace audit import in {entrypoint}.lean")
    libraries = library_declarations() if libraries is None else libraries
    for declaration in declarations.values():
        literal_return_type(declaration.signature)
        proof_name = named_library_application(declaration.proof)
        require(proof_name in libraries, f"Missing named library theorem: {declaration.full_name}: {proof_name}")
    return declarations


def baseline_source() -> str | None:
    """Use the historical object when available; never require Git history."""
    try:
        result = subprocess.run(["git", "show", f"{BASELINE_COMMIT}:Paper.lean"], cwd=ROOT,
                                capture_output=True)
    except FileNotFoundError:
        return None
    return result.stdout.decode("utf-8") if result.returncode == 0 else None


def signature_corpus(rows: list[dict]) -> str:
    """Canonical UTF-8 payload: sorted original name, TAB, signature SHA, LF."""
    return "".join(f"{row['original_name']}\t{row['signature_sha256']}\n"
                   for row in sorted(rows, key=lambda row: row["original_name"]))


def check_relocations() -> int:
    manifest = json.loads(MANIFEST.read_text())
    require(manifest.get("schema_version") == 1, "Unknown relocation manifest schema")
    require(manifest["original_source_path"] == "Paper.lean", "Changed relocation baseline path")
    require(manifest["library_source"] == "KFOL/Results/Certificates.lean", "Changed relocated source path")
    require(manifest["original_source_commit"] == BASELINE_COMMIT, "Changed relocation baseline commit")
    require(manifest["original_source_sha256"] == BASELINE_SOURCE_SHA256, "Changed relocation baseline source")
    rows = manifest["declarations"]
    require(manifest["signature_corpus_sha256"] == BASELINE_CORPUS_SHA256 and
            digest(signature_corpus(rows)) == BASELINE_CORPUS_SHA256,
            "Changed canonical original signature corpus")
    require(len({row["original_name"] for row in rows}) == len(rows), "Duplicate original relocation name")
    require(len({row["library_name"] for row in rows}) == len(rows), "Duplicate relocated library name")
    library_source = read_source(LIBRARY)
    require(not re.search(r"^[ \t]*(?:variable|variables|parameter|parameters|include|omit)\b",
                          mask_noncode(library_source), re.M),
            "Preserved Certificates must not acquire section parameters or assumptions")
    relocated = theorem_declarations(library_source)
    for row in rows:
        name, target = row["original_name"], row["library_name"]
        require(row["original_source_commit"] == BASELINE_COMMIT, f"Changed relocation baseline: {name}")
        require(target == name.replace("KFOL.Paper.", "KFOL.Results.", 1), f"Changed relocation mapping: {name}")
        require(target in relocated, f"Missing preserved library theorem: {target}")
        require(digest(relocated[target].signature) == row["signature_sha256"],
                f"Changed complete relocated signature: {target}")
    original_text = baseline_source()
    if original_text is not None:
        require(digest(original_text) == BASELINE_SOURCE_SHA256, "Changed historical relocation source")
        original = theorem_declarations(original_text)
        require(set(original) == {row["original_name"] for row in rows},
                "Relocation manifest does not cover all historical signatures")
        for row in rows:
            expected = original[row["original_name"]].signature
            require(row["signature_sha256"] == digest(expected),
                    f"Changed historical signature fingerprint: {row['original_name']}")
            require(relocated[row["library_name"]].signature == expected,
                    f"Changed exact historical signature text: {row['library_name']}")
    return len(rows)


def main() -> None:
    libraries = library_declarations()
    declarations = {entry: check_facade(entry, libraries) for entry in ENTRYPOINTS}
    preserved = check_relocations()
    print(f"Audited façades: {len(declarations['Paper'])} Paper and {len(declarations['Report'])} Report statements; "
          f"{preserved} complete original signatures preserved.")


if __name__ == "__main__":
    main()
