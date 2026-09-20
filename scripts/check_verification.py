#!/usr/bin/env python3
"""Keep advertised coverage, proof audits, and supplement status in agreement.

Run this in addition to `lake build`: the build executes the Lean axiom checks;
this script makes sure every advertised theorem actually has such a check.
"""

from pathlib import Path
import re
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
NAME = r"Papers\.[A-Za-z0-9_]+\.[A-Za-z0-9_.]+"


def without_comments(source: str) -> str:
    """Remove Lean's nested comments without turning commented commands into checks."""
    out = []
    depth = 0
    i = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if source[i] == "\n" else " ")
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError("unterminated Lean block comment")
    return "".join(out)


def check(root: Path = ROOT) -> tuple[list[str], int]:
    errors = []
    total = 0
    for metadata in sorted((root / "Papers").glob("*/paper.toml")):
        paper = tomllib.loads(metadata.read_text(encoding="utf-8"))
        folder = metadata.parent
        coverage = (folder / paper["coverage"]).read_text(encoding="utf-8")
        declarations = set()
        pending = False
        for line in coverage.splitlines():
            if not line.startswith("|"):
                continue
            cells = [cell.strip().strip("`") for cell in line.strip("|").split("|")]
            pending |= "pending" in cells
            if "verified" not in cells:
                continue
            names = re.findall(rf"`({NAME})`", line)
            if not names:
                errors.append(f"{paper['id']}: verified row has no fully qualified theorem")
            for name in names:
                if not name.startswith(f"Papers.{paper['id']}."):
                    errors.append(f"{paper['id']}: theorem belongs to another supplement: {name}")
                declarations.add(name)
        audit = (folder / "Axioms.lean").read_text(encoding="utf-8")
        # Audit modules are declarative: imports, reports, and assertions only.
        # In particular, an early-exit command must not bypass advertised checks.
        try:
            audit = without_comments(audit)
        except ValueError as error:
            errors.append(f"{paper['id']}: {error}")
            continue
        for line in audit.splitlines():
            if line.strip() and not re.fullmatch(
                rf"(?:import [A-Za-z0-9_.]+|#print axioms {NAME}|#assert_standard_axioms {NAME})",
                line.strip(),
            ):
                errors.append(f"{paper['id']}: unexpected command in Axioms.lean: {line.strip()}")
        checked = set(re.findall(rf"^#assert_standard_axioms ({NAME})\s*$", audit, re.M))
        printed = set(re.findall(rf"^#print axioms ({NAME})\s*$", audit, re.M))
        for label, actual in [("axiom assertion", checked), ("axiom report", printed)]:
            for name in sorted(declarations - actual):
                errors.append(f"{paper['id']}: missing {label} for {name}")
            for name in sorted(actual - declarations):
                errors.append(f"{paper['id']}: {label} has no verified coverage row: {name}")
        status = paper["verification_status"]
        if status == "scaffold" and declarations:
            errors.append(f"{paper['id']}: scaffold has verified results")
        elif status in {"in-progress", "complete-for-scope"} and not declarations:
            errors.append(f"{paper['id']}: {status} has no verified results")
        elif status not in {"scaffold", "in-progress", "complete-for-scope"}:
            errors.append(f"{paper['id']}: unknown status {status}")
        if status == "complete-for-scope" and pending:
            errors.append(f"{paper['id']}: complete-for-scope still has pending rows")
        total += len(declarations)
    return errors, total


if __name__ == "__main__":
    errors, total = check()
    if errors:
        print("\n".join(errors), file=sys.stderr)
        sys.exit(1)
    print(f"Coverage and axiom audits agree for {total} verified declarations.")
