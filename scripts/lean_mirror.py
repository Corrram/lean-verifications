#!/usr/bin/env python3
"""Build the checked example, then export or check its reproducible LaTeX.

Uses only the standard library. LAKE may name a toolchain's lake executable.
No generation is allowed before a successful Lean build.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "examples" / "paper-bridge" / "blest-bound.tex"
COMPANION = ROOT / "examples" / "paper-bridge" / "blest-bound.json"
LAKE = os.environ.get("LAKE", "lake")


def run(*args: str) -> None:
    subprocess.run([LAKE, *args], cwd=ROOT, check=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="reject a stale committed document")
    args = parser.parse_args()
    run("build", "LeanMirror", "Papers.Rockel2026ExactBlest.ArticlePresentation")
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    # Stage output so a failed exporter never overwrites the last successful artifact.
    temp_root = ROOT / ".lake" / "lean-mirror-export"
    temp_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=temp_root) as tmp:
        Path(tmp).resolve().relative_to(temp_root.resolve())
        fresh = Path(tmp) / OUTPUT.name
        fresh_json = Path(tmp) / COMPANION.name
        run("env", "lean", "--run", "scripts/ExportLeanMirror.lean", str(fresh), str(fresh_json))
        for staged, output in ((fresh, OUTPUT), (fresh_json, COMPANION)):
            generated = staged.read_text(encoding="utf-8")
            if args.check:
                if not output.exists() or output.read_text(encoding="utf-8") != generated:
                    raise SystemExit(f"Stale {output.name}. Run: python scripts/lean_mirror.py")
            else:
                output.write_text(generated, encoding="utf-8", newline="\n")
                print(f"Wrote {output}")
        if args.check:
            print("LaTeX and website companion match the checked syntax trees.")


if __name__ == "__main__":
    main()
