#!/usr/bin/env python3
"""Create a paper supplement from the checked-in template (Python 3.11+)."""

import argparse
from pathlib import Path
import re
import tomllib


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paper_id", help="Permanent identifier, e.g. Author2026ShortTitle")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Z][A-Za-z0-9]*", args.paper_id):
        parser.error("Use an uppercase initial letter followed by ASCII letters or digits.")
    reserved = {"CON", "PRN", "AUX", "NUL", "CLOCK$"}
    reserved.update(f"{prefix}{i}" for prefix in ("COM", "LPT") for i in range(1, 10))
    if args.paper_id.upper() in reserved:
        parser.error("This identifier is reserved on Windows; choose a descriptive paper ID.")

    root = Path(__file__).resolve().parents[1]
    papers = root / "Papers"
    destination = papers / args.paper_id
    if any(path.name.casefold() == args.paper_id.casefold() for path in papers.iterdir()):
        parser.error(f"A paper or file named {args.paper_id} already exists; nothing was changed.")

    # Render and validate before creating the destination. Never overwrite a paper.
    template = root / "templates" / "paper"
    rendered = {
        path.name: path.read_text(encoding="utf-8").replace("__PAPER_ID__", args.paper_id)
        for path in sorted(template.iterdir()) if path.is_file()
    }
    tomllib.loads(rendered["paper.toml"])
    destination.mkdir()
    for name, content in rendered.items():
        (destination / name).write_text(content, encoding="utf-8", newline="\n")

    print(f"Created Papers/{args.paper_id}/")
    print("Fill in paper.toml, README.md, references.bib, and COVERAGE.md.")
    print("Add the article to README.md and Papers/README.md, then run lake build.")


if __name__ == "__main__":
    main()
