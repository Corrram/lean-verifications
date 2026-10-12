#!/usr/bin/env python3
"""Build the checked example, then export or check its reproducible LaTeX.

Uses only the standard library. LAKE may name a toolchain's lake executable.
No generation is allowed before a successful Lean build.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "examples" / "paper-bridge" / "blest-bound.tex"
COMPANION = ROOT / "examples" / "paper-bridge" / "blest-bound.json"
_toolchain = (ROOT / 'lean-toolchain').read_text().strip().replace('/', '--').replace(':', '---')
_direct = Path.home() / '.elan/toolchains' / _toolchain / 'bin' / ('lake.exe' if os.name == 'nt' else 'lake')
LAKE = os.environ.get("LAKE", str(_direct) if _direct.exists() else "lake")


def engine():
    path = ROOT / '.lake/packages/lean-mirror/scripts/mirror.py'
    spec = importlib.util.spec_from_file_location('lean_mirror_engine', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def latex_document(data, mirror):
    esc, clean = mirror.tex_escape, mirror.clean_math
    result = data['document']['results'][0]
    text = r'''\documentclass[11pt]{article}
\usepackage[a4paper,margin=24mm]{geometry}
\usepackage[T1]{fontenc}
\usepackage{lmodern,amsmath,amssymb,amsthm}
\usepackage[hidelinks]{hyperref}
\newtheorem*{corollary}{Corollary 3.2}
\setlength{\emergencystretch}{3em}
\begin{document}
\title{Sharp deviation between $\nu$ and $\rho$\\\large A LeanMirror companion}
\author{Marcus Rockel}
\date{}
\maketitle
'''
    text += 'Source: \\href{'+data['sourceUrl']+'}{'+esc(data['source'])+'}.\\par\n'
    text += esc(data['scope'])+'\n\n'
    text += '\\begin{corollary}\n'+mirror.formula_prose(result['checked']['statement']).replace('for every','For every',1)+'.\n\\end{corollary}\n'
    text += '\\section*{Definitions used below}\n'
    for d in data['definitions']:
        text += '\\hypertarget{def-'+d['key']+'}{}\\paragraph{'+esc(d['title'])+'}\n'+clean(d['latex'])+'\n\n'
    text += '\\section*{The checked proof}\n\\begin{proof}\n'+mirror.latex_proof(result['checked']['proof'])+'\\end{proof}\n'
    text += r'''\section*{Verification}
The proof follows the derivative argument in the published corollary. Every assertion above is generated from the typed proof tree certified by \texttt{ArticleProof.corollary\_valid}. Lean checks every intermediate step and the equivalence to the formal statement. The earlier region theorem, family values and survival identities are compiled dependencies.

The online companion compares the complete original statement and proof with this version. Notation, rendering and correspondence with the intended mathematics remain inspectable presentation components. The rest of the article is not reproduced as an executable document here.

To reproduce, run \texttt{python scripts/lean\_mirror.py --check} in the pinned repository after fetching its Lean dependencies.
\end{document}
'''
    return text


def run(*args: str) -> None:
    subprocess.run([LAKE, *args], cwd=ROOT, check=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="reject a stale committed document")
    args = parser.parse_args()
    run("build", "LeanMirror", "Papers.Rockel2026ExactBlest.ArticleDocument")
    mirror = engine()
    source = json.loads((OUTPUT.parent / 'source.json').read_text(encoding='utf-8'))
    excerpts = mirror.load_source(OUTPUT.parent, source)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    # Stage output so a failed exporter never overwrites the last successful artifact.
    temp_root = ROOT / ".lake" / "lean-mirror-export"
    temp_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=temp_root) as tmp:
        Path(tmp).resolve().relative_to(temp_root.resolve())
        fresh = Path(tmp) / OUTPUT.name
        fresh_json = Path(tmp) / COMPANION.name
        run("env", "lean", "--run", "scripts/ExportLeanMirror.lean", str(fresh_json))
        data = json.loads(fresh_json.read_text(encoding='utf-8'))
        data['original'] = {'provenance': source, 'latex': excerpts['corollary-3-2']}
        fresh_json.write_text(json.dumps(data, ensure_ascii=False, indent=2)+'\n', encoding='utf-8', newline='\n')
        fresh.write_text(latex_document(data, mirror), encoding='utf-8', newline='\n')
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
