#!/usr/bin/env python3
"""Adversarial checks of the prototype's correspondence and language boundaries."""

from __future__ import annotations

import os
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LAKE = os.environ.get("LAKE", "lake")
PRELUDE = r"""import Papers.Rockel2026ExactBlest.ArticleBridge
import Papers.Rockel2026ExactBlest.ArticleProof
open Companion Papers.Rockel2026ExactBlest.ArticleBridge
open ClaimSymbol
"""

CASES = {
    "a false intermediate step cannot reuse the valid document": (r"""
namespace ProofMutation
open Papers.Rockel2026ExactBlest.ArticleProof
def changed : Argument Symbol [] := .have [math| |- 0 = 1] corollaryProof
theorem bad : changed.Valid model (fun _ => True) := corollary_valid
end ProofMutation
""", "type mismatch"),
    "a changed extremizer value cannot reuse its certificate": (r"""
namespace ExtremizerMutation
open Papers.Rockel2026ExactBlest.ArticleProof
theorem bad : extremizer.spearmanRho = 1 := extremizer_values.1
end ExtremizerMutation
""", "type mismatch"),
    "wrong external context": (r"""
def bad : Expr ClaimSymbol [law] .real :=
  [math| D, C |- \nu(C)]
""", "rfl"),
    "unbound variable": (r"""
def bad : Expr ClaimSymbol [] .prop :=
  [math| |- Let C be copula. \nu(D) \le 1]
""", "unbound mathematical variable"),
    "wrong symbol type": (r"""
def bad : Expr ClaimSymbol [] .prop :=
  [math| |- Let C be copula. \nu(1) \le 1]
""", "type mismatch"),
    "unknown symbol": (r"""
def bad : Expr ClaimSymbol [] .prop :=
  [math| |- Let C be copula. \unknownCoefficient(C) \le 1]
""", "unknown identifier"),
    "shadowed binder": (r"""
def bad : Expr ClaimSymbol [] .prop :=
  [math| |- Let C be copula. Let C be copula. \nu(C) \le 1]
""", "shadowed mathematical binder"),
    "unsupported grammar": (r"""
def bad : Expr ClaimSymbol [] .prop :=
  [math| |- Every C is nice]
""", "unexpected"),
    "changed bound cannot reuse certificate": (r"""
def changed : Expr ClaimSymbol [] .prop :=
  [math| |- Let C be copula. \abs{\nu(C) - \rho(C)} \le 0]
theorem bad : changed.eval articleModel () := article_verified
""", "type mismatch"),
    "changed coefficient cannot reuse definition bridge": (r"""
open CoefficientSymbol in
def changed : Expr CoefficientSymbol [law] .real :=
  [math| C |- 25 * \int_{0}^{1}{v}{\int_{0}^{1}{u}{(1 - \real{u}) * \cdf(C,u,v)}} - 2]
theorem bad (C : Law) (h : IsCopula C) : changed.eval coefficientModel (C, ()) =
    Papers.Rockel2026XiBlest.blestNu (toLean C h) := nu_definition_eq C h
""", "type mismatch"),
    "nonstandard axiom": (r"""
axiom fabricated : False
theorem bad : True := False.elim fabricated
#assert_companion_axioms bad
""", "nonstandard axiom fabricated"),
    "unfinished proof": (r"""
theorem bad : False := by sorry
#assert_companion_axioms bad
""", "nonstandard axiom sorryAx"),
}


def main() -> None:
    subprocess.run([LAKE, "build", "Companion.Tests",
                    "Companion.DocumentTests", "Papers.Rockel2026ExactBlest.ArticleDocument"], cwd=ROOT, check=True)
    temp_root = ROOT / ".lake" / "lean-mirror-tests"
    temp_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=temp_root) as tmp:
        Path(tmp).resolve().relative_to(temp_root.resolve())
        def check_case(item: tuple[int, tuple[str, tuple[str, str]]]) -> str:
            index, (name, (source, expected)) = item
            path = Path(tmp) / f"Reject{index}.lean"
            path.write_text(PRELUDE + source, encoding="utf-8")
            result = subprocess.run([LAKE, "env", "lean", str(path)], cwd=ROOT,
                                    capture_output=True, text=True, encoding="utf-8")
            output = result.stdout + result.stderr
            if result.returncode == 0 or expected.lower() not in output.lower():
                raise AssertionError(f"{name}: unexpected result\n{output}")
            return name

        with ThreadPoolExecutor(max_workers=2) as pool:
            for name in pool.map(check_case, enumerate(CASES.items())):
                print(f"PASS: rejected {name}", flush=True)
    print(f"All {len(CASES)} adversarial checks passed.")


if __name__ == "__main__":
    main()
