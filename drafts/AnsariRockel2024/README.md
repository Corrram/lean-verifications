# Uncompiled drafts: AnsariRockel2024 continuation (2026-09-25)

**None of these files has been compiled yet.** They are kept outside `Papers/` and
`Verification/` on purpose: the Lake globs build every file there with warnings as
errors, so dropping unchecked files in would break `lake build`. The drafts contain no
`sorry`, but they will need the usual round of fixes to names and tactics.

To check them, move each file to the matching path in the repository root,
run `lake build` on it and fix it up. After that, add the declarations to `Main.lean`,
`Axioms.lean` and `COVERAGE.md`, and run `python scripts/check_verification.py`.

## Contents

| Path | Target |
| --- | --- |
| Verification/TEVStudentCDF.lean | T_k as a gamma mixture; chi substitution; ∫ z^ν₊ Φ(βz) dN = m(ν) T_{ν+1}(β√(ν+1)) |
| Verification/TEVPickandsFormula.lean | t-EV stable tail/Pickands/CDF in printed Student-t form (Tables 1, 4) |
| Verification/TEVStudentDensity.lean | T_k density, derivative, ∫ pdf = 1 |
| Verification/TEVCorrelationOrder.lean | Pickands decreasing in ρ (density-balance derivative), extremal coefficient, tails |
| Verification/TEVEndpoints.lean | ρ=1 is M, ρ=−1 is Π |
| Verification/TEVLimits.lean | ν→∞: t-EV → Π for fixed ρ |
| Verification/TEVZeroLimit.lean | T_1 = Cauchy CDF; T_k→T_1; ν→0: t-EV → MO(α,α), α=½+arcsin ρ/π |
| Papers/AnsariRockel2024/TEV.lean | Table 1/4/5 t-EV wrappers: formula, CI, tails, LO/Schur ⇔ ρ order, closed-range orders |
| Papers/AnsariRockel2024/TEVLimits.lean | Table 4 audit: printed HR (ν→∞) limit refuted; ν→0 limit ≠ Π |
| Verification/ArchimedeanOrder.lean, Papers/.../ArchimedeanOrders.lean | Proposition 3.3 (i)–(iii) |
| Verification/SchurUnordered.lean, SchurUnorderedNelsen818.lean, Papers/.../SchurUnordered.lean | Table 3 "not ordered": Nelsen 2, 8, 15 neither Schur-increasing nor -decreasing; Nelsen 18 not decreasing |
| Verification/DecreasingRearrangement.lean, SchurRearrangement.lean, RearrangedCopula.lean, Papers/.../Rearrangement.lean | Decreasing rearrangement, Hardy–Littlewood–Pólya on [0,1], E↑/E↓; Lemma 2.4, Lemma 2.7, Proposition 3.1 |

## Still open after these drafts
- Nelsen 18 "not Schur-increasing" (numerical claim in source; no proof drafted).
- Starred numerical cells: Hüsler–Reiss TP2 (yes*), Joe-EV/Tawn/t-EV non-TP2 (no*), Mardia Schur (*).
  Numerically, Galambos (= Joe-EV at α=β=1) looks TP2, which would contradict Joe-EV "no*".
  Mardia Schur-monotonicity in |θ| checks out numerically.
- The journal comparison of the remaining cells. The published PDF's Table 4 t-EV row still prints the HR limit for ν→∞.
