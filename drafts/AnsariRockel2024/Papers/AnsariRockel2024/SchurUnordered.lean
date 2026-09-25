import Verification.SchurUnorderedNelsen818
import Copula.Order.SymmetricSchur

/-! # Table 3: families that are not Schur ordered in their parameter

Table 3 marks Nelsen 2, Nelsen 8, Genest–Ghoudi (Nelsen 15), Nelsen 18 and Nelsen 21 as not
ordered in `≤_∂S` (numerical observation `*`). We prove, for the directional order and hence
for the two-direction order, that Nelsen 2, Nelsen 8 and Genest–Ghoudi are neither
increasing nor decreasing, and that Nelsen 18 is not decreasing. (Nelsen 21 is covered in
`Nelsen21.lean`.) For Archimedean copulas the directional and two-direction orders agree.
-/

open ProbabilityTheory Copula

namespace Papers.AnsariRockel2024

theorem nelsen2_not_schur_monotone :
    ¬ (∀ (θ η : ℝ) (hθ : 1≤θ) (hθη : θ≤η), (nelsen2 θ hθ).SchurLE (nelsen2 η (hθ.trans hθη))) :=
  Verification.nelsen2_not_schur_monotone

theorem nelsen2_not_schur_antitone :
    ¬ (∀ (θ η : ℝ) (hθ : 1≤θ) (hθη : θ≤η), (nelsen2 η (hθ.trans hθη)).SchurLE (nelsen2 θ hθ)) :=
  Verification.nelsen2_not_schur_antitone

theorem genestGhoudi_not_schur_monotone :
    ¬ (∀ (θ η : ℝ) (hθ : 1≤θ) (hθη : θ≤η),
      (genestGhoudi θ hθ).SchurLE (genestGhoudi η (hθ.trans hθη))) :=
  Verification.genestGhoudi_not_schur_monotone

theorem genestGhoudi_not_schur_antitone :
    ¬ (∀ (θ η : ℝ) (hθ : 1≤θ) (hθη : θ≤η),
      (genestGhoudi η (hθ.trans hθη)).SchurLE (genestGhoudi θ hθ)) :=
  Verification.genestGhoudi_not_schur_antitone

theorem nelsen8_not_schur_monotone :
    ¬ (∀ (θ η : ℝ) (hθ : 1≤θ) (hθη : θ≤η), (nelsen8 θ hθ).SchurLE (nelsen8 η (hθ.trans hθη))) :=
  Verification.nelsen8_not_schur_monotone

theorem nelsen8_not_schur_antitone :
    ¬ (∀ (θ η : ℝ) (hθ : 1≤θ) (hθη : θ≤η), (nelsen8 η (hθ.trans hθη)).SchurLE (nelsen8 θ hθ)) :=
  Verification.nelsen8_not_schur_antitone

/-- Exact conditional energy of Nelsen 8 at `θ=5`, threshold `1/4`, used above. -/
theorem nelsen8_five_quarter_energy :
    (∫ u : unitInterval, (nelsen8 5 (by norm_num)).conditionalCDF u Verification.unitQuarter ^ 2)=279/3600 :=
  Verification.nelsen8_five_quarter_energy

theorem nelsen18_not_schur_antitone :
    ¬ (∀ (θ η : ℝ) (hθ : 2≤θ) (hθη : θ≤η),
      (Verification.nelsen18 η (hθ.trans hθη)).SchurLE (Verification.nelsen18 θ hθ)) :=
  Verification.nelsen18_not_schur_antitone

end Papers.AnsariRockel2024
