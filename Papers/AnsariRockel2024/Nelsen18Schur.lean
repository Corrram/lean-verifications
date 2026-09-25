import Verification.Nelsen18SchurIncreasing
import Papers.AnsariRockel2024.SchurUnordered

/-! # Table 3: Nelsen 18 is not Schur-ordered in its parameter

`nelsen18_not_schur_antitone` (in `SchurUnordered.lean`) excludes a decreasing order.
Here the convex test `z ↦ (z-5/8)₊` at threshold `1/9` shows `C₂ ≰_∂S C₄`, so the family
is not increasing either. Together with Archimedean symmetry, neither both-direction
monotonicity holds.
-/

open ProbabilityTheory Copula

namespace Papers.AnsariRockel2024

theorem nelsen18_two_not_schurLE_four :
    ¬ (Verification.nelsen18 2 le_rfl).SchurLE (Verification.nelsen18 4 (by norm_num)) :=
  Verification.N18Schur.nelsen18_two_not_schurLE_four

theorem nelsen18_not_schur_monotone :
    ¬ (∀ (θ η : ℝ) (hθ : 2 ≤ θ) (hθη : θ ≤ η),
      (Verification.nelsen18 θ hθ).SchurLE (Verification.nelsen18 η (hθ.trans hθη))) :=
  Verification.N18Schur.nelsen18_not_schur_monotone

end Papers.AnsariRockel2024
