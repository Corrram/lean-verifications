import Copula.Dependence.Nelsen12

/-! # Nelsen 12 lower-orthant parameter order from Table 3 -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

/-- For all finite admissible parameters θ ≤ η, Nelsen 12 at θ lies below
Nelsen 12 at η in lower-orthant order on the whole closed square. -/
theorem nelsen12_lowerOrthant {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η)
    (hθη : θ ≤ η) :
    (Copula.nelsen12 θ hθ).LowerOrthantLE (Copula.nelsen12 η hη) :=
  Copula.lowerOrthantLE_nelsen12 hθ hη hθη

end Papers.AnsariRockel2024
