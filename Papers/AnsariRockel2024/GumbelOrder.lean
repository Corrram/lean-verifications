import Copula.Dependence.Gumbel

/-! # Gumbel–Hougaard lower-orthant parameter order from Table 3 -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

/-- For all finite admissible parameters θ ≤ η, Gumbel–Hougaard at θ lies
below Gumbel–Hougaard at η in lower-orthant order on the closed square. -/
theorem gumbel_lowerOrthant {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η)
    (hθη : θ ≤ η) :
    (Copula.gumbel θ hθ).LowerOrthantLE (Copula.gumbel η hη) :=
  Copula.lowerOrthantLE_gumbel hθ hη hθη

end Papers.AnsariRockel2024
