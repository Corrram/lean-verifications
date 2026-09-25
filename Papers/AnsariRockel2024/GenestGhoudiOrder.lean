import Verification.GenestGhoudiOrder

/-! # Table 3: Genest–Ghoudi lower-orthant parameter order -/

open ProbabilityTheory Copula

namespace Papers.AnsariRockel2024

/-- Table 3: Genest–Ghoudi (Nelsen 15) increases in lower-orthant order. -/
theorem genestGhoudi_lowerOrthant_mono {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) :
    (genestGhoudi θ hθ).LowerOrthantLE (genestGhoudi η (hθ.trans hθη)) :=
  Verification.GenestGhoudiOrder.genestGhoudi_lowerOrthant_mono hθ hθη

end Papers.AnsariRockel2024
