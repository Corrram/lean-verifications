import Verification.TawnPickands

/-! # Table 4: canonical Pickands functions of four constructed families -/

open ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem tawn_pickands (θ : ℝ) (hθ : 1 ≤ θ) (α β t : I) :
    copulaPickands (Copula.tawn θ hθ α β) t =
      (1-(α:ℝ))*(1-(t:ℝ))+(1-(β:ℝ))*(t:ℝ)+
        (((α:ℝ)*(1-(t:ℝ)))^θ+((β:ℝ)*(t:ℝ))^θ)^θ⁻¹ :=
  Verification.tawn_pickands θ hθ α β t

theorem gumbel_pickands (θ : ℝ) (hθ : 1 ≤ θ) (t : I) :
    copulaPickands (Copula.gumbel θ hθ) t = ((1-(t:ℝ))^θ+(t:ℝ)^θ)^θ⁻¹ :=
  Verification.gumbel_pickands θ hθ t

theorem marshallOlkin_pickands (α β t : I) :
    copulaPickands (Copula.marshallOlkin α β) t =
      1-min ((α:ℝ)*(1-(t:ℝ))) ((β:ℝ)*(t:ℝ)) :=
  Verification.marshallOlkin_pickands α β t

theorem cuadrasAuge_pickands (α t : I) :
    copulaPickands (Copula.cuadrasAuge α) t = 1-(α:ℝ)*min (1-(t:ℝ)) (t:ℝ) :=
  Verification.cuadrasAuge_pickands α t

end Papers.AnsariRockel2024
