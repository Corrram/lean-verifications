import Verification.Nelsen16
import Verification.Nelsen16Order

/-! # Tables 1–2: Nelsen 16 constructor and zero endpoint -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem nelsen16_cdf_full (θ : ℝ) (hθ : 0 ≤ θ) (u v : I) :
    (Verification.nelsen16 θ hθ).cdf ![u,v] =
      if u = 0 ∨ v = 0 then 0 else
        let s := (u:ℝ)+(v:ℝ)-1-θ*((u:ℝ)⁻¹+(v:ℝ)⁻¹-1)
        (s+Real.sqrt (s^2+4*θ))/2 :=
  Verification.nelsen16_cdf_full θ hθ u v

theorem nelsen16_zero : Verification.nelsen16 0 le_rfl = Copula.countermonotonic :=
  Verification.nelsen16_zero

theorem nelsen16_cdf_continuous_parameter (u v : I) :
    Continuous (fun θ : Set.Ici (0:ℝ) =>
      (Verification.nelsen16 θ (Set.mem_Ici.mp θ.property)).cdf ![u,v]) :=
  Verification.nelsen16_cdf_continuous_parameter u v

theorem nelsen16_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 ≤ θ a) (ht : Filter.Tendsto θ l (nhds 0)) (u v : I) :
    Filter.Tendsto (fun a => (Verification.nelsen16 (θ a) (hθ a)).cdf ![u,v]) l
      (nhds (Copula.countermonotonic.cdf ![u,v])) :=
  Verification.nelsen16_tendsto_zero θ hθ ht u v

theorem nelsen16_lowerOrthant_monotone {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθη : θ ≤ η) :
    (Verification.nelsen16 θ hθ).LowerOrthantLE (Verification.nelsen16 η hη) :=
  Verification.nelsen16_lowerOrthant_monotone hθ hη hθη

theorem nelsen16_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 0 ≤ θ z) (hlim : Filter.Tendsto θ l Filter.atTop) (u v : I) :
    Filter.Tendsto (fun z => (Verification.nelsen16 (θ z) (hθ z)).cdf ![u,v]) l
      (nhds ((Copula.clayton 2 1 (by norm_num)).cdf ![u,v])) :=
  Verification.nelsen16_tendsto_atTop θ hθ hlim u v

end Papers.AnsariRockel2024
