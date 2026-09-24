import Verification.Nelsen20
import Verification.Nelsen20Conditional
import Verification.Nelsen20Tails
import Verification.Nelsen20Limits
import Verification.Nelsen20Order
import Verification.Nelsen20Density

/-! # Tables 1–3: Nelsen 20 constructor, independence member, CI and tails -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem nelsen20_cdf {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    (Verification.nelsen20 θ hθ.le).cdf ![u,v] =
      if u = 0 ∨ v = 0 then 0 else
        Real.log (Real.exp ((u:ℝ)^(-θ))+Real.exp ((v:ℝ)^(-θ))-Real.exp 1)^(-θ⁻¹) :=
  Verification.nelsen20_cdf hθ u v

theorem nelsen20_zero : Verification.nelsen20 0 le_rfl = Copula.independence 2 :=
  Verification.nelsen20_zero

theorem nelsen20_ci (θ : ℝ) (hθ : 0 ≤ θ) : (Verification.nelsen20 θ hθ).IsCI :=
  Verification.nelsen20_isCI θ hθ

theorem nelsen20_tails (θ : ℝ) (hθ : 0 ≤ θ) :
    (Verification.nelsen20 θ hθ).HasLowerTailDependence (if θ = 0 then 0 else 1) ∧
      (Verification.nelsen20 θ hθ).HasUpperTailDependence 0 :=
  Verification.nelsen20_tails θ hθ

theorem nelsen20_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 ≤ θ a) (ht : Filter.Tendsto θ l (nhds 0)) (u v : I) :
    Filter.Tendsto (fun a => (Verification.nelsen20 (θ a) (hθ a)).cdf ![u,v]) l
      (nhds ((Copula.independence 2).cdf ![u,v])) :=
  Verification.nelsen20_tendsto_zero θ hθ ht u v

theorem nelsen20_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 ≤ θ a) (ht : Filter.Tendsto θ l Filter.atTop) (u v : I) :
    Filter.Tendsto (fun a => (Verification.nelsen20 (θ a) (hθ a)).cdf ![u,v]) l
      (nhds ((Copula.comonotonic 2).cdf ![u,v])) :=
  Verification.nelsen20_tendsto_atTop θ hθ ht u v

theorem nelsen20_lowerOrthant_monotone {θ η : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθη : θ ≤ η) :
    (Verification.nelsen20 θ hθ).LowerOrthantLE (Verification.nelsen20 η hη) :=
  Verification.nelsen20_lowerOrthant_monotone hθ hη hθη

theorem nelsen20_schur_monotone {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθη : θ ≤ η) :
    (Verification.nelsen20 θ hθ).SchurBothLE (Verification.nelsen20 η hη) :=
  Verification.nelsen20_schur_monotone hθ hη hθη

theorem nelsen20_toMeasure_density {θ : ℝ} (hθ : 0 < θ) :
    (Verification.nelsen20 θ hθ.le).toMeasure =
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 2 → I)).withDensity
        (fun x => ENNReal.ofReal (Verification.n20Density θ x)) :=
  Verification.n20_toMeasure_density hθ

theorem nelsen20_density_tp2 (θ : ℝ) (hθ : 0 ≤ θ) : (Verification.nelsen20 θ hθ).HasMTP2Density :=
  Verification.nelsen20_density_tp2 θ hθ

end Papers.AnsariRockel2024
