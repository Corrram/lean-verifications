import Verification.Nelsen13Tails
import Verification.Nelsen13Order
import Verification.Nelsen13Continuity
import Verification.Nelsen13Limits
import Verification.Nelsen13Dependence
import Verification.Nelsen13Density
import Verification.Nelsen13DensityMeasure

/-! # Tables 1–3: Nelsen 13 constructor, endpoints, orders, CI, and tails -/

open ProbabilityTheory
open MeasureTheory
open scoped unitInterval
open Filter
open scoped Topology

namespace Papers.AnsariRockel2024

theorem nelsen13_cdf (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (Verification.nelsen13 θ hθ.le).cdf ![u,v] =
      if u = 0 ∨ v = 0 then 0 else
        Real.exp (1-((1-Real.log (u:ℝ))^θ+(1-Real.log (v:ℝ))^θ-1)^θ⁻¹) :=
  Verification.nelsen13_cdf θ hθ u v

theorem nelsen13_zero : Verification.nelsen13 0 le_rfl = Verification.gumbelBarnett 1 :=
  Verification.nelsen13_zero

theorem nelsen13_one : Verification.nelsen13 1 zero_le_one = Copula.independence 2 :=
  Verification.nelsen13_one

theorem nelsen13_tails (θ : ℝ) (hθ : 0 ≤ θ) :
    (Verification.nelsen13 θ hθ).HasLowerTailDependence 0 ∧
      (Verification.nelsen13 θ hθ).HasUpperTailDependence 0 :=
  Verification.nelsen13_tails θ hθ

theorem nelsen13_lowerOrthant_monotone {θ η : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθη : θ ≤ η) :
    (Verification.nelsen13 θ hθ).LowerOrthantLE (Verification.nelsen13 η hη) :=
  Verification.nelsen13_lowerOrthant_monotone hθ hη hθη

theorem nelsen13_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 0 ≤ θ z) (hlim : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun z => (Verification.nelsen13 (θ z) (hθ z)).cdf ![u,v]) l
      (𝓝 ((Verification.gumbelBarnett 1).cdf ![u,v])) :=
  Verification.nelsen13_tendsto_zero θ hθ hlim u v

theorem nelsen13_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 0 ≤ θ z) (hlim : Tendsto θ l atTop) (u v : I) :
    Tendsto (fun z => (Verification.nelsen13 (θ z) (hθ z)).cdf ![u,v]) l
      (𝓝 (min (u:ℝ) (v:ℝ))) :=
  Verification.nelsen13_tendsto_atTop θ hθ hlim u v

theorem nelsen13_ci_iff (θ : ℝ) (hθ : 0 ≤ θ) :
    (Verification.nelsen13 θ hθ).IsCI ↔ 1 ≤ θ :=
  Verification.nelsen13_isCI_iff θ hθ

theorem nelsen13_schur_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (hθη : θ ≤ η) :
    (Verification.nelsen13 θ (by linarith)).SchurBothLE (Verification.nelsen13 η (by linarith)) :=
  Verification.nelsen13_schur_monotone hθ hη hθη

theorem nelsen13_density_tp2_requires_one (θ : ℝ) (hθ : 0 ≤ θ)
    (hd : (Verification.nelsen13 θ hθ).HasMTP2Density) : 1 ≤ θ :=
  Verification.nelsen13_density_tp2_requires_one θ hθ hd

theorem nelsen13_density_measure {θ : ℝ} (hθ : 1 ≤ θ) :
    (Verification.nelsen13 θ (by linarith)).toMeasure =
      (volume : Measure (Fin 2 → I)).withDensity
        (fun x => ENNReal.ofReal (Verification.n13Density θ x)) :=
  Verification.nelsen13_toMeasure_density hθ

theorem nelsen13_density_tp2_iff (θ : ℝ) (hθ : 0 ≤ θ) :
    (Verification.nelsen13 θ hθ).HasMTP2Density ↔ 1 ≤ θ :=
  Verification.nelsen13_density_tp2_iff θ hθ

end Papers.AnsariRockel2024
