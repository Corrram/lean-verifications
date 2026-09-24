import Verification.Nelsen17Density
import Verification.Nelsen17Order
import Verification.Nelsen17UpperLimit
import Verification.Nelsen17ZeroLimit
import Verification.Nelsen17LowerLimit
import Verification.Nelsen17Tails

/-! # Tables 1–2: Nelsen 17 on both nonzero parameter branches -/

open ProbabilityTheory Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem nelsen17_cdf_full (θ : ℝ) (hθ : θ ≠ 0) (u v : I) :
    (Verification.nelsen17 θ hθ).cdf ![u,v] =
      (1+(((1+(u:ℝ))^(-θ)-1)*((1+(v:ℝ))^(-θ)-1))/((2:ℝ)^(-θ)-1))^(-θ⁻¹)-1 :=
  Verification.nelsen17_cdf_full θ hθ u v

theorem nelsen17_neg_one : Verification.nelsen17 (-1) (by norm_num) = Copula.independence 2 :=
  Verification.nelsen17_neg_one

theorem nelsen17_isCI (θ : ℝ) (hθ : θ ≠ 0) (hθ1 : -1 ≤ θ) :
    (Verification.nelsen17 θ hθ).IsCI :=
  Verification.nelsen17_isCI θ hθ hθ1

theorem nelsen17_isCD (θ : ℝ) (hθ : θ ≠ 0) (hθ1 : θ ≤ -1) :
    (Verification.nelsen17 θ hθ).IsCD :=
  Verification.nelsen17_isCD θ hθ hθ1

theorem nelsen17_tails (θ : ℝ) (hθ : θ ≠ 0) :
    (Verification.nelsen17 θ hθ).HasLowerTailDependence 0 ∧
      (Verification.nelsen17 θ hθ).HasUpperTailDependence 0 :=
  Verification.nelsen17_tails θ hθ

theorem nelsen17_isCI_iff (θ : ℝ) (hθ : θ ≠ 0) :
    (Verification.nelsen17 θ hθ).IsCI ↔ -1 ≤ θ :=
  Verification.nelsen17_isCI_iff θ hθ

theorem nelsen17_isCD_iff (θ : ℝ) (hθ : θ ≠ 0) :
    (Verification.nelsen17 θ hθ).IsCD ↔ θ ≤ -1 :=
  Verification.nelsen17_isCD_iff θ hθ

theorem nelsen17_isPQD_iff (θ : ℝ) (hθ : θ ≠ 0) :
    (Verification.nelsen17 θ hθ).IsPQD ↔ -1 ≤ θ :=
  Verification.nelsen17_isPQD_iff θ hθ

theorem nelsen17_isNQD_iff (θ : ℝ) (hθ : θ ≠ 0) :
    (Verification.nelsen17 θ hθ).IsNQD ↔ θ ≤ -1 :=
  Verification.nelsen17_isNQD_iff θ hθ

theorem nelsen17_toMeasure_density (θ : ℝ) (hθ : θ ≠ 0) :
    (Verification.nelsen17 θ hθ).toMeasure =
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 2 → I)).withDensity
        (fun x => ENNReal.ofReal (Verification.n17Density (-θ) x)) := by
  simpa only [neg_neg] using Verification.n17_toMeasure_density (neg_ne_zero.mpr hθ)

theorem nelsen17_density_tp2_iff (θ : ℝ) (hθ : θ ≠ 0) :
    (Verification.nelsen17 θ hθ).HasMTP2Density ↔ -1 ≤ θ :=
  Verification.nelsen17_density_tp2_iff θ hθ

theorem nelsen17_lowerOrthant_monotone {θ η : ℝ}
    (hθ : θ ≠ 0) (hη : η ≠ 0) (hθη : θ ≤ η) :
    (Verification.nelsen17 θ hθ).LowerOrthantLE (Verification.nelsen17 η hη) :=
  Verification.nelsen17_lowerOrthant_monotone hθ hη hθη

theorem nelsen17_schur_monotone {θ η : ℝ} (hθ : θ ≠ 0) (hη : η ≠ 0)
    (hθ1 : -1 ≤ θ) (hθη : θ ≤ η) :
    (Verification.nelsen17 θ hθ).SchurBothLE (Verification.nelsen17 η hη) :=
  Verification.nelsen17_schur_monotone hθ hη hθ1 hθη

theorem nelsen17_schur_antitone {θ η : ℝ} (hθ : θ ≠ 0) (hη : η ≠ 0)
    (hη1 : η ≤ -1) (hθη : θ ≤ η) :
    (Verification.nelsen17 η hη).SchurBothLE (Verification.nelsen17 θ hθ) :=
  Verification.nelsen17_schur_antitone hθ hη hη1 hθη

theorem nelsen17_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, θ a ≠ 0) (ht : Tendsto θ l atTop) (u v : I) :
    Tendsto (fun a => (Verification.nelsen17 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((Copula.comonotonic 2).cdf ![u,v])) :=
  Verification.nelsen17_tendsto_atTop θ hθ ht u v

theorem nelsen17_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, θ a ≠ 0) (ht : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun a => (Verification.nelsen17 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 (Real.exp (Real.log (1+(u:ℝ))*Real.log (1+(v:ℝ))/Real.log 2)-1)) :=
  Verification.nelsen17_tendsto_zero θ hθ ht u v

theorem nelsen17_tendsto_atBot {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, θ a ≠ 0) (ht : Tendsto θ l atBot) (u v : I) :
    Tendsto (fun a => (Verification.nelsen17 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 (max 1 ((1+(u:ℝ))*(1+(v:ℝ))/2)-1)) :=
  Verification.nelsen17_tendsto_atBot θ hθ ht u v

end Papers.AnsariRockel2024
