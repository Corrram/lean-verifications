import Verification.GumbelConditional
import Verification.JoeConditional
import Verification.JoeOrder
import Verification.JoeDensity
import Verification.GumbelDensity

/-! # Table 3: Gumbel–Hougaard and Joe conditional increase and parameter orders -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

theorem gumbel_ci (θ : ℝ) (hθ : 1 ≤ θ) : (Copula.gumbel θ hθ).IsCI :=
  Verification.gumbel_isCI θ hθ

theorem gumbel_schur_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (hθη : θ ≤ η) :
    (Copula.gumbel θ hθ).SchurBothLE (Copula.gumbel η hη) :=
  Verification.gumbel_schur_monotone hθ hη hθη

theorem joe_ci (θ : ℝ) (hθ : 1 ≤ θ) : (Copula.joe θ hθ).IsCI :=
  Verification.joe_isCI θ hθ

theorem joe_lowerOrthant_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (hθη : θ ≤ η) :
    (Copula.joe θ hθ).LowerOrthantLE (Copula.joe η hη) :=
  Verification.joe_lowerOrthant_monotone hθ hη hθη

theorem joe_schur_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (hθη : θ ≤ η) :
    (Copula.joe θ hθ).SchurBothLE (Copula.joe η hη) :=
  Verification.joe_schur_monotone hθ hη hθη

theorem joe_toMeasure_density {θ : ℝ} (hθ : 1 ≤ θ) :
    (Copula.joe θ hθ).toMeasure =
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 2 → unitInterval)).withDensity
        (fun x => ENNReal.ofReal (Verification.joeDensity θ x)) :=
  Verification.joe_toMeasure_density hθ

theorem joe_density_tp2 {θ : ℝ} (hθ : 1 ≤ θ) : (Copula.joe θ hθ).HasMTP2Density :=
  Verification.joe_hasMTP2Density hθ

theorem gumbel_toMeasure_density {θ : ℝ} (hθ : 1 ≤ θ) :
    (Copula.gumbel θ hθ).toMeasure =
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 2 → unitInterval)).withDensity
        (fun x => ENNReal.ofReal (Verification.gumbelDensity θ x)) :=
  Verification.gumbel_toMeasure_density hθ

theorem gumbel_density_tp2 {θ : ℝ} (hθ : 1 ≤ θ) : (Copula.gumbel θ hθ).HasMTP2Density :=
  Verification.gumbel_hasMTP2Density hθ

end Papers.AnsariRockel2024
