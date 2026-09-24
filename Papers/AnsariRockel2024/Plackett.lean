import Verification.PlackettDensity
import Verification.PlackettConditional
import Verification.PlackettTails
import Verification.PlackettContinuity

/-! # Table 4: the Plackett copula and its actual Lebesgue density -/

open ProbabilityTheory MeasureTheory Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem plackett_cdf {θ : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1) (u v : I) :
    (Verification.plackett θ hθ).cdf ![u,v] =
      (1+(θ-1)*((u:ℝ)+(v:ℝ))-Real.sqrt ((1+(θ-1)*((u:ℝ)+(v:ℝ)))^2-
        4*θ*(θ-1)*(u:ℝ)*(v:ℝ)))/(2*(θ-1)) :=
  Verification.plackett_cdf hθ hne u v

theorem plackett_one : Verification.plackett 1 (by norm_num) = Copula.independence 2 :=
  Verification.plackett_one

theorem plackett_density {θ : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1) :
    (Verification.plackett θ hθ).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (Verification.plackettDensity θ (x 0) (x 1))) :=
  Verification.plackett_toMeasure_density hθ hne

theorem plackett_ci_iff {θ : ℝ} (hθ : 0 < θ) :
    (Verification.plackett θ hθ).IsCI ↔ 1 ≤ θ := Verification.plackett_ci_iff hθ

theorem plackett_cd_iff {θ : ℝ} (hθ : 0 < θ) :
    (Verification.plackett θ hθ).IsCD ↔ θ ≤ 1 := Verification.plackett_cd_iff hθ

theorem plackett_pqd_iff {θ : ℝ} (hθ : 0 < θ) :
    (Verification.plackett θ hθ).IsPQD ↔ 1 ≤ θ := Verification.plackett_pqd_iff hθ

theorem plackett_nqd_iff {θ : ℝ} (hθ : 0 < θ) :
    (Verification.plackett θ hθ).IsNQD ↔ θ ≤ 1 := Verification.plackett_nqd_iff hθ

theorem plackett_tails {θ : ℝ} (hθ : 0 < θ) :
    (Verification.plackett θ hθ).HasLowerTailDependence 0 ∧
      (Verification.plackett θ hθ).HasUpperTailDependence 0 := Verification.plackett_tails hθ

theorem plackett_cdf_rationalized {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    (Verification.plackett θ hθ).cdf ![u,v] =
      2*θ*(u:ℝ)*(v:ℝ)/(Verification.plackettA θ u v+Real.sqrt (Verification.plackettD θ u v)) :=
  Verification.plackett_cdf_rationalized hθ u v

theorem plackett_tendsto_parameter {A : Type*} {l : Filter A} (θ : A → ℝ)
    (hθ : ∀ a, 0 < θ a) {η : ℝ} (hη : 0 < η) (ht : Tendsto θ l (𝓝 η)) (u v : I) :
    Tendsto (fun a => (Verification.plackett (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((Verification.plackett η hη).cdf ![u,v])) :=
  Verification.plackett_tendsto_parameter θ hθ hη ht u v

theorem plackett_tendsto_zero {A : Type*} {l : Filter A} (θ : A → ℝ)
    (hθ : ∀ a, 0 < θ a) (ht : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun a => (Verification.plackett (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 (Copula.countermonotonic.cdf ![u,v])) :=
  Verification.plackett_tendsto_zero θ hθ ht u v

theorem plackett_tendsto_atTop {A : Type*} {l : Filter A} (θ : A → ℝ)
    (hθ : ∀ a, 0 < θ a) (ht : Tendsto θ l atTop) (u v : I) :
    Tendsto (fun a => (Verification.plackett (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((Copula.comonotonic 2).cdf ![u,v])) :=
  Verification.plackett_tendsto_atTop θ hθ ht u v

end Papers.AnsariRockel2024
