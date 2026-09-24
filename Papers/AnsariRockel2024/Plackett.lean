import Verification.PlackettDensity

/-! # Table 4: the Plackett copula and its actual Lebesgue density -/

open ProbabilityTheory MeasureTheory
open scoped unitInterval

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

end Papers.AnsariRockel2024
