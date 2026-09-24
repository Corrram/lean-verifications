import Verification.Nelsen19
import Verification.Nelsen19Conditional
import Verification.Nelsen19Tails
import Verification.Nelsen19Limits

/-! # Tables 1–3: Nelsen 19 constructor, zero limit, CI and tails -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem nelsen19_cdf {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    (Verification.nelsen19 θ hθ.le).cdf ![u,v] =
      if u = 0 ∨ v = 0 then 0 else
        θ/Real.log (Real.exp (θ/(u:ℝ))+Real.exp (θ/(v:ℝ))-Real.exp θ) :=
  Verification.nelsen19_cdf hθ u v

theorem nelsen19_zero : Verification.nelsen19 0 le_rfl = Copula.clayton 2 1 (by norm_num) :=
  Verification.nelsen19_zero

theorem nelsen19_ci (θ : ℝ) (hθ : 0 ≤ θ) : (Verification.nelsen19 θ hθ).IsCI :=
  Verification.nelsen19_isCI θ hθ

theorem nelsen19_tails (θ : ℝ) (hθ : 0 ≤ θ) :
    (Verification.nelsen19 θ hθ).HasLowerTailDependence (if θ = 0 then 1/2 else 1) ∧
      (Verification.nelsen19 θ hθ).HasUpperTailDependence 0 :=
  Verification.nelsen19_tails θ hθ

theorem nelsen19_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 ≤ θ a) (ht : Filter.Tendsto θ l (nhds 0)) (u v : I) :
    Filter.Tendsto (fun a => (Verification.nelsen19 (θ a) (hθ a)).cdf ![u,v]) l
      (nhds ((Copula.clayton 2 1 (by norm_num)).cdf ![u,v])) :=
  Verification.nelsen19_tendsto_zero θ hθ ht u v

end Papers.AnsariRockel2024
