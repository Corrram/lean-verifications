import Verification.GumbelTauEvaluation
import Verification.GumbelRho

/-! # Gumbel–Hougaard conditional law and reduction of the Table 6 tau integral -/

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem gumbel_conditionalCDF {θ : ℝ} (hθ : 1≤θ) (v : I)
    (hv : (v:ℝ)∈Ioo 0 1) :
    (fun u => (gumbel θ hθ).conditionalCDF u v) =ᵐ[volume]
      fun u => Verification.gumbelPartial θ u v :=
  Verification.gumbel_conditionalCDF hθ v hv

theorem gumbel_kendallTau_generator_integral {θ : ℝ} (hθ : 1≤θ) :
    (gumbel θ hθ).kendallTau =
      1-4*(∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
        (Verification.gumbelPsiDeriv θ⁻¹ (x+y))^2) :=
  Verification.gumbel_kendallTau_generator_integral hθ

theorem gumbel_kendallTau {θ : ℝ} (hθ : 1≤θ) :
    (gumbel θ hθ).kendallTau=(θ-1)/θ := Verification.gumbel_kendallTau hθ

theorem gumbel_spearmanRho_ratio_integral {θ : ℝ} (hθ : 1≤θ) :
    (gumbel θ hθ).spearmanRho=
      12*(∫ s in Ioi (0:ℝ), (1/(1+s+(1+s^θ)^θ⁻¹))^2)-3 :=
  Verification.gumbel_spearmanRho_ratio_integral hθ

end Papers.AnsariRockel2024
