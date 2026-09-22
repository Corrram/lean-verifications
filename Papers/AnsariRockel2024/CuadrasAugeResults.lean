import Verification.CuadrasAugeTau
import Verification.CuadrasAugeSingular

/-! # Exact Cuadras–Augé conditional law and all three Table 6 coefficients -/

open MeasureTheory ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- A conditional CDF version on the full closed parameter range; the value at
 the moving diagonal is irrelevant to the almost-everywhere identity. -/
theorem cuadrasAuge_conditionalCDF (δ v : I) :
    (fun u => (Copula.cuadrasAuge δ).conditionalCDF u v) =ᵐ[volume]
      fun u => cuadrasConditional δ u v := conditionalCDF_cuadrasAuge δ v

/-- Table 6: Spearman rho, including independence and comonotonicity. -/
theorem cuadrasAuge_rho (δ : I) :
    (Copula.cuadrasAuge δ).spearmanRho=3*(δ:ℝ)/(4-(δ:ℝ)) := cuadrasAuge_spearmanRho δ

/-- Table 6 and Appendix A.5: Chatterjee xi on all of [0,1]. -/
theorem cuadrasAuge_xi (δ : I) :
    (Copula.cuadrasAuge δ).chatterjeeXi=(δ:ℝ)^2/(2-(δ:ℝ)) := cuadrasAuge_chatterjeeXi δ

/-- Table 6: Kendall tau, including the singular comonotonic endpoint. -/
theorem cuadrasAuge_tau (δ : I) :
    (Copula.cuadrasAuge δ).kendallTau=(δ:ℝ)/(2-(δ:ℝ)) := cuadrasAuge_kendallTau δ

/-- Table 5: the exact TP2-density domain, including the singular endpoint. -/
theorem cuadrasAuge_density_tp2 (δ : I) :
    (Copula.cuadrasAuge δ).HasMTP2Density ↔ δ=0 := cuadrasAuge_density_tp2_iff δ

/-- Positive parameters charge the diagonal, so absolute continuity holds only at independence. -/
theorem cuadrasAuge_absolutelyContinuous (δ : I) :
    (Copula.cuadrasAuge δ).toMeasure ≪ (volume : Measure (Fin 2 → I)) ↔ δ=0 :=
  cuadrasAuge_absolutelyContinuous_iff δ

end Papers.AnsariRockel2024
