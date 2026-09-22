import Verification.CuadrasAugeXi

/-! # Exact Cuadras–Augé conditional law, rho, and xi -/

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

end Papers.AnsariRockel2024
