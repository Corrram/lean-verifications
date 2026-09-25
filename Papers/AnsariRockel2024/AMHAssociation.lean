import Verification.AMHXi

/-! # Ali–Mikhail–Haq association formulas -/

open ProbabilityTheory MeasureTheory Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem amh_conditionalCDF {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) (v : I) :
    (fun u => (amh θ hmin hmax.le).conditionalCDF u v) =ᵐ[volume]
      fun u => Verification.amhPartial θ u v := Verification.amh_conditionalCDF hmin hmax v

theorem amh_chatterjeeXi {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) (h0 : θ≠0) :
    (amh θ hmin hmax.le).chatterjeeXi=
      -θ/6-2/3+3/θ-2/θ^2-2*(θ-1)^2*Real.log (1-θ)/θ^3 :=
  Verification.amh_chatterjeeXi hmin hmax h0

theorem amh_chatterjeeXi_zero : (amh 0 (by norm_num) (by norm_num)).chatterjeeXi=0 :=
  Verification.amh_chatterjeeXi_zero

end Papers.AnsariRockel2024
