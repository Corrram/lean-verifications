import Verification.AMHXi

/-! # Ali–Mikhail–Haq association formulas -/

open ProbabilityTheory MeasureTheory Copula
open scoped unitInterval Topology

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

theorem amh_chatterjeeXi_one : (amh 1 (by norm_num) le_rfl).chatterjeeXi=1/6 :=
  Verification.amh_chatterjeeXi_one

theorem amh_xi_bound_near_zero {θ : ℝ} (hmin : -1≤θ) (hhalf : θ≤1/2) :
    (amh θ hmin (by linarith)).chatterjeeXi≤4*θ^2 :=
  Verification.amh_xi_bound_near_zero hmin hhalf

theorem amh_xi_tendsto_zero {A : Type*} {l : Filter A} (θ : A → ℝ)
    (hmin : ∀ x, -1≤θ x) (hmax : ∀ x, θ x≤1) (hθ : Filter.Tendsto θ l (nhds 0)) :
    Filter.Tendsto (fun x => (amh (θ x) (hmin x) (hmax x)).chatterjeeXi) l (nhds 0) :=
  Verification.amh_xi_tendsto_zero θ hmin hmax hθ

end Papers.AnsariRockel2024
