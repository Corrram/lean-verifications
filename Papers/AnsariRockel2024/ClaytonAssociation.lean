import Papers.AnsariRockel2024.ClaytonResults
import Verification.ClaytonTau
import Verification.ClaytonNegativeTau
import Verification.ClaytonXi

/-! # Table 6: signed Clayton Kendall tau and positive Clayton Chatterjee xi -/

open ProbabilityTheory MeasureTheory Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem clayton_positive_conditionalCDF {θ : ℝ} (hθ : 0<θ) (v : I) (hv : 0<(v:ℝ)) :
    (fun u => (clayton 2 θ hθ).conditionalCDF u v) =ᵐ[volume]
      fun u => Verification.claytonPartial θ u v := Verification.clayton_conditionalCDF hθ v hv

theorem clayton_positive_kendallTau {θ : ℝ} (hθ : 0<θ) :
    (clayton 2 θ hθ).kendallTau=θ/(θ+2) := Verification.clayton_kendallTau hθ

theorem clayton_zero_kendallTau : (independence 2).kendallTau=0 := by simp

theorem clayton_negative_one_kendallTau :
    (claytonNegative (-1) (by norm_num) (by norm_num)).kendallTau= -1 := by
  rw [clayton_negative_one]
  simp

theorem clayton_negative_conditionalCDF {θ : ℝ} (hmin : -1<θ) (hmax : θ<0)
    (v : I) (hv : 0<(v:ℝ)) :
    (fun u => (claytonNegative θ hmin.le hmax).conditionalCDF u v) =ᵐ[volume]
      fun u => Verification.claytonNegativePartial θ u v :=
  Verification.claytonNegative_conditionalCDF hmin hmax v hv

theorem clayton_negative_kendallTau {θ : ℝ} (hmin : -1≤θ) (hmax : θ<0) :
    (claytonNegative θ hmin hmax).kendallTau=θ/(θ+2) := by
  by_cases he : θ= -1
  · subst θ
    rw [clayton_negative_one_kendallTau]
    norm_num
  · exact Verification.claytonNegative_kendallTau (lt_of_le_of_ne hmin (Ne.symm he)) hmax

theorem clayton_positive_chatterjeeXi {θ : ℝ} (hθ : 0<θ) :
    (clayton 2 θ hθ).chatterjeeXi =
      6*(∫ v : I, Verification.eulerHypergeometric (1/θ) (2+2/θ) (1/θ+1)
        (1-(v:ℝ)^(-θ)))-2 := Verification.clayton_chatterjeeXi hθ

end Papers.AnsariRockel2024
