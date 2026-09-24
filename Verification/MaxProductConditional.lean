import Verification.PowerPerspective
import Verification.StochasticRigidity
import Verification.MarshallOlkinOrder

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem maxProduct_independence_isSI (C : Copula 2) (hC : C.IsSI) (α β : I) :
    (maxProduct C (independence 2) ![α,β]).IsSI := by
  apply isSI_of_concave_formula _ (fun v x =>
    (x^(1-(α:ℝ))*cdfSection C (unitPower v β β.property.1) (x^(α:ℝ)))*
      (v:ℝ)^(1-(β:ℝ)))
  · intro v
    have hf := cdfSection_concave_of_isSI hC (unitPower v β β.property.1)
    have hf0 : cdfSection C (unitPower v β β.property.1) 0 = 0 := by
      simp [cdfSection]
    have hp := concave_power_perspective hf hf0
      (sub_nonneg.mpr α.property.2) (show 1-(α:ℝ) ≤ 1 by linarith [α.property.1])
    have he : 1-(1-(α:ℝ)) = (α:ℝ) := by ring
    rw [he] at hp
    simpa only [Pi.smul_apply,smul_eq_mul,mul_comm] using
      ConcaveOn.smul (Real.rpow_nonneg v.property.1 (1-(β:ℝ))) hp
  · intro u v
    rw [cdf_maxProduct,cdf_independence]
    simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,coe_unitPower,
      unitInterval.coe_symm_eq]
    have hu : (u:ℝ)^(α:ℝ) ∈ Icc (0:ℝ) 1 :=
      ⟨Real.rpow_nonneg u.property.1 _,Real.rpow_le_one u.property.1 u.property.2 α.property.1⟩
    rw [cdfSection,projIcc_of_mem zero_le_one hu]
    have he : (fun i : Fin 2 => unitPower (![u,v] i) (![α,β] i) (![α,β] i).property.1) =
        ![⟨(u:ℝ)^(α:ℝ),hu⟩,unitPower v β β.property.1] := by
      funext i; fin_cases i <;> rfl
    rw [he]
    ring

theorem maxProduct_independence_transpose (C : Copula 2) (α β : I) :
    (maxProduct C (independence 2) ![α,β]).transpose =
      maxProduct C.transpose (independence 2) ![β,α] := by
  apply ext_cdf
  intro u
  have hu : u = ![u 0,u 1] := by funext i; fin_cases i <;> rfl
  rw [hu,cdf_transpose,cdf_maxProduct,cdf_maxProduct]
  have he (a b c d : I) :
      (fun i : Fin 2 => unitPower (![a,b] i) (![c,d] i) (![c,d] i).property.1) =
        ![unitPower a c c.property.1,unitPower b d d.property.1] := by
    funext i; fin_cases i <;> rfl
  simp only [he,cdf_transpose,cdf_independence,Fin.prod_univ_two,coe_unitPower,
    Matrix.cons_val_zero,Matrix.cons_val_one,unitInterval.coe_symm_eq]
  ring

theorem maxProduct_independence_isCI (C : Copula 2) (hC : C.IsCI) (α β : I) :
    (maxProduct C (independence 2) ![α,β]).IsCI := by
  refine ⟨maxProduct_independence_isSI C hC.1 α β,?_⟩
  rw [maxProduct_independence_transpose]
  exact maxProduct_independence_isSI C.transpose hC.2 β α

end Verification
