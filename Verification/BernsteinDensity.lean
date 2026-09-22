import Verification.BernsteinXi
import Copula.Dependence.Density
import Copula.UnitInterval
import Mathlib.Analysis.Calculus.TangentCone.Real

open MeasureTheory ProbabilityTheory Polynomial Set
open scoped unitInterval BigOperators

namespace Verification

noncomputable def bernsteinKernel (C : Copula 2) (m n : ℕ) (u v : I) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n,
    C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] *
      bernsteinDerivative m (i.val+1) u * _root_.bernstein n (j.val+1) v

noncomputable def bernsteinDensity (C : Copula 2) (m n : ℕ) (x : Fin 2 → I) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n,
    C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] *
      bernsteinDerivative m (i.val+1) (x 0) * bernsteinDerivative n (j.val+1) (x 1)

theorem bernsteinKernel_mono (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) (u : I) :
    Monotone (bernsteinKernel C m n u) := by
  intro v w hvw
  have h : (fun u : I => min (bernsteinKernel C m n u v) (bernsteinKernel C m n u w)) =ᵐ[volume]
      fun u : I => bernsteinKernel C m n u v := by
    filter_upwards [conditionalCDF_bernstein_grid C m n hm hn v,
      conditionalCDF_bernstein_grid C m n hm hn w] with t ht hw
    apply min_eq_left
    unfold bernsteinKernel
    rw [← ht,← hw]
    exact measureReal_mono (Iic_subset_Iic.mpr hvw)
  have he := Measure.eq_of_ae_eq h
    (by unfold bernsteinKernel bernsteinDerivative; fun_prop)
    (by unfold bernsteinKernel bernsteinDerivative; fun_prop)
  exact min_eq_left_iff.mp (congrFun he u)

theorem bernsteinDensity_nonneg (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (x : Fin 2 → I) : 0 ≤ bernsteinDensity C m n x := by
  let p : ℝ[X] := ∑ i : Fin m, ∑ j : Fin n,
    Polynomial.C (C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] *
      bernsteinDerivative m (i.val+1) (x 0)) * bernsteinPolynomial ℝ n (j.val+1)
  have hp (v : I) : p.eval (v : ℝ) = bernsteinKernel C m n (x 0) v := by
    simp only [p,bernsteinKernel,eval_finsetSum,eval_mul,eval_C]
    rfl
  have hm' : MonotoneOn (fun v => p.eval v) (Icc 0 1) := by
    intro v hv w hw hvw
    change p.eval ((⟨v,hv⟩ : I) : ℝ) ≤ p.eval ((⟨w,hw⟩ : I) : ℝ)
    rw [hp,hp]
    exact bernsteinKernel_mono C m n hm hn (x 0) hvw
  have hd := (p.hasDerivAt (x 1 : ℝ)).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc_zero_one (x 1) (x 1).property)
  have h := hm'.derivWithin_nonneg (x := (x 1 : ℝ))
  rw [hd] at h
  simpa only [p,bernsteinDensity,bernsteinDerivative,derivative_sum,derivative_mul,
    derivative_C,zero_mul,zero_add,eval_finsetSum,eval_mul,eval_C] using h

theorem integral_Iic_bernsteinDerivative (m i : ℕ) (u : I) :
    (∫ t in Iic u, bernsteinDerivative m (i+1) t) = _root_.bernstein m (i+1) u := by
  rw [show (fun t : I => bernsteinDerivative m (i+1) t) =
      (fun t : I => (bernsteinPolynomial ℝ m (i+1)).derivative.eval (t : ℝ)) from rfl,
    Copula.integral_unit_Iic (fun t => (bernsteinPolynomial ℝ m (i+1)).derivative.eval t)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => (bernsteinPolynomial ℝ m (i+1)).hasDerivAt x)
    ((by fun_prop : Continuous (fun x : ℝ => (bernsteinPolynomial ℝ m (i+1)).derivative.eval x)).intervalIntegrable _ _)]
  simp only [bernsteinPolynomial.eval_at_0,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,sub_zero]
  rfl

theorem integral_Iic_bernsteinDensity (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (u : Fin 2 → I) :
    (∫ x in Iic u, bernsteinDensity C m n x) = (C.bernstein m n hm hn).cdf u := by
  have he : u = ![u 0,u 1] := by ext i; fin_cases i <;> rfl
  have hterm (i : Fin m) (j : Fin n) :
      (∫ x in Iic u, C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] *
        bernsteinDerivative m (i.val+1) (x 0) * bernsteinDerivative n (j.val+1) (x 1)) =
      C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] *
        _root_.bernstein m (i.val+1) (u 0) * _root_.bernstein n (j.val+1) (u 1) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    conv_lhs => rw [he]
    rw [Copula.integral_cube_Iic_mul,integral_Iic_bernsteinDerivative,integral_Iic_bernsteinDerivative]
  unfold bernsteinDensity
  simp (disch := intro i hi; exact Copula.integrable_continuous_cube _ (by unfold bernsteinDerivative; fun_prop)) only [integral_finsetSum,hterm]
  rw [Copula.cdf_bernstein,Copula.bernsteinCDF_eq_sum,Fin.sum_univ_succ]
  simp only [_root_.bernstein.z_zero,Copula.cdf_two_zero_left,zero_mul,
    Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  simp only [_root_.bernstein.z_zero,Copula.cdf_two_zero_right,zero_mul,zero_add,Fin.val_succ]

theorem toMeasure_bernstein_density (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    (C.bernstein m n hm hn).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (bernsteinDensity C m n x)) := by
  apply Copula.toMeasure_eq_withDensity_of_cdf_integral _
    (Copula.integrable_continuous_cube volume (by unfold bernsteinDensity bernsteinDerivative; fun_prop))
    (bernsteinDensity_nonneg C m n hm hn)
  exact integral_Iic_bernsteinDensity C m n hm hn

theorem integral_bernstein_density (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (f : (Fin 2 → I) → ℝ) :
    (∫ x, f x ∂(C.bernstein m n hm hn).toMeasure) =
      ∫ x, bernsteinDensity C m n x * f x := by
  rw [toMeasure_bernstein_density,integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x => ENNReal.ofReal (bernsteinDensity C m n x)) by
      unfold bernsteinDensity bernsteinDerivative; fun_prop) (by simp)]
  simp only [ENNReal.toReal_ofReal (bernsteinDensity_nonneg C m n hm hn _),smul_eq_mul]

end Verification
