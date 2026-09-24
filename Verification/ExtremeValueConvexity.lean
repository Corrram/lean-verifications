import Verification.ExtremeValueLog
import Verification.GeometricConvexity

/-! # Convex logarithmic sections of arbitrary extreme-value copulas -/

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

/-- Extension to real first coordinates, clamped at the logarithmic boundary. -/
noncomputable def extremeValueLogSection (C : Copula 2) (y : ℝ) (hy : 0≤y) (x : ℝ) : ℝ :=
  extremeValueLog C (max x 0) y (le_max_right _ _) hy

theorem extremeValueLogSection_of_nonneg (C : Copula 2) (y : ℝ) (hy : 0≤y)
    (x : ℝ) (hx : 0≤x) : extremeValueLogSection C y hy x=extremeValueLog C x y hx hy := by
  simp only [extremeValueLogSection,max_eq_left hx]

theorem extremeValueLogSection_continuous (C : Copula 2) (hC : C.IsExtremeValue)
    (y : ℝ) (hy : 0≤y) : Continuous (extremeValueLogSection C y hy) := by
  have hu : Continuous (fun x : ℝ => unitNegExp (max x 0) (le_max_right _ _)) := by
    unfold unitNegExp
    fun_prop
  have hc : Continuous (fun x : ℝ => C.cdf ![unitNegExp (max x 0) (le_max_right _ _),unitNegExp y hy]) :=
    C.continuous_cdf.comp (by fun_prop)
  exact (hc.log (fun x => (extremeValue_exp_cdf_pos C hC (max x 0) y _ hy).ne')).neg

theorem extremeValueLogSection_geometric (C : Copula 2) (hC : C.IsExtremeValue)
    (y : ℝ) (hy : 0≤y) (x r : ℝ) (hx : 0<x) (hr : 1<r) :
    (r+1)*extremeValueLogSection C y hy x ≤
      r*extremeValueLogSection C y hy (x/r)+extremeValueLogSection C y hy (r*x) := by
  have hr0 : 0<r := by linarith
  have hri : 0≤1/r := by positivity
  have hxdiv : 0≤x/r := div_nonneg hx.le hr0.le
  have hydiv : 0≤y/r := div_nonneg hy hr0.le
  have hxx : x/r≤x := (div_le_self hx.le hr.le)
  have hyy : y/r≤y := (div_le_self hy hr.le)
  have hhom1 := extremeValueLog_homogeneous C hC x y (1/r) hx.le hy hri
  have hhom2 := extremeValueLog_homogeneous C hC (r*x) y (1/r) (mul_nonneg hr0.le hx.le) hy hri
  have he : (1/r)*(r*x)=x := by field_simp
  simp only [he] at hhom2
  have he1 : (1/r)*x=x/r := by ring
  have he2 : (1/r)*y=y/r := by ring
  simp only [he1,he2] at hhom1
  simp only [he2] at hhom2
  have hh := extremeValueLog_submodular C hC hxdiv hydiv hxx hyy
  rw [hhom1,hhom2] at hh
  rw [extremeValueLogSection_of_nonneg C y hy x hx.le,
    extremeValueLogSection_of_nonneg C y hy (x/r) hxdiv,
    extremeValueLogSection_of_nonneg C y hy (r*x) (mul_nonneg hr0.le hx.le)]
  have hm := mul_le_mul_of_nonneg_left hh hr0.le
  field_simp [hr0.ne'] at hm
  nlinarith only [hm]

theorem extremeValueLogSection_convex (C : Copula 2) (hC : C.IsExtremeValue)
    (y : ℝ) (hy : 0≤y) : ConvexOn ℝ (Ioi 0) (extremeValueLogSection C y hy) :=
  convexOn_Ioi_of_geometric_jensen (extremeValueLogSection_continuous C hC y hy).continuousOn
    (extremeValueLogSection_geometric C hC y hy)

end Verification
