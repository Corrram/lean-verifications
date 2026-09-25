import Verification.NormalCDFDerivative
import Verification.HuslerReissFormula
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open ProbabilityTheory MeasureTheory Real Set

namespace Verification

noncomputable def huslerReissExponent (δ x y : ℝ) : ℝ :=
  x*ProbabilityTheory.cdf (gaussianReal 0 1) (1/δ+δ/2*Real.log (x/y))+
  y*ProbabilityTheory.cdf (gaussianReal 0 1) (1/δ+δ/2*Real.log (y/x))

theorem huslerReiss_density_balance (δ x y : ℝ) (hδ : 0<δ) (hx : 0<x) (hy : 0<y) :
    x*gaussianPDFReal 0 1 (1/δ+δ/2*Real.log (x/y))=
      y*gaussianPDFReal 0 1 (1/δ+δ/2*Real.log (y/x)) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [mul_left_comm x,mul_left_comm y]
  congr 1
  nth_rw 1 [← Real.exp_log hx]
  nth_rw 2 [← Real.exp_log hy]
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  rw [Real.log_div hx.ne' hy.ne',Real.log_div hy.ne' hx.ne']
  field_simp
  ring

theorem huslerReissExponent_hasDerivAt (δ x y : ℝ) (hδ : 0<δ) (hx : 0<x) (hy : 0<y) :
    HasDerivAt (fun d => huslerReissExponent d x y)
      (-2/δ^2*(x*gaussianPDFReal 0 1 (1/δ+δ/2*Real.log (x/y)))) δ := by
  have hd := hasDerivAt_id δ
  have harg (a : ℝ) : HasDerivAt (fun d : ℝ => 1/d+d/2*a) (-1/δ^2+a/2) δ := by
    convert ((hd.inv hδ.ne').add ((hd.div_const 2).mul_const a)) using 1
    · funext d
      simp only [Pi.add_apply,Pi.inv_apply,id_eq,one_div]
    · simp only [id_eq,one_div]
      ring
  have h := ((standardNormalCDF_hasDerivAt _).comp δ (harg (Real.log (x/y)))).const_mul x
  have k := ((standardNormalCDF_hasDerivAt _).comp δ (harg (Real.log (y/x)))).const_mul y
  convert h.add k using 1
  · rfl
  · have hb := huslerReiss_density_balance δ x y hδ hx hy
    rw [← mul_assoc x,← mul_assoc y,← hb]
    rw [Real.log_div hx.ne' hy.ne',Real.log_div hy.ne' hx.ne']
    ring

theorem huslerReissExponent_antitone (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    AntitoneOn (fun δ => huslerReissExponent δ x y) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro δ hδ; exact (huslerReissExponent_hasDerivAt δ x y hδ hx hy).continuousAt.continuousWithinAt
  · intro δ hδ
    exact (huslerReissExponent_hasDerivAt δ x y (interior_subset hδ) hx hy).differentiableAt.differentiableWithinAt
  · intro δ hδ
    rw [(huslerReissExponent_hasDerivAt δ x y (interior_subset hδ) hx hy).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg hx.le (gaussianPDFReal_nonneg _ _ _))

end Verification
