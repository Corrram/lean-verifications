import Verification.GalambosConstruction

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem galambos_kernel_bound (δ : ℝ) (hδ : 0<δ) (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    galambosTailKernel δ x y ≤ max x y*(2:ℝ)^(-1/δ) := by
  have hm : 0<max x y := lt_of_lt_of_le hx (le_max_left _ _)
  have h1 := Real.rpow_le_rpow_of_nonpos hx (le_max_left x y) (neg_nonpos.mpr hδ.le)
  have h2 := Real.rpow_le_rpow_of_nonpos hy (le_max_right x y) (neg_nonpos.mpr hδ.le)
  have hh : 2*(max x y)^(-δ)≤x^(-δ)+y^(-δ) := by linarith
  have hp : 0<2*(max x y)^(-δ) := mul_pos (by norm_num) (Real.rpow_pos_of_pos hm _)
  have h := Real.rpow_le_rpow_of_nonpos hp hh (div_nonpos_of_nonpos_of_nonneg (by norm_num : (-1:ℝ)≤0) hδ.le)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hm.le _),
    ← Real.rpow_mul hm.le,show (-δ)*(-1/δ)=1 by field_simp,Real.rpow_one,mul_comm] at h
  exact h

theorem galambos_kernel_limit_zero {ι : Type*} {l : Filter ι} (δ : ι→ℝ)
    (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0)) (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    Tendsto (fun i => galambosTailKernel (δ i) x y) l (nhds 0) := by
  have hd' : Tendsto δ l (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hd,Eventually.of_forall hδ⟩
  have hi := tendsto_neg_atTop_atBot.comp (tendsto_inv_nhdsGT_zero.comp hd')
  have hp := (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp hi
  have hb := hp.const_mul (max x y)
  simp only [Function.comp_def,mul_zero] at hb
  apply squeeze_zero (fun i => Real.rpow_nonneg
    (add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hy.le _)) _) _ hb
  intro i
  simpa only [galambosTailKernel,neg_div,one_div] using galambos_kernel_bound (δ i) (hδ i) x y hx hy

end Verification
