import Verification.Nelsen22
import Verification.ArchimedeanCDRatio

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n22Prime (p t : ℝ) : ℝ :=
  if t < Real.pi/2 then -p*Real.cos t*(1-Real.sin t)^(p-1) else 0

theorem n22Base_deriv_cutoff : HasDerivAt n22Base 0 (Real.pi/2) := by
  have hl : HasDerivWithinAt n22Base 0 (Iic (Real.pi/2)) (Real.pi/2) := by
    have hh : HasDerivAt (fun t => 1-Real.sin t) 0 (Real.pi/2) := by
      simpa using (Real.hasDerivAt_sin (Real.pi/2)).const_sub 1
    apply hh.hasDerivWithinAt.congr_of_mem
    · intro x hx; exact congrArg (fun t => 1-Real.sin t) (min_eq_left (show x ≤ Real.pi/2 from hx))
    · exact show Real.pi/2 ≤ Real.pi/2 from le_rfl
  have hr : HasDerivWithinAt n22Base 0 (Ici (Real.pi/2)) (Real.pi/2) := by
    apply (hasDerivWithinAt_const (Real.pi/2) (Ici (Real.pi/2)) (0:ℝ)).congr_of_mem
    · intro x hx; simp [n22Base,min_eq_right (show Real.pi/2 ≤ x from hx)]
    · exact show Real.pi/2 ≤ Real.pi/2 from le_rfl
  have hh := hl.union hr
  rwa [Iic_union_Ici,hasDerivWithinAt_univ] at hh

theorem n22Psi_deriv (p : ℝ) (hp : 1 ≤ p) (t : ℝ) :
    HasDerivAt (fun x => n22Base x^p) (n22Prime p t) t := by
  rcases lt_trichotomy t (Real.pi/2) with ht | ht | ht
  · have hb : HasDerivAt n22Base (-Real.cos t) t := by
      apply ((Real.hasDerivAt_sin t).const_sub 1).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds ht] with x hx
      exact congrArg (fun z => 1-Real.sin z) (min_eq_left hx.le)
    convert hb.rpow_const (p := p) (Or.inr hp) using 1
    simp only [n22Prime,ht,ite_true,n22Base,min_eq_left ht.le]
    ring
  · subst t
    convert n22Base_deriv_cutoff.rpow_const (p := p) (Or.inr hp) using 1
    simp [n22Prime]
  · rw [n22Prime,ite_eq_right (not_lt.mpr ht.le)]
    apply (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with x hx
    change Real.pi/2 < x at hx
    simp [n22Base,min_eq_right hx.le,Real.zero_rpow (by linarith : p ≠ 0)]

theorem n22_trig_pos {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi/2)) :
    0 < Real.cos t ∧ 0 < 1-Real.sin t := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,ht.1],ht.2⟩
  have hs : Real.sin t < 1 := by
    have hh := Real.strictMonoOn_sin ⟨by linarith [Real.pi_pos,ht.1],ht.2.le⟩
      ⟨by linarith [Real.pi_pos],le_rfl⟩ ht.2
    simpa only [Real.sin_pi_div_two] using hh
  exact ⟨hc,sub_pos.mpr hs⟩

theorem n22_log_cos_deriv {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi/2)) :
    HasDerivAt (fun x => Real.log (Real.cos x)) (-Real.sin t/Real.cos t) t :=
  (Real.hasDerivAt_cos t).log (n22_trig_pos ht).1.ne'

theorem n22_log_cos_deriv2 {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi/2)) :
    HasDerivAt (fun x => -Real.sin x/Real.cos x) (-1/Real.cos t^2) t := by
  have hc := (n22_trig_pos ht).1
  convert ((Real.hasDerivAt_sin t).neg).div (Real.hasDerivAt_cos t) hc.ne' using 1
  have he := Real.sin_sq_add_cos_sq t
  simp only [Pi.neg_apply]
  field_simp
  nlinarith

theorem n22_log_base_deriv {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi/2)) :
    HasDerivAt (fun x => Real.log (1-Real.sin x)) (-Real.cos t/(1-Real.sin t)) t :=
  ((Real.hasDerivAt_sin t).const_sub 1).log (n22_trig_pos ht).2.ne'

theorem n22_log_base_deriv2 {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi/2)) :
    HasDerivAt (fun x => -Real.cos x/(1-Real.sin x)) (-1/(1-Real.sin t)) t := by
  have hb := (n22_trig_pos ht).2
  convert ((Real.hasDerivAt_cos t).neg).div ((Real.hasDerivAt_sin t).const_sub 1) hb.ne' using 1
  have he := Real.sin_sq_add_cos_sq t
  simp only [Pi.neg_apply]
  field_simp
  nlinarith

theorem n22_log_cos_concave : ConcaveOn ℝ (Ioo 0 (Real.pi/2)) (fun x => Real.log (Real.cos x)) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioo _ _)
  · intro t ht; exact (n22_log_cos_deriv ht).continuousAt.continuousWithinAt
  · intro t ht; exact (n22_log_cos_deriv (interior_subset ht)).hasDerivWithinAt
  · intro t ht; exact (n22_log_cos_deriv2 (interior_subset ht)).hasDerivWithinAt
  · intro t _; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)

theorem n22_log_base_concave : ConcaveOn ℝ (Ioo 0 (Real.pi/2)) (fun x => Real.log (1-Real.sin x)) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioo _ _)
  · intro t ht; exact (n22_log_base_deriv ht).continuousAt.continuousWithinAt
  · intro t ht; exact (n22_log_base_deriv (interior_subset ht)).hasDerivWithinAt
  · intro t ht; exact (n22_log_base_deriv2 (interior_subset ht)).hasDerivWithinAt
  · intro t ht; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (n22_trig_pos (interior_subset ht)).2.le

theorem n22Prime_neg {p t : ℝ} (hp : 1 ≤ p) (ht : t ∈ Ioo 0 (Real.pi/2)) : n22Prime p t < 0 := by
  rw [n22Prime,ite_eq_left ht.2]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (n22_trig_pos ht).1)
    (Real.rpow_pos_of_pos (n22_trig_pos ht).2 _)

theorem n22Prime_log {p t : ℝ} (hp : 1 ≤ p) (ht : t ∈ Ioo 0 (Real.pi/2)) :
    Real.log (-n22Prime p t) = Real.log (Real.cos t)+(p-1)*Real.log (1-Real.sin t)+Real.log p := by
  have hpos : 0 < p := by linarith
  have hc := (n22_trig_pos ht).1
  have hb := (n22_trig_pos ht).2
  rw [n22Prime,ite_eq_left ht.2]
  rw [show -(-p*Real.cos t*(1-Real.sin t)^(p-1)) = p*Real.cos t*(1-Real.sin t)^(p-1) by ring]
  rw [Real.log_mul (mul_pos hpos hc).ne' (Real.rpow_pos_of_pos hb _).ne',
    Real.log_mul hpos.ne' hc.ne',Real.log_rpow hb]
  ring

theorem n22Prime_log_concave {p : ℝ} (hp : 1 ≤ p) :
    ConcaveOn ℝ (Ioo 0 (Real.pi/2)) (fun t => Real.log (-n22Prime p t)) := by
  have hh := (n22_log_cos_concave.add (ConcaveOn.smul (sub_nonneg.mpr hp) n22_log_base_concave)).add_const (Real.log p)
  apply hh.congr
  intro t ht
  simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] using (n22Prime_log hp ht).symm

end Verification
