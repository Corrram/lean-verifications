import Verification.Nelsen21
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open ProbabilityTheory Set Copula

namespace Verification

noncomputable def n21Y (θ t : ℝ) : ℝ := 1-(1-t)^θ
noncomputable def n21Z (θ η t : ℝ) : ℝ := 1-n21Y θ t^(η/θ)
noncomputable def n21Comparison (θ η t : ℝ) : ℝ := 1-n21Z θ η t^η⁻¹
noncomputable def n21ComparisonPrime (θ η t : ℝ) : ℝ :=
  (1-t)^(θ-1)*n21Y θ t^(η/θ-1)*n21Z θ η t^(η⁻¹-1)
noncomputable def n21ComparisonLog (θ η t : ℝ) : ℝ :=
  (θ-1)*Real.log (1-t)+(η/θ-1)*Real.log (n21Y θ t)+(η⁻¹-1)*Real.log (n21Z θ η t)

theorem n21YZ_pos {θ η t : ℝ} (hθ : 0 < θ) (hη : 0 < η) (ht : t ∈ Ioo 0 1) :
    0 < n21Y θ t ∧ 0 < n21Z θ η t := by
  have hx : 0 < 1-t := by linarith [ht.2]
  have hy : 0 < n21Y θ t := sub_pos.mpr (Real.rpow_lt_one hx.le (by linarith [ht.1]) hθ)
  have hy1 : n21Y θ t < 1 := by have hh := Real.rpow_pos_of_pos hx θ; dsimp [n21Y]; linarith
  exact ⟨hy,sub_pos.mpr (Real.rpow_lt_one hy.le hy1 (div_pos hη hθ))⟩

theorem n21Y_deriv {θ t : ℝ} (ht : t < 1) :
    HasDerivAt (n21Y θ) (θ*(1-t)^(θ-1)) t := by
  have hh := (((hasDerivAt_id t).const_sub 1).rpow_const (p := θ) (Or.inl (by linarith : 1-t ≠ 0))).const_sub 1
  convert hh using 1
  · rfl
  · dsimp; ring

theorem n21Z_deriv {θ η t : ℝ} (hθ : 0 < θ) (hη : 0 < η) (ht : t ∈ Ioo 0 1) :
    HasDerivAt (n21Z θ η) (-η*(1-t)^(θ-1)*n21Y θ t^(η/θ-1)) t := by
  have hh := ((n21Y_deriv ht.2).rpow_const (p := η/θ) (Or.inl (n21YZ_pos hθ hη ht).1.ne')).const_sub 1
  convert hh using 1
  · rfl
  · field_simp

theorem n21Comparison_deriv {θ η t : ℝ} (hθ : 0 < θ) (hη : 0 < η) (ht : t ∈ Ioo 0 1) :
    HasDerivAt (n21Comparison θ η) (n21ComparisonPrime θ η t) t := by
  have hh := ((n21Z_deriv hθ hη ht).rpow_const (p := η⁻¹) (Or.inl (n21YZ_pos hθ hη ht).2.ne')).const_sub 1
  convert hh using 1
  · rfl
  · dsimp [n21ComparisonPrime]
    field_simp

theorem n21ComparisonLog_deriv {θ η t : ℝ} (hθ : 0 < θ) (hη : 0 < η) (ht : t ∈ Ioo 0 1) :
    HasDerivAt (n21ComparisonLog θ η)
      ((η-θ-(η-1)*n21Y θ t+(θ-1)*n21Y θ t^(η/θ))/((1-t)*n21Y θ t*n21Z θ η t)) t := by
  have hx : 0 < 1-t := by linarith [ht.2]
  have hy := (n21YZ_pos hθ hη ht).1
  have hz := (n21YZ_pos hθ hη ht).2
  have hh := (((((hasDerivAt_id t).const_sub 1).log hx.ne').const_mul (θ-1)).add
    (((n21Y_deriv ht.2).log hy.ne').const_mul (η/θ-1))).add
      (((n21Z_deriv hθ hη ht).log hz.ne').const_mul (η⁻¹-1))
  convert hh using 1
  · rfl
  · dsimp only [id_eq]
    rw [Real.rpow_sub_one hx.ne',Real.rpow_sub_one hy.ne']
    field_simp
    dsimp [n21Z,n21Y]
    ring

theorem n21ComparisonLog_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) :
    MonotoneOn (n21ComparisonLog θ η) (Ioo 0 1) := by
  have hp : 0 < θ := by linarith
  have hq : 0 < η := by linarith
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1)
  · intro t ht; exact (n21ComparisonLog_deriv hp hq ht).continuousAt.continuousWithinAt
  · intro t ht; exact (n21ComparisonLog_deriv hp hq (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    have ht' := interior_subset ht
    have hy := (n21YZ_pos hp hq ht').1
    have hz := (n21YZ_pos hp hq ht').2
    have hy1 : n21Y θ t ≤ 1 := (n21_inner_mem hp ⟨ht'.1.le,ht'.2.le⟩).2
    have hr : 1 ≤ η/θ := (le_div_iff₀ hp).mpr (by simpa using hθη)
    have hh := one_add_mul_self_le_rpow_one_add (show -1 ≤ n21Y θ t-1 by linarith) hr
    rw [show 1+(n21Y θ t-1) = n21Y θ t by ring] at hh
    have hm := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hθ)
    have he : η-θ-(η-1)*n21Y θ t+(θ-1)*(1+(η/θ)*(n21Y θ t-1)) =
        (η/θ-1)*(1-n21Y θ t) := by field_simp; ring
    have hn := mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hy1)
    apply div_nonneg (by nlinarith) (mul_nonneg (mul_nonneg (by linarith [ht'.2]) hy.le) hz.le)

theorem n21ComparisonPrime_exp {θ η t : ℝ} (hθ : 0 < θ) (hη : 0 < η) (ht : t ∈ Ioo 0 1) :
    n21ComparisonPrime θ η t = Real.exp (n21ComparisonLog θ η t) := by
  have hx : 0 < 1-t := by linarith [ht.2]
  have hy := (n21YZ_pos hθ hη ht).1
  have hz := (n21YZ_pos hθ hη ht).2
  simp only [n21ComparisonPrime,n21ComparisonLog,Real.exp_add,Real.rpow_def_of_pos hx,
    Real.rpow_def_of_pos hy,Real.rpow_def_of_pos hz]
  simp only [mul_comm]

theorem n21Comparison_convex {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) :
    ConvexOn ℝ (Icc 0 1) (n21Comparison θ η) := by
  have hp : 0 < θ := by linarith
  have hq : 0 < η := by linarith
  have hc : Continuous (n21Comparison θ η) := by
    exact continuous_const.sub ((continuous_const.sub ((continuous_const.sub
      ((continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr hp.le))).rpow_const
        (fun _ => Or.inr (div_pos hq hp).le))).rpow_const (fun _ => Or.inr (inv_pos.mpr hq).le))
  apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1) hc.continuousOn
  · intro t ht; exact (n21Comparison_deriv hp hq (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt
  · intro s hs t ht hst
    have hs' : s ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using hs
    have ht' : t ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using ht
    rw [(n21Comparison_deriv hp hq hs').deriv,(n21Comparison_deriv hp hq ht').deriv,
      n21ComparisonPrime_exp hp hq hs',n21ComparisonPrime_exp hp hq ht']
    exact Real.exp_le_exp.mpr (n21ComparisonLog_monotone hθ hθη hs' ht' hst)


theorem n21Comparison_core {θ η t : ℝ} (hθ : 0 < θ) (ht : t ∈ Icc 0 1) :
    n21Comparison θ η t = n21Core η (n21Core θ t) := by
  unfold n21Comparison n21Z n21Core
  rw [sub_sub_cancel,← Real.rpow_mul (n21_inner_mem hθ ht).1]
  rw [show θ⁻¹*η = η/θ by ring]
  rfl

theorem n21Comparison_zero {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) : n21Comparison θ η 0 = 0 := by
  norm_num [n21Comparison,n21Z,n21Y,Real.zero_rpow (div_pos hη hθ).ne']

theorem n21Comparison_superadd {θ η s t : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t ≤ 1) :
    n21Comparison θ η s+n21Comparison θ η t ≤ n21Comparison θ η (s+t) := by
  have hp : 0 < θ := by linarith
  have hq : 0 < η := by linarith
  by_cases hz : s+t = 0
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simp [hs0,ht0,n21Comparison_zero hp hq]
  have hst0 : 0 < s+t := lt_of_le_of_ne (add_nonneg hs ht) (Ne.symm hz)
  have hc := n21Comparison_convex hθ hθη
  have hcomb : t/(s+t)+s/(s+t) = 1 := by field_simp; ring
  have h₁ := hc.2 (show (0:ℝ) ∈ Icc 0 1 by norm_num) ⟨hst0.le,hst⟩
    (div_nonneg ht hst0.le) (div_nonneg hs hst0.le) hcomb
  have h₂ := hc.2 (show (0:ℝ) ∈ Icc 0 1 by norm_num) ⟨hst0.le,hst⟩
    (div_nonneg hs hst0.le) (div_nonneg ht hst0.le) (by linarith)
  simp only [smul_eq_mul,mul_zero,zero_add,n21Comparison_zero hp hq,div_mul_cancel₀ _ hz] at h₁ h₂
  have he : s/(s+t)*n21Comparison θ η (s+t)+t/(s+t)*n21Comparison θ η (s+t) = n21Comparison θ η (s+t) := by
    field_simp
  linarith

end Verification

