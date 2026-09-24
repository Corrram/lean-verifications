import Verification.Nelsen17Conditional
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Copula.Dependence.Singular
import Mathlib.Analysis.Calculus.Deriv.Slope

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n17RealCDF (a u v : ℝ) : ℝ :=
  (1+((1+u)^a-1)*((1+v)^a-1)/n17A a)^a⁻¹-1

theorem n17RealCDF_eq (θ : ℝ) (hθ : θ ≠ 0) (u v : I) :
    n17RealCDF (-θ) u v = (nelsen17 θ hθ).cdf ![u,v] := by
  rw [nelsen17_cdf_full]
  simp only [n17RealCDF, n17A, inv_neg]

theorem n17RealCDF_deriv_zero {a : ℝ} (ha : a ≠ 0) (v : ℝ) :
    HasDerivAt (fun u => n17RealCDF a u v) (n17Ratio a v) 0 := by
  have hh := ((((((hasDerivAt_id (0:ℝ)).const_add 1).rpow_const (p := a)
    (Or.inl (by norm_num))).sub_const 1).mul_const ((1+v)^a-1)).div_const (n17A a)).const_add 1
  have hd := (hh.rpow_const (p := a⁻¹) (Or.inl (by simp))).sub_const 1
  convert hd using 1
  · rfl
  · dsimp only [id_eq]
    simp only [add_zero, Real.one_rpow, sub_self, zero_mul, zero_div, mul_one, one_mul]
    dsimp [n17Ratio]
    field_simp

theorem n17Ratio_ge_of_pqd (θ : ℝ) (hθ : θ ≠ 0)
    (hC : (nelsen17 θ hθ).IsPQD) (v : I) : (v:ℝ) ≤ n17Ratio (-θ) v := by
  have hd := (n17RealCDF_deriv_zero (neg_ne_zero.mpr hθ) (v:ℝ)).tendsto_slope_zero_right
  have hl : Tendsto (fun t => n17RealCDF (-θ) t v/t) (𝓝[>] (0:ℝ)) (𝓝 (n17Ratio (-θ) v)) := by
    simpa [n17RealCDF, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))] with t ht ht1
  have hi : t ∈ Icc (0:ℝ) 1 := ⟨ht.le,ht1.le⟩
  have hh := hC ⟨t,hi⟩ v
  rw [← n17RealCDF_eq] at hh
  exact (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hh)

theorem n17Ratio_le_of_nqd (θ : ℝ) (hθ : θ ≠ 0)
    (hC : (nelsen17 θ hθ).IsNQD) (v : I) : n17Ratio (-θ) v ≤ (v:ℝ) := by
  have hd := (n17RealCDF_deriv_zero (neg_ne_zero.mpr hθ) (v:ℝ)).tendsto_slope_zero_right
  have hl : Tendsto (fun t => n17RealCDF (-θ) t v/t) (𝓝[>] (0:ℝ)) (𝓝 (n17Ratio (-θ) v)) := by
    simpa [n17RealCDF, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))] with t ht ht1
  have hi : t ∈ Icc (0:ℝ) 1 := ⟨ht.le,ht1.le⟩
  have hh := hC ⟨t,hi⟩ v
  rw [← n17RealCDF_eq] at hh
  exact (div_le_iff₀ ht).mpr (by simpa only [mul_comm] using hh)

theorem n17Ratio_half_lt {a : ℝ} (ha : 1 < a) : n17Ratio a (1/2) < 1/2 := by
  have hh := (strictConvexOn_rpow ha).2 (show (1:ℝ) ∈ Ici 0 by norm_num)
    (show (2:ℝ) ∈ Ici 0 by norm_num) (by norm_num : (1:ℝ) ≠ 2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  norm_num only [smul_eq_mul, Real.one_rpow] at hh
  apply (div_lt_iff₀ (n17A_pos (by linarith : 0 < a))).mpr
  dsimp [n17A]
  norm_num at hh ⊢
  linarith

theorem nelsen17_isCI_iff (θ : ℝ) (hθ : θ ≠ 0) : (nelsen17 θ hθ).IsCI ↔ -1 ≤ θ := by
  constructor
  · intro hC
    by_contra hn
    have hh := n17Ratio_ge_of_pqd θ hθ hC.isPQD (⟨1/2,by norm_num⟩:I)
    have hl := n17Ratio_half_lt (a := -θ) (by linarith : 1 < -θ)
    exact (not_lt_of_ge hh) hl
  · exact nelsen17_isCI θ hθ

theorem n17Ratio_half_gt {a : ℝ} (ha : a ≠ 0) (ha1 : a < 1) : 1/2 < n17Ratio a (1/2) := by
  rcases lt_or_gt_of_ne ha with hn | hp
  · have hc : StrictConvexOn ℝ (Ioi 0) (fun x : ℝ => x^a) := by
      apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
      · intro x hx
        exact ((hasDerivAt_id x).rpow_const (p := a) (Or.inl (ne_of_gt hx))).continuousAt.continuousWithinAt
      · intro x hx y hy hxy
        have hx0 : 0 < x := interior_subset hx
        have hy0 : 0 < y := interior_subset hy
        have hd (z : ℝ) (hz : 0 < z) : HasDerivAt (fun x : ℝ => x^a) (a*z^(a-1)) z := by
          simpa using (hasDerivAt_id z).rpow_const (p := a) (Or.inl hz.ne')
        rw [(hd x hx0).deriv, (hd y hy0).deriv]
        exact mul_lt_mul_of_neg_left (Real.rpow_lt_rpow_of_neg hx0 hxy (by linarith : a-1 < 0)) hn
    have hh := hc.2 (show (1:ℝ) ∈ Ioi 0 by norm_num)
      (show (2:ℝ) ∈ Ioi 0 by norm_num) (by norm_num : (1:ℝ) ≠ 2)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    apply (lt_div_iff_of_neg (n17A_neg hn)).mpr
    dsimp [n17A]
    norm_num [smul_eq_mul] at hh ⊢
    linarith
  · have hh := (Real.strictConcaveOn_rpow hp ha1).2 (show (1:ℝ) ∈ Ici 0 by norm_num)
      (show (2:ℝ) ∈ Ici 0 by norm_num) (by norm_num : (1:ℝ) ≠ 2)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    apply (lt_div_iff₀ (n17A_pos hp)).mpr
    dsimp [n17A]
    norm_num [smul_eq_mul] at hh ⊢
    linarith

theorem nelsen17_isCD_iff (θ : ℝ) (hθ : θ ≠ 0) : (nelsen17 θ hθ).IsCD ↔ θ ≤ -1 := by
  constructor
  · intro hC
    by_contra hn
    have hh := n17Ratio_le_of_nqd θ hθ hC.isNQD (⟨1/2,by norm_num⟩:I)
    have hl := n17Ratio_half_gt (neg_ne_zero.mpr hθ) (by linarith : -θ < 1)
    exact (not_lt_of_ge hh) hl
  · exact nelsen17_isCD θ hθ

theorem nelsen17_isPQD_iff (θ : ℝ) (hθ : θ ≠ 0) : (nelsen17 θ hθ).IsPQD ↔ -1 ≤ θ := by
  constructor
  · intro hC
    by_contra hn
    have hh := n17Ratio_ge_of_pqd θ hθ hC (⟨1/2,by norm_num⟩:I)
    have hl := n17Ratio_half_lt (a := -θ) (by linarith : 1 < -θ)
    exact (not_lt_of_ge hh) hl
  · intro h; exact (nelsen17_isCI θ hθ h).isPQD

theorem nelsen17_isNQD_iff (θ : ℝ) (hθ : θ ≠ 0) : (nelsen17 θ hθ).IsNQD ↔ θ ≤ -1 := by
  constructor
  · intro hC
    by_contra hn
    have hh := n17Ratio_le_of_nqd θ hθ hC (⟨1/2,by norm_num⟩:I)
    have hl := n17Ratio_half_gt (neg_ne_zero.mpr hθ) (by linarith : -θ < 1)
    exact (not_lt_of_ge hh) hl
  · intro h; exact (nelsen17_isCD θ hθ h).isNQD

end Verification
