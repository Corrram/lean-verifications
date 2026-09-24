import Verification.Nelsen13

open Set

namespace Verification

noncomputable def n13A (u : ℝ) : ℝ := 1-Real.log u
noncomputable def n13B (θ k u : ℝ) : ℝ := (n13A u)^θ+k
noncomputable def n13Section (θ k u : ℝ) : ℝ := Real.exp (1-(n13B θ k u)^θ⁻¹)
noncomputable def n13Factor (θ k u : ℝ) : ℝ :=
  (n13A u)^θ / n13A u * (n13B θ k u)^θ⁻¹ / n13B θ k u
noncomputable def n13SectionDeriv (θ k u : ℝ) : ℝ :=
  n13Section θ k u / u * n13Factor θ k u

theorem n13Section_deriv {θ k u : ℝ} (hθ : θ ≠ 0) (hu : 0 < u)
    (ha : 0 < n13A u) (hb : 0 < n13B θ k u) :
    HasDerivAt (n13Section θ k) (n13SectionDeriv θ k u) u := by
  have hA := (Real.hasDerivAt_log hu.ne').const_sub 1
  have hP := hA.rpow_const (p := θ) (Or.inl ha.ne')
  have hB := hP.add_const k
  have hR := hB.rpow_const (p := θ⁻¹) (Or.inl hb.ne')
  have hh := (hR.const_sub 1).exp
  convert hh using 1
  · rfl
  · change n13SectionDeriv θ k u =
      n13Section θ k u * -((-u⁻¹*θ*(n13A u)^(θ-1))*θ⁻¹*(n13B θ k u)^(θ⁻¹-1))
    rw [Real.rpow_sub_one ha.ne', Real.rpow_sub_one hb.ne']
    dsimp [n13SectionDeriv, n13Factor]
    field_simp

theorem n13Section_deriv2 {θ k u : ℝ} (hθ : θ ≠ 0) (hu : 0 < u)
    (ha : 0 < n13A u) (hb : 0 < n13B θ k u) :
    HasDerivAt (n13SectionDeriv θ k)
      (n13SectionDeriv θ k u / u *
        (n13Factor θ k u-1-(θ-1)/n13A u+(θ-1)*(n13A u)^θ/n13A u/n13B θ k u)) u := by
  have hA := (Real.hasDerivAt_log hu.ne').const_sub 1
  have hP := hA.rpow_const (p := θ) (Or.inl ha.ne')
  have hB := hP.add_const k
  have hR := hB.rpow_const (p := θ⁻¹) (Or.inl hb.ne')
  have hF := (((hP.div hA ha.ne').mul hR).div hB hb.ne')
  have hh := ((n13Section_deriv hθ hu ha hb).div (hasDerivAt_id u) hu.ne').mul hF
  convert hh using 1
  · rfl
  · change n13SectionDeriv θ k u / u *
        (n13Factor θ k u-1-(θ-1)/n13A u+(θ-1)*(n13A u)^θ/n13A u/n13B θ k u) =
      (n13SectionDeriv θ k u*u-n13Section θ k u*1)/u^2*n13Factor θ k u +
      n13Section θ k u/u *
        ((((-u⁻¹*θ*(n13A u)^(θ-1)*n13A u-(n13A u)^θ*(-u⁻¹))/(n13A u)^2*
          (n13B θ k u)^θ⁻¹+(n13A u)^θ/n13A u*
            ((-u⁻¹*θ*(n13A u)^(θ-1))*θ⁻¹*(n13B θ k u)^(θ⁻¹-1)))*n13B θ k u-
          ((n13A u)^θ/n13A u*(n13B θ k u)^θ⁻¹)*(-u⁻¹*θ*(n13A u)^(θ-1)))/(n13B θ k u)^2)
    rw [Real.rpow_sub_one ha.ne', Real.rpow_sub_one hb.ne']
    dsimp [n13SectionDeriv, n13Factor]
    field_simp
    ring

theorem n13Factor_le_one {θ k u : ℝ} (hθ : 1 ≤ θ) (hk : 0 ≤ k)
    (ha : 0 < n13A u) : n13Factor θ k u ≤ 1 := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  have hP : 0 < (n13A u)^θ := Real.rpow_pos_of_pos ha _
  have hb : 0 < n13B θ k u := by unfold n13B; positivity
  have he : θ⁻¹-1 ≤ 0 := by have hh := (inv_le_one₀ hp).mpr hθ; linarith
  have hh := Real.rpow_le_rpow_of_nonpos hP
    (show (n13A u)^θ ≤ n13B θ k u by unfold n13B; linarith) he
  rw [← Real.rpow_mul ha.le] at hh
  have hexp : θ*(θ⁻¹-1) = 1-θ := by field_simp
  rw [hexp] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg ha.le (θ-1))
  rw [← Real.rpow_add ha, sub_add_sub_cancel, sub_self, Real.rpow_zero] at hm
  simpa only [n13Factor, Real.rpow_sub_one ha.ne' θ, Real.rpow_sub_one hb.ne' θ⁻¹,
    mul_div_assoc] using hm

theorem n13Section_deriv2_nonpos {θ k u : ℝ} (hθ : 1 ≤ θ) (hk : 0 ≤ k)
    (hu : 0 < u) (ha : 0 < n13A u) :
    n13SectionDeriv θ k u / u *
      (n13Factor θ k u-1-(θ-1)/n13A u+(θ-1)*(n13A u)^θ/n13A u/n13B θ k u) ≤ 0 := by
  have hb : 0 < n13B θ k u := by unfold n13B; positivity
  have hf := n13Factor_le_one hθ hk ha
  have hq : (n13A u)^θ/n13B θ k u ≤ 1 := (div_le_one hb).mpr (by unfold n13B; linarith)
  have hm := mul_le_mul_of_nonneg_left hq (div_nonneg (sub_nonneg.mpr hθ) ha.le)
  have hn : n13Factor θ k u-1-(θ-1)/n13A u+
      (θ-1)*(n13A u)^θ/n13A u/n13B θ k u ≤ 0 := by
    have he : (θ-1)/n13A u*((n13A u)^θ/n13B θ k u) =
        (θ-1)*(n13A u)^θ/n13A u/n13B θ k u := by ring
    rw [he] at hm
    nlinarith
  apply mul_nonpos_of_nonneg_of_nonpos _ hn
  dsimp [n13SectionDeriv, n13Section, n13Factor]
  positivity

end Verification
