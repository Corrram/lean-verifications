import Verification.Nelsen10
import Mathlib.Analysis.Convex.Deriv

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

noncomputable def n10Base (θ v x : ℝ) : ℝ := 1+(1-x^θ)*(1-v^θ)
noncomputable def n10Section (θ v x : ℝ) : ℝ := v*x*(n10Base θ v x)^(-θ⁻¹)

theorem n10Base_ge_one {θ : ℝ} (hθ : 0 ≤ θ) (v : I) {x : ℝ} (hx : x ∈ Icc 0 1) :
    1 ≤ n10Base θ v x := by
  have hu := Real.rpow_le_one hx.1 hx.2 hθ
  have hv := Real.rpow_le_one v.property.1 v.property.2 hθ
  dsimp [n10Base]
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)]

theorem n10Section_deriv {θ : ℝ} (hθ : 0 < θ) (v : I) {x : ℝ}
    (hx : x ∈ Ioo 0 1) :
    HasDerivAt (n10Section θ v)
      ((v:ℝ)*(2-(v:ℝ)^θ)*(n10Base θ v x)^(-θ⁻¹-1)) x := by
  have hd : 0 < n10Base θ v x := lt_of_lt_of_le zero_lt_one
    (n10Base_ge_one hθ.le v ⟨hx.1.le,hx.2.le⟩)
  have hxpow := (hasDerivAt_id x).rpow_const (p := θ) (Or.inl hx.1.ne')
  have hb := ((hxpow.const_sub 1).mul_const (1-(v:ℝ)^θ)).const_add 1
  have hp := hb.rpow_const (p := -θ⁻¹) (Or.inl hd.ne')
  convert ((hasDerivAt_id x).const_mul (v:ℝ)).mul hp using 1
  · rfl
  · dsimp
    simp only [one_mul, mul_one]
    change (v:ℝ)*(2-(v:ℝ)^θ)*(n10Base θ v x)^(-θ⁻¹-1) =
      (v:ℝ)*(n10Base θ v x)^(-θ⁻¹) +
        (v:ℝ)*x*(-(θ*x^(θ-1))*(1-(v:ℝ)^θ)*(-θ⁻¹)*(n10Base θ v x)^(-θ⁻¹-1))
    rw [Real.rpow_sub_one hx.1.ne' θ, Real.rpow_sub_one hd.ne' (-θ⁻¹)]
    field_simp [hx.1.ne', hd.ne', hθ.ne']
    unfold n10Base
    ring

theorem n10Section_convex {θ : ℝ} (hθ : 0 < θ) (v : I) :
    ConvexOn ℝ (Icc 0 1) (n10Section θ v) := by
  have hc : ContinuousOn (n10Section θ v) (Icc 0 1) := by
    unfold n10Section
    apply ContinuousOn.mul
    · fun_prop
    · apply ContinuousOn.rpow_const
      · unfold n10Base
        exact (continuous_const.add
          ((continuous_const.sub (Real.continuous_rpow_const hθ.le)).mul continuous_const)).continuousOn
      · intro x hx
        exact Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (n10Base_ge_one hθ.le v hx)))
  apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1) hc
  · intro x hx
    exact (n10Section_deriv hθ v (by simpa only [interior_Icc] using hx)).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    have hx' : x ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using hx
    have hy' : y ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using hy
    rw [(n10Section_deriv hθ v hx').deriv, (n10Section_deriv hθ v hy').deriv]
    have hv := Real.rpow_le_one v.property.1 v.property.2 hθ.le
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg v.property.1 (by linarith))
    apply Real.rpow_le_rpow_of_nonpos
    · exact lt_of_lt_of_le zero_lt_one (n10Base_ge_one hθ.le v ⟨hy'.1.le,hy'.2.le⟩)
    · have hm := Real.rpow_le_rpow hx'.1.le hxy hθ.le
      unfold n10Base
      nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hv)]
    · have hp := inv_pos.mpr hθ
      linarith

theorem nelsen10_section (θ u v : I) (hθ : 0 < (θ:ℝ)) :
    (nelsen10 θ).cdf ![u,v] = n10Section θ v u := by
  rw [nelsen10_cdf θ u v hθ]
  unfold n10Section n10Base
  have hb : 0 ≤ 1+(1-(u:ℝ)^(θ:ℝ))*(1-(v:ℝ)^(θ:ℝ)) :=
    le_trans zero_le_one (n10Base_ge_one hθ.le v u.property)
  rw [Real.rpow_neg hb]
  ring

theorem nelsen10_isSD (θ : I) : (nelsen10 θ).IsSD := by
  by_cases hz : (θ:ℝ) = 0
  · have he : θ = 0 := Subtype.ext hz
    rw [he, nelsen10_zero]
    exact isCD_independence.isSD
  have hp : 0 < (θ:ℝ) := lt_of_le_of_ne θ.property.1 (Ne.symm hz)
  intro a b c v hab hbc
  rcases eq_or_lt_of_le hab with he | hab'
  · subst b; simp
  rcases eq_or_lt_of_le hbc with he | hbc'
  · subst c; simp
  have hs := (n10Section_convex hp v).secant_mono_aux1 a.property c.property
    (show (a:ℝ) < b from hab') (show (b:ℝ) < c from hbc')
  simp only [nelsen10_section θ _ _ hp]
  nlinarith [hs]

theorem nelsen10_isCD (θ : I) : (nelsen10 θ).IsCD := by
  by_cases hz : (θ:ℝ) = 0
  · have he : θ = 0 := Subtype.ext hz
    rw [he, nelsen10_zero]
    exact isCD_independence
  have ha : (nelsen10 θ).IsArchimedean := by
    simp only [nelsen10, hz, dite_false, nelsen10Positive]
    exact BivariateGenerator.isArchimedean _
  exact ha.isCD_iff.mpr (nelsen10_isSD θ)

end Verification
