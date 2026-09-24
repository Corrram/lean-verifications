import Verification.Plackett
import Verification.MarshallOlkinOrder
import Mathlib.Analysis.Convex.Deriv

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem plackettP_deriv_first {θ u v : ℝ} (hD : 0 < plackettD θ u v) :
    HasDerivAt (fun x => plackettP θ x v)
      (-2*θ*(θ-1)*v*(1-v)/(Real.sqrt (plackettD θ u v))^3) u := by
  have hA : HasDerivAt (fun x => plackettA θ x v) (θ-1) u := by
    convert (((hasDerivAt_id u).add_const v).const_mul (θ-1)).const_add 1 using 1 <;> simp [plackettA]
  have hD' : HasDerivAt (fun x => plackettD θ x v)
      (2*plackettA θ u v*(θ-1)-4*θ*(θ-1)*v) u := by
    convert (hA.pow 2).sub ((hasDerivAt_id u).const_mul (4*θ*(θ-1)*v)) using 1
    · funext x; dsimp [plackettD,plackettA]; ring
    · ring
  have hh := (((hA.sub_const (2*θ*v)).div (hD'.sqrt hD.ne')
    (Real.sqrt_pos.mpr hD).ne').const_sub 1).div_const 2
  convert hh using 1
  · rfl
  · have hs := Real.sq_sqrt hD.le
    field_simp [(Real.sqrt_pos.mpr hD).ne']
    rw [hs]
    dsimp [plackettD,plackettA]
    ring

theorem plackett_transpose (θ : ℝ) (hθ : 0 < θ) : (plackett θ hθ).transpose = plackett θ hθ := by
  by_cases he : θ=1
  · subst θ; rw [plackett_one]; exact isExchangeable_independence
  apply ext_cdf_two
  intro u v
  rw [cdf_transpose,plackett_cdf hθ he,plackett_cdf hθ he]
  exact plackettF_symm θ v u

theorem plackett_isCI {θ : ℝ} (hθ : 0 < θ) (hθ1 : 1 ≤ θ) : (plackett θ hθ).IsCI := by
  by_cases he : θ=1
  · subst θ; rw [plackett_one]; exact isCI_independence
  have hs : (plackett θ hθ).IsSI := by
    apply isSI_of_concave_formula _ (fun v x => plackettF θ x v)
    · intro v
      apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
      · intro u hu; exact (plackettF_deriv he (plackettD_pos hθ hu v.property)).continuousAt.continuousWithinAt
      · intro u hu; exact (plackettF_deriv he (plackettD_pos hθ (interior_subset hu) v.property)).hasDerivWithinAt
      · intro u hu; exact (plackettP_deriv_first (plackettD_pos hθ (interior_subset hu) v.property)).hasDerivWithinAt
      · intro u _
        apply div_nonpos_of_nonpos_of_nonneg _ (pow_nonneg (Real.sqrt_nonneg _) _)
        have hh : 0 ≤ 2*θ*(θ-1)*(v:ℝ)*(1-(v:ℝ)) :=
          mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθ.le)
            (sub_nonneg.mpr hθ1)) v.property.1) (sub_nonneg.mpr v.property.2)
        nlinarith
    · intro u v; exact plackett_cdf hθ he u v
  exact ⟨hs,by rw [plackett_transpose]; exact hs⟩

theorem plackett_isCD {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) : (plackett θ hθ).IsCD := by
  by_cases he : θ=1
  · subst θ; rw [plackett_one]; exact isCD_independence
  have hc (v : I) : ConvexOn ℝ (Icc 0 1) (fun x => plackettF θ x v) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
    · intro u hu; exact (plackettF_deriv he (plackettD_pos hθ hu v.property)).continuousAt.continuousWithinAt
    · intro u hu; exact (plackettF_deriv he (plackettD_pos hθ (interior_subset hu) v.property)).hasDerivWithinAt
    · intro u hu; exact (plackettP_deriv_first (plackettD_pos hθ (interior_subset hu) v.property)).hasDerivWithinAt
    · intro u _
      apply div_nonneg _ (pow_nonneg (Real.sqrt_nonneg _) _)
      exact mul_nonneg (mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by nlinarith) (sub_nonpos.mpr hθ1))
        v.property.1) (sub_nonneg.mpr v.property.2)
  have hs : (plackett θ hθ).IsSD := by
    intro a b c v hab hbc
    rcases eq_or_lt_of_le hab with rfl | hab
    · simp
    rcases eq_or_lt_of_le hbc with rfl | hbc
    · simp
    have hh := (hc v).secant_mono_aux1 a.property c.property
      (show (a:ℝ)<b from hab) (show (b:ℝ)<c from hbc)
    rw [plackett_cdf hθ he,plackett_cdf hθ he,plackett_cdf hθ he]
    change _ ≤ _
    change (b-a)*plackettF θ c v+(c-b)*plackettF θ a v ≥ (c-a)*plackettF θ b v
    nlinarith only [hh]
  exact ⟨hs,by rw [plackett_transpose]; exact hs⟩

theorem plackett_midpoint {θ : ℝ} (hθ : 0 < θ) :
    (plackett θ hθ).cdf ![unitHalf,unitHalf] = Real.sqrt θ/(2*(Real.sqrt θ+1)) := by
  by_cases he : θ=1
  · subst θ; rw [plackett_one]; norm_num [cdf_independence,Fin.prod_univ_two,unitHalf]
  rw [plackett_cdf hθ he]
  dsimp [unitHalf]
  have hd : (1+(θ-1)*((1:ℝ)/2+1/2))^2-4*θ*(θ-1)*(1/2)*(1/2) = θ := by ring
  change (1+(θ-1)*((1:ℝ)/2+1/2)-Real.sqrt _)/(2*(θ-1)) = _
  rw [hd]
  have hs := Real.sq_sqrt hθ.le
  have hn : Real.sqrt θ+1 ≠ 0 := by linarith [Real.sqrt_nonneg θ]
  field_simp [sub_ne_zero.mpr he,hn]
  nlinarith [hs]

theorem plackett_pqd_iff {θ : ℝ} (hθ : 0 < θ) : (plackett θ hθ).IsPQD ↔ 1 ≤ θ := by
  constructor
  · intro h
    have hh := h unitHalf unitHalf
    rw [plackett_midpoint hθ] at hh
    change (1:ℝ)/2*(1/2) ≤ Real.sqrt θ/(2*(Real.sqrt θ+1)) at hh
    have hn : 0 < 2*(Real.sqrt θ+1) := by positivity
    have hi := (le_div_iff₀ hn).mp hh
    nlinarith [Real.sq_sqrt hθ.le,Real.sqrt_nonneg θ]
  · intro h; exact (plackett_isCI hθ h).isPQD

theorem plackett_nqd_iff {θ : ℝ} (hθ : 0 < θ) : (plackett θ hθ).IsNQD ↔ θ ≤ 1 := by
  constructor
  · intro h
    have hh := h unitHalf unitHalf
    rw [plackett_midpoint hθ] at hh
    change Real.sqrt θ/(2*(Real.sqrt θ+1)) ≤ (1:ℝ)/2*(1/2) at hh
    have hn : 0 < 2*(Real.sqrt θ+1) := by positivity
    have hi := (div_le_iff₀ hn).mp hh
    nlinarith [Real.sq_sqrt hθ.le,Real.sqrt_nonneg θ]
  · intro h; exact (plackett_isCD hθ h).isNQD

theorem plackett_ci_iff {θ : ℝ} (hθ : 0 < θ) : (plackett θ hθ).IsCI ↔ 1 ≤ θ :=
  ⟨fun h => (plackett_pqd_iff hθ).mp h.isPQD,plackett_isCI hθ⟩

theorem plackett_cd_iff {θ : ℝ} (hθ : 0 < θ) : (plackett θ hθ).IsCD ↔ θ ≤ 1 :=
  ⟨fun h => (plackett_nqd_iff hθ).mp h.isNQD,plackett_isCD hθ⟩

end Verification
