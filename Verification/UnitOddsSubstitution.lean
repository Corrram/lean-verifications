import Verification.ExponentialIntegral

open MeasureTheory Set

namespace Verification

theorem unitOdds_deriv {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (fun x : ℝ => x/(1-x)) ((1-t)^2)⁻¹ t := by
  have hd := (hasDerivAt_id t).div ((hasDerivAt_id t).const_sub 1)
    (sub_pos.mpr ht.2).ne'
  convert hd using 1
  · rfl
  · dsimp only [id_eq]
    field_simp
    ring

theorem integral_unit_odds (f : ℝ → ℝ) :
    (∫ s in Ioi (0:ℝ), f s)=
      ∫ t in (0:ℝ)..1, ((1-t)^2)⁻¹*f (t/(1-t)) := by
  have hi : (fun t : ℝ => t/(1-t)) '' Ioo 0 1=Ioi 0 := by
    ext s
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact div_pos ht.1 (sub_pos.mpr ht.2)
    · intro hs
      have hs' : 0<s := hs
      have h1 : 0<1+s := by linarith
      refine ⟨s/(1+s), ⟨div_pos hs' h1, (div_lt_one h1).mpr (by linarith)⟩, ?_⟩
      field_simp
      ring
  have hj : InjOn (fun t : ℝ => t/(1-t)) (Ioo 0 1) := by
    intro a ha b hb he
    have he' := (div_eq_div_iff (sub_pos.mpr ha.2).ne' (sub_pos.mpr hb.2).ne').mp he
    nlinarith
  have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t ht => (unitOdds_deriv ht).hasDerivWithinAt) hj f
  rw [hi] at hh
  rw [intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo]
  convert hh using 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _
  simp only [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (1-t))),smul_eq_mul]

end Verification
