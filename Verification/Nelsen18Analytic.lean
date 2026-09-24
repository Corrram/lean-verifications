import Verification.Nelsen19

open ProbabilityTheory Set Filter Copula
open scoped Topology

namespace Verification

noncomputable def n18Core (θ t : ℝ) : ℝ := 1+θ/Real.log t
noncomputable def n18CorePrime (θ t : ℝ) : ℝ := -θ/(t*Real.log t^2)

theorem n18_log_bound {θ t : ℝ} (ht : 0 < t) (hb : t ≤ Real.exp (-θ)) :
    Real.log t ≤ -θ := by
  simpa using Real.log_le_log ht hb

theorem n18Core_deriv {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t)
    (hb : t ≤ Real.exp (-θ)) : HasDerivAt (n18Core θ) (n18CorePrime θ t) t := by
  have hl : Real.log t ≠ 0 := ne_of_lt (lt_of_le_of_lt (n18_log_bound ht hb) (neg_neg_of_pos hθ))
  have hh := ((hasDerivAt_const t θ).div ((hasDerivAt_id t).log ht.ne') hl).const_add 1
  convert hh using 1
  · rfl
  · dsimp [n18CorePrime]; field_simp; ring

theorem n18Core_deriv2 {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t)
    (hb : t ≤ Real.exp (-θ)) :
    HasDerivAt (n18CorePrime θ) (θ*(Real.log t+2)/(t^2*Real.log t^3)) t := by
  have hl : Real.log t ≠ 0 := ne_of_lt (lt_of_le_of_lt (n18_log_bound ht hb) (neg_neg_of_pos hθ))
  have hh := (hasDerivAt_const t (-θ)).div
    ((hasDerivAt_id t).mul (((hasDerivAt_id t).log ht.ne').pow 2))
    (mul_ne_zero ht.ne' (pow_ne_zero _ hl))
  convert hh using 1
  · rfl
  · dsimp; field_simp; ring

theorem n18Core_continuousAt_zero (θ : ℝ) : ContinuousAt (n18Core θ) 0 := by
  rw [continuousAt_iff_punctured_nhds]
  have hh := (tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsNE_zero).const_mul θ
  change Tendsto (fun t => 1+θ/Real.log t) (𝓝[≠] 0) (𝓝 (1+θ/Real.log 0))
  simpa [n18Core,div_eq_mul_inv] using hh.const_add 1

theorem n18Core_continuousOn {θ : ℝ} (hθ : 0 < θ) :
    ContinuousOn (n18Core θ) (Icc 0 (Real.exp (-θ))) := by
  intro t ht
  by_cases hz : t = 0
  · subst t; exact (n18Core_continuousAt_zero θ).continuousWithinAt
  · exact (n18Core_deriv hθ (lt_of_le_of_ne ht.1 (Ne.symm hz)) ht.2).continuousAt.continuousWithinAt

theorem n18Core_antitone {θ : ℝ} (hθ : 0 < θ) :
    AntitoneOn (n18Core θ) (Icc 0 (Real.exp (-θ))) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
  · exact n18Core_continuousOn hθ
  · intro t ht
    have ht' : t ∈ Ioo 0 (Real.exp (-θ)) := by simpa only [interior_Icc] using ht
    exact (n18Core_deriv hθ ht'.1 ht'.2.le).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo 0 (Real.exp (-θ)) := by simpa only [interior_Icc] using ht
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ.le) (mul_nonneg ht'.1.le (sq_nonneg _))

theorem n18Core_convex {θ : ℝ} (hθ : 2 ≤ θ) :
    ConvexOn ℝ (Icc 0 (Real.exp (-θ))) (n18Core θ) := by
  have hp : 0 < θ := by linarith
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
  · exact n18Core_continuousOn hp
  · intro t ht
    have ht' : t ∈ Ioo 0 (Real.exp (-θ)) := by simpa only [interior_Icc] using ht
    exact (n18Core_deriv hp ht'.1 ht'.2.le).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo 0 (Real.exp (-θ)) := by simpa only [interior_Icc] using ht
    exact (n18Core_deriv2 hp ht'.1 ht'.2.le).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo 0 (Real.exp (-θ)) := by simpa only [interior_Icc] using ht
    have hl := n18_log_bound ht'.1 ht'.2.le
    apply div_nonneg_of_nonpos
    · exact mul_nonpos_of_nonneg_of_nonpos hp.le (by linarith)
    · apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
      simpa only [pow_succ] using mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (Real.log t)) (show Real.log t ≤ 0 by linarith)

theorem n18Core_cutoff {θ : ℝ} (hθ : θ ≠ 0) : n18Core θ (Real.exp (-θ)) = 0 := by
  simp [n18Core,hθ]

theorem n18Core_nonneg {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Icc 0 (Real.exp (-θ))) :
    0 ≤ n18Core θ t := by
  rw [← n18Core_cutoff hθ.ne']
  exact n18Core_antitone hθ ht ⟨(Real.exp_pos _).le,le_rfl⟩ ht.2

end Verification
