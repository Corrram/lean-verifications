import Verification.Nelsen13
import Copula.Families.Nelsen12Limits

open ProbabilityTheory Set Filter
open Copula
open scoped unitInterval Topology

namespace Verification

theorem n13_powerRoot_bounds (p a b : ℝ) (hp : 0 < p) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    max a b ≤ (a^p+b^p-1)^p⁻¹ ∧
      (a^p+b^p-1)^p⁻¹ ≤ (2:ℝ)^p⁻¹*max a b := by
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hA := Real.one_le_rpow ha hp.le
  have hB := Real.one_le_rpow hb hp.le
  constructor
  · apply max_le
    · have hh := Real.rpow_le_rpow (Real.rpow_nonneg ha0 p)
        (show a^p ≤ a^p+b^p-1 by linarith) (inv_nonneg.mpr hp.le)
      rwa [Real.rpow_rpow_inv ha0 hp.ne'] at hh
    · have hh := Real.rpow_le_rpow (Real.rpow_nonneg hb0 p)
        (show b^p ≤ a^p+b^p-1 by linarith) (inv_nonneg.mpr hp.le)
      rwa [Real.rpow_rpow_inv hb0 hp.ne'] at hh
  · exact (Real.rpow_le_rpow (by linarith : 0 ≤ a^p+b^p-1)
      (by linarith : a^p+b^p-1 ≤ a^p+b^p) (inv_nonneg.mpr hp.le)).trans
      (twoTermPowerNorm_le p a b hp ha0 hb0)

theorem nelsen13_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 0 ≤ θ z) (hlim : Tendsto θ l atTop) (u v : I) :
    Tendsto (fun z => (nelsen13 (θ z) (hθ z)).cdf ![u,v]) l
      (𝓝 (min (u:ℝ) (v:ℝ))) := by
  by_cases hu : u = 0
  · subst u
    simpa [min_eq_left v.property.1] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (0:ℝ)) l (𝓝 0))
  by_cases hv : v = 0
  · subst v
    have he (C : Copula 2) : C.cdf ![u,0] = 0 :=
      Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)
    simpa [he, min_eq_right u.property.1] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (0:ℝ)) l (𝓝 0))
  have hu0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
  have hv0 : 0 < (v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
  let a : ℝ := 1-Real.log (u:ℝ)
  let b : ℝ := 1-Real.log (v:ℝ)
  have hq : Tendsto (fun z => (2:ℝ)^(θ z)⁻¹) l (𝓝 1) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : α => (2:ℝ)) l (𝓝 2)).rpow
      (tendsto_inv_atTop_zero.comp hlim) (Or.inl (by norm_num : (2:ℝ) ≠ 0)))
  have hup : Tendsto (fun z => (2:ℝ)^(θ z)⁻¹*max a b) l (𝓝 (max a b)) := by
    simpa only [one_mul] using hq.mul_const (max a b)
  have hp : ∀ᶠ z in l, 0 < θ z := hlim.eventually (eventually_gt_atTop 0)
  have hr : Tendsto (fun z => (a^(θ z)+b^(θ z)-1)^(θ z)⁻¹) l (𝓝 (max a b)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · filter_upwards [hp] with z hz
      exact (n13_powerRoot_bounds (θ z) a b hz (n13_inv_base u) (n13_inv_base v)).1
    · filter_upwards [hp] with z hz
      exact (n13_powerRoot_bounds (θ z) a b hz (n13_inv_base u) (n13_inv_base v)).2
  have he : Real.exp (1-max a b) = min (u:ℝ) (v:ℝ) := by
    rcases le_total (u:ℝ) (v:ℝ) with huv | hvu
    · have hab : b ≤ a := sub_le_sub_left (Real.log_le_log hu0 huv) 1
      rw [max_eq_left hab, min_eq_left huv]
      dsimp [a]
      rw [sub_sub_cancel, Real.exp_log hu0]
    · have hab : a ≤ b := sub_le_sub_left (Real.log_le_log hv0 hvu) 1
      rw [max_eq_right hab, min_eq_right hvu]
      dsimp [b]
      rw [sub_sub_cancel, Real.exp_log hv0]
  have hh : Tendsto (fun z => Real.exp (1-(a^(θ z)+b^(θ z)-1)^(θ z)⁻¹)) l
      (𝓝 (Real.exp (1-max a b))) :=
    (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.sub hr)
  rw [he] at hh
  apply hh.congr'
  filter_upwards [hp] with z hz
  rw [nelsen13_cdf (θ z) hz]
  simp [hu, hv, a, b]

end Verification
