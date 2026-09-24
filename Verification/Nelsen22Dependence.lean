import Verification.Nelsen22
import Verification.MTP2ConditionalIncreasing
import Copula.TailDependence.Basic
import Copula.TailDependence.Examples

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem nelsen22_zero_diagonal {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ q : I, 0 < q ∧ (nelsen22 θ ⟨hθ.le,hθ1⟩).cdf ![q,q] = 0 := by
  have hs0 : 0 ≤ Real.sin (Real.pi/4) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  have hs1 : Real.sin (Real.pi/4) < 1 := by
    have hh := Real.strictMonoOn_sin (show Real.pi/4 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
      (show Real.pi/2 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
      (show Real.pi/4 < Real.pi/2 by linarith [Real.pi_pos])
    simpa only [Real.sin_pi_div_two] using hh
  have hb : 0 < 1-Real.sin (Real.pi/4) := sub_pos.mpr hs1
  have hq0 : 0 < (1-Real.sin (Real.pi/4))^θ⁻¹ := Real.rpow_pos_of_pos hb _
  have hq1 : (1-Real.sin (Real.pi/4))^θ⁻¹ ≤ 1 := Real.rpow_le_one hb.le (by linarith) (inv_pos.mpr hθ).le
  let q : I := ⟨(1-Real.sin (Real.pi/4))^θ⁻¹,hq0.le,hq1⟩
  have he : (q:ℝ)^θ = 1-Real.sin (Real.pi/4) := Real.rpow_inv_rpow hb.le hθ.ne'
  refine ⟨q,hq0,?_⟩
  rw [nelsen22_cdf_full hθ hθ1,he,sub_sub_cancel,
    Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  rw [show Real.pi/4+Real.pi/4 = Real.pi/2 by ring,min_self,Real.sin_pi_div_two,sub_self,
    Real.zero_rpow (inv_ne_zero hθ.ne')]

theorem nelsen22_not_pqd {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ¬ (nelsen22 θ ⟨hθ.le,hθ1⟩).IsPQD := by
  obtain ⟨q,hq,hz⟩ := nelsen22_zero_diagonal hθ hθ1
  intro h
  have hh := h q q
  rw [hz] at hh
  exact (not_le_of_gt (mul_pos (show 0 < (q:ℝ) from hq) hq)) hh

theorem nelsen22_not_ci {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ¬ (nelsen22 θ ⟨hθ.le,hθ1⟩).IsCI := fun h => nelsen22_not_pqd hθ hθ1 h.isPQD

theorem nelsen22_not_density_tp2 {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ¬ (nelsen22 θ ⟨hθ.le,hθ1⟩).HasMTP2Density := fun h => nelsen22_not_ci hθ hθ1 (mtp2_isCI h)

theorem nelsen22_lowerTail_positive {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (nelsen22 θ ⟨hθ.le,hθ1⟩).HasLowerTailDependence 0 := by
  obtain ⟨q,hq,hz⟩ := nelsen22_zero_diagonal hθ hθ1
  apply tendsto_const_nhds.congr'
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hq)] with t ht
  have hh := (nelsen22 θ ⟨hθ.le,hθ1⟩).monotone_cdf (show ![t,t] ≤ ![q,q] from by
    intro i; fin_cases i <;> exact ht.le)
  have he : (nelsen22 θ ⟨hθ.le,hθ1⟩).cdf ![t,t] = 0 := le_antisymm (hh.trans_eq hz) ((nelsen22 θ ⟨hθ.le,hθ1⟩).cdf_nonneg _)
  simp [lowerTailRatio,Copula.diagonal,he]

theorem nelsen22_isCI_iff (θ : ℝ) (hθ : θ ∈ Icc 0 1) :
    (nelsen22 θ hθ).IsCI ↔ θ = 0 := by
  constructor
  · intro h
    by_contra hn
    exact nelsen22_not_ci (lt_of_le_of_ne hθ.1 (Ne.symm hn)) hθ.2 h
  · intro hz; subst θ; rw [nelsen22_zero]; exact isCI_independence

theorem nelsen22_density_tp2_iff (θ : ℝ) (hθ : θ ∈ Icc 0 1) :
    (nelsen22 θ hθ).HasMTP2Density ↔ θ = 0 := by
  constructor
  · intro h; exact (nelsen22_isCI_iff θ hθ).mp (mtp2_isCI h)
  · intro hz; subst θ; rw [nelsen22_zero]; exact hasMTP2Density_independence 2

theorem nelsen22_lowerTail (θ : ℝ) (hθ : θ ∈ Icc 0 1) :
    (nelsen22 θ hθ).HasLowerTailDependence 0 := by
  by_cases hz : θ = 0
  · subst θ; rw [nelsen22_zero]; exact hasLowerTailDependence_independence
  · exact nelsen22_lowerTail_positive (lt_of_le_of_ne hθ.1 (Ne.symm hz)) hθ.2

end Verification
