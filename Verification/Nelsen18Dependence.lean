import Verification.Nelsen18
import Verification.MTP2ConditionalIncreasing
import Copula.TailDependence.Basic

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem nelsen18_zero_diagonal (θ : ℝ) (hθ : 2 ≤ θ) :
    ∃ q : I, 0 < q ∧ (nelsen18 θ hθ).cdf ![q,q] = 0 := by
  have hp : 0 < θ := by linarith
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < θ+Real.log 2 := add_pos hp hl
  have hq0 : 0 < Real.log 2/(θ+Real.log 2) := div_pos hl hd
  have hq1 : Real.log 2/(θ+Real.log 2) < 1 := (div_lt_one hd).mpr (by linarith)
  let q : I := ⟨Real.log 2/(θ+Real.log 2),hq0.le,hq1.le⟩
  have hi : n18Inv θ q = Real.exp (-θ)/2 := by
    have hq : q ≠ 1 := ne_of_lt (show q < 1 from hq1)
    simp only [n18Inv,hq,ite_false]
    have he : θ/((q:ℝ)-1) = -θ-Real.log 2 := by
      dsimp [q]
      field_simp [hp.ne',hd.ne']
      ring
    rw [he,Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ) < 2)]
  refine ⟨q,hq0,?_⟩
  rw [nelsen18_cdf_full,hi]
  rw [show Real.exp (-θ)/2+Real.exp (-θ)/2 = Real.exp (-θ) by ring,Real.log_exp]
  have he : 1+θ/(-θ) = 0 := by field_simp; ring
  rw [he,max_self]

theorem nelsen18_not_pqd (θ : ℝ) (hθ : 2 ≤ θ) : ¬ (nelsen18 θ hθ).IsPQD := by
  obtain ⟨q,hq,hz⟩ := nelsen18_zero_diagonal θ hθ
  intro h
  have hh := h q q
  rw [hz] at hh
  exact (not_le_of_gt (mul_pos (show 0 < (q:ℝ) from hq) hq)) hh

theorem nelsen18_not_ci (θ : ℝ) (hθ : 2 ≤ θ) : ¬ (nelsen18 θ hθ).IsCI :=
  fun h => nelsen18_not_pqd θ hθ h.isPQD

theorem nelsen18_not_density_tp2 (θ : ℝ) (hθ : 2 ≤ θ) : ¬ (nelsen18 θ hθ).HasMTP2Density :=
  fun h => nelsen18_not_ci θ hθ (mtp2_isCI h)

theorem nelsen18_lowerTail (θ : ℝ) (hθ : 2 ≤ θ) : (nelsen18 θ hθ).HasLowerTailDependence 0 := by
  obtain ⟨q,hq,hz⟩ := nelsen18_zero_diagonal θ hθ
  apply tendsto_const_nhds.congr'
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hq)] with t ht
  have hh := (nelsen18 θ hθ).monotone_cdf (show ![t,t] ≤ ![q,q] from by
    intro i; fin_cases i <;> exact ht.le)
  have he : (nelsen18 θ hθ).cdf ![t,t] = 0 := le_antisymm (hh.trans_eq hz) ((nelsen18 θ hθ).cdf_nonneg _)
  simp [lowerTailRatio,Copula.diagonal,he]

end Verification
