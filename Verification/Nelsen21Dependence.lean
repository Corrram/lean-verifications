import Verification.Nelsen21
import Verification.MTP2ConditionalIncreasing
import Copula.TailDependence.Basic

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem n21Core_pos {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Ico 0 1) : 0 < n21Core θ t := by
  have hi := n21_inner_mem hθ ⟨ht.1,ht.2.le⟩
  have hp : 0 < (1-t)^θ := Real.rpow_pos_of_pos (by linarith [ht.2]) _
  exact sub_pos.mpr (Real.rpow_lt_one hi.1 (by linarith) (inv_pos.mpr hθ))

theorem nelsen21_zero_diagonal (θ : ℝ) (hθ : 1 ≤ θ) :
    ∃ q : I, 0 < q ∧ (nelsen21 θ hθ).cdf ![q,q] = 0 := by
  have hp : 0 < θ := by linarith
  let q : I := ⟨n21Core θ (3/4),n21Core_mem hp (by norm_num)⟩
  have hq : 0 < (q:ℝ) := n21Core_pos hp (by norm_num)
  refine ⟨q,hq,?_⟩
  have hq0 : q ≠ 0 := ne_of_gt (show (0:I) < q from hq)
  rw [nelsen21,BivariateGenerator.cdf_copula,BivariateGenerator.cdf]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,hq0,or_self,ite_false]
  change n21Psi θ (n21Core θ (n21Core θ (3/4))+n21Core θ (n21Core θ (3/4))) = 0
  rw [n21Core_involutive hp (by norm_num)]
  norm_num [n21Psi,n21Core,Real.zero_rpow hp.ne']

theorem nelsen21_not_pqd (θ : ℝ) (hθ : 1 ≤ θ) : ¬ (nelsen21 θ hθ).IsPQD := by
  obtain ⟨q,hq,hz⟩ := nelsen21_zero_diagonal θ hθ
  intro h
  have hh := h q q
  rw [hz] at hh
  exact (not_le_of_gt (mul_pos (show 0 < (q:ℝ) from hq) hq)) hh

theorem nelsen21_not_ci (θ : ℝ) (hθ : 1 ≤ θ) : ¬ (nelsen21 θ hθ).IsCI :=
  fun h => nelsen21_not_pqd θ hθ h.isPQD

theorem nelsen21_not_density_tp2 (θ : ℝ) (hθ : 1 ≤ θ) : ¬ (nelsen21 θ hθ).HasMTP2Density :=
  fun h => nelsen21_not_ci θ hθ (mtp2_isCI h)

theorem nelsen21_lowerTail (θ : ℝ) (hθ : 1 ≤ θ) : (nelsen21 θ hθ).HasLowerTailDependence 0 := by
  obtain ⟨q,hq,hz⟩ := nelsen21_zero_diagonal θ hθ
  apply tendsto_const_nhds.congr'
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hq)] with t ht
  have hh := (nelsen21 θ hθ).monotone_cdf (show ![t,t] ≤ ![q,q] from by
    intro i; fin_cases i <;> exact ht.le)
  have he : (nelsen21 θ hθ).cdf ![t,t] = 0 := le_antisymm (hh.trans_eq hz) ((nelsen21 θ hθ).cdf_nonneg _)
  simp [lowerTailRatio,Copula.diagonal,he]

end Verification
