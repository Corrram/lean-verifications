import Verification.RowEnergyConvergence

/-! # Continuous tests of partition-averaged conditional distributions -/

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval BigOperators Topology

namespace Verification

/-- A continuous test on the unit interval has an affine error modulus with
arbitrarily small constant term. -/
theorem continuous_unit_affine_modulus (φ : ℝ → ℝ) (hc : Continuous φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      |φ x-φ y| ≤ ε+K*|x-y| := by
  obtain ⟨b,hb⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  have hb0 : 0 ≤ b := (norm_nonneg (φ 0)).trans (hb 0 (by norm_num))
  have hu : UniformContinuous (fun x : I => φ (x:ℝ)) :=
    CompactSpace.uniformContinuous_of_continuous (hc.comp continuous_subtype_val)
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨2*b/δ,div_nonneg (by positivity) hδ.le,?_⟩
  intro x hx y hy
  by_cases hxy : |x-y| < δ
  · have h := hd (a := (⟨x,hx⟩ : I)) (b := (⟨y,hy⟩ : I)) hxy
    change |φ x-φ y| < ε at h
    exact h.le.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) (abs_nonneg _)))
  · have hbxy : |φ x-φ y| ≤ 2*b := by
      have hh := norm_sub_le (φ x) (φ y)
      simp only [Real.norm_eq_abs] at hh
      have hx' := hb x hx
      have hy' := hb y hy
      simp only [Real.norm_eq_abs] at hx' hy'
      linarith
    have hh : 2*b ≤ (2*b/δ)*|x-y| := by
      calc
        2*b = (2*b/δ)*δ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_of_not_gt hxy) (by positivity)
    linarith

theorem conditionalCDF_embed_comp_integrable {n : ℕ} (P : IntervalPartition n)
    (C : Copula 2) (i : Fin n) (v : I) (φ : ℝ → ℝ) (hc : Continuous φ) :
    Integrable (fun u : I => φ (C.conditionalCDF (partitionEmbed P i u) v)) := by
  obtain ⟨b,hb⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine (integrable_const b).mono'
    (hc.measurable.comp ((C.measurable_conditionalCDF_left v).comp
      (partitionEmbed_continuous P i).measurable)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun u => hb _ ⟨C.conditionalCDF_nonneg _ _,C.conditionalCDF_le_one _ _⟩

noncomputable def rowMeanTest {n : ℕ} (P : IntervalPartition n) (C : Copula 2)
    (v : I) (φ : ℝ → ℝ) : ℝ := ∑ i, P.width i*φ (copulaRowMean P C i v)

theorem rowMeanTest_error {n : ℕ} (P : IntervalPartition n) (C : Copula 2)
    (v : I) (φ : ℝ → ℝ) (hc : Continuous φ) (ε K : ℝ)
    (hm : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, |φ x-φ y| ≤ ε+K*|x-y|) :
    |rowMeanTest P C v φ-(∫ u : I,φ (C.conditionalCDF u v))| ≤
      ε+K*partitionAverageError P (fun u => C.conditionalCDF u v) := by
  have hi (i : Fin n) :
      |φ (copulaRowMean P C i v)-(∫ u : I,φ (C.conditionalCDF (partitionEmbed P i u) v))| ≤
        ε+K*(∫ u : I,|copulaRowMean P C i v-C.conditionalCDF (partitionEmbed P i u) v|) := by
    have he : φ (copulaRowMean P C i v)-(∫ u : I,φ (C.conditionalCDF (partitionEmbed P i u) v)) =
        ∫ u : I,φ (copulaRowMean P C i v)-φ (C.conditionalCDF (partitionEmbed P i u) v) := by
      rw [integral_sub (integrable_const _) (conditionalCDF_embed_comp_integrable P C i v φ hc)]
      simp
    rw [he]
    apply abs_integral_le_integral_abs.trans
    have hh := integral_mono
      ((integrable_const _).sub (conditionalCDF_embed_comp_integrable P C i v φ hc)).abs
      ((integrable_const ε).add (((integrable_const _).sub (conditionalCDF_embed_integrable P C i v)).abs.const_mul K))
      (fun u => hm _ (copulaRowMean_mem P C i v) _ ⟨C.conditionalCDF_nonneg _ _,C.conditionalCDF_le_one _ _⟩)
    simp only [Pi.add_apply,Pi.sub_apply] at hh
    rw [integral_add (g := fun u => K*|copulaRowMean P C i v-C.conditionalCDF (partitionEmbed P i u) v|) (integrable_const ε)
      (((integrable_const _).sub (conditionalCDF_embed_integrable P C i v)).abs.const_mul K),integral_const_mul] at hh
    simpa using hh
  rw [integral_partition P (fun u => φ (C.conditionalCDF u v)) (hc.measurable.comp (C.measurable_conditionalCDF_left v))
    (fun i => conditionalCDF_embed_comp_integrable P C i v φ hc)]
  unfold rowMeanTest
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |P.width i*φ (copulaRowMean P C i v)-P.width i*(∫ u : I,φ (C.conditionalCDF (partitionEmbed P i u) v))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, P.width i*|φ (copulaRowMean P C i v)-(∫ u : I,φ (C.conditionalCDF (partitionEmbed P i u) v))| := by
      simp_rw [← mul_sub,abs_mul,abs_of_pos (P.width_pos _)]
    _ ≤ ∑ i, P.width i*(ε+K*(∫ u : I,|copulaRowMean P C i v-C.conditionalCDF (partitionEmbed P i u) v|)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i) (P.width_pos i).le
    _ = _ := by
      unfold partitionAverageError partitionAverage
      simp_rw [← copulaRowMean_integral]
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,P.sum_width,one_mul]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem rowMeanTest_tendsto (C : Copula 2) (v : I) (φ : ℝ → ℝ) (hc : Continuous φ) :
    Tendsto (fun k => rowMeanTest (IntervalPartition.uniform (k+1) (by omega)) C v φ)
      atTop (𝓝 (∫ u : I,φ (C.conditionalCDF u v))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,_,hK⟩ := continuous_unit_affine_modulus φ hc (show 0<ε/2 by linarith)
  have he := partitionAverageError_tendsto (fun u => C.conditionalCDF u v)
    (C.measurable_conditionalCDF_left v) (C.integrable_conditionalCDF v)
    (fun k i => conditionalCDF_embed_integrable _ C i v)
  have hk := he.const_mul K
  simp only [mul_zero] at hk
  filter_upwards [hk.eventually (gt_mem_nhds (show 0<ε/2 by linarith))] with k hh
  rw [Real.dist_eq]
  exact (rowMeanTest_error _ C v φ hc (ε/2) K hK).trans_lt (by linarith)

end Verification
