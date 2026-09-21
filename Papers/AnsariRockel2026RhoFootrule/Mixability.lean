import Papers.AnsariRockel2026RhoFootrule.MeanVariance
import Copula.Rank.Symmetry

/-! # Theorem 2.4: the generalized mixability optimization problem

Every coupling of two centered uniforms is represented by shifting both uniform
coordinates by -1/2. Reflection of the second coordinate identifies their absolute
sum with the absolute displacement problem, preserving the entire probability law.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2026RhoFootrule

noncomputable def centeredSumMean (C : Copula 2) : ℝ :=
  ∫ x, |((x 0 : ℝ) - 1 / 2) + ((x 1 : ℝ) - 1 / 2)| ∂C.toMeasure

noncomputable def centeredSumVariance (C : Copula 2) : ℝ :=
  ∫ x, (|((x 0 : ℝ) - 1 / 2) + ((x 1 : ℝ) - 1 / 2)| - centeredSumMean C) ^ 2 ∂C.toMeasure

/-- Reflection identifies the full law, hence every continuous test function, of the magnitudes. -/
theorem centered_sum_law (C : Copula 2) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x, f (|((x 0 : ℝ) - 1 / 2) + ((x 1 : ℝ) - 1 / 2)|) ∂C.toMeasure) =
      ∫ x, f (|(x 0 : ℝ) - x 1|) ∂(C.reflect {1}).toMeasure := by
  rw [C.integral_reflect _ _ (by fun_prop)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [Copula.reflectPoint, Finset.mem_singleton, show (0 : Fin 2) ≠ 1 by decide,
      ite_false, ite_true, unitInterval.coe_symm_eq]
    congr 2
    ring

/-- Both optimization statistics are preserved by the reflection equivalence. -/
theorem centered_sum_statistics (C : Copula 2) :
    centeredSumMean C = meanDistance (C.reflect {1}) ∧
      centeredSumVariance C = distanceVariance (C.reflect {1}) := by
  have hm : centeredSumMean C = meanDistance (C.reflect {1}) := centered_sum_law C id continuous_id
  refine ⟨hm, ?_⟩
  unfold centeredSumVariance distanceVariance
  rw [← hm]
  exact centered_sum_law C (fun r => (r - centeredSumMean C) ^ 2) (by fun_prop)

/-- Feasible variances in the source constrained optimization problem. -/
def mixabilityVariances (m : ℝ) : Set ℝ :=
  {v | ∃ C : Copula 2, centeredSumMean C = m ∧ centeredSumVariance C = v}

/-- Theorem 2.4: the source infimum is attained and equals the exact correction. -/
theorem mixability_minimum {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    IsLeast (mixabilityVariances m) (minimumVariance m) := by
  constructor
  · obtain ⟨C, hmean, hvar⟩ := (exact_mean_variance_region m (minimumVariance m)).mpr
      ⟨hm, le_rfl, minimumVariance_le_maximumVariance hm⟩
    refine ⟨C.reflect {1}, ?_, ?_⟩
    · rw [(centered_sum_statistics _).1, C.reflect_reflect]
      exact hmean
    · rw [(centered_sum_statistics _).2, C.reflect_reflect]
      exact hvar
  · rintro v ⟨C, hmean, hvar⟩
    have h := (sharp_variance_bounds (C.reflect {1})).1
    rwa [← (centered_sum_statistics C).1, ← (centered_sum_statistics C).2, hmean, hvar] at h

/-- The infimum notation in equation (33). -/
theorem mixability_infimum {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    sInf (mixabilityVariances m) = minimumVariance m := (mixability_minimum hm).csInf_eq

/-- Exactly the source set of generalized complete-mixability magnitudes. -/
theorem mixability_zero_iff {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    sInf (mixabilityVariances m) = 0 ↔ m = 0 ∨ ∃ N : ℕ, 0 < N ∧ m = 1 / (2 * (N : ℝ)) := by
  rw [mixability_infimum hm, minimum_variance_zero_iff hm]

/-- The bound applies on an arbitrary probability space, via the joint law of any two uniforms. -/
theorem centered_sum_variance_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (X : Ω → Fin 2 → I) (hX : Measurable X)
    (hU : ∀ i, μ.toMeasure.map (fun ω => X ω i) = volume) :
    let m := ∫ ω, |((X ω 0 : ℝ) - 1 / 2) + ((X ω 1 : ℝ) - 1 / 2)| ∂μ.toMeasure
    minimumVariance m ≤
      ∫ ω, (|((X ω 0 : ℝ) - 1 / 2) + ((X ω 1 : ℝ) - 1 / 2)| - m) ^ 2 ∂μ.toMeasure := by
  dsimp
  let C := Copula.ofMap μ X hX hU
  have hmean : centeredSumMean C =
      ∫ ω, |((X ω 0 : ℝ) - 1 / 2) + ((X ω 1 : ℝ) - 1 / 2)| ∂μ.toMeasure := by
    unfold centeredSumMean
    exact integral_map hX.aemeasurable (show Measurable (fun x : Fin 2 → I =>
      |((x 0 : ℝ) - 1 / 2) + ((x 1 : ℝ) - 1 / 2)|) by fun_prop).aestronglyMeasurable
  have hvar : centeredSumVariance C =
      ∫ ω, (|((X ω 0 : ℝ) - 1 / 2) + ((X ω 1 : ℝ) - 1 / 2)| - centeredSumMean C) ^ 2 ∂μ.toMeasure := by
    unfold centeredSumVariance
    exact integral_map hX.aemeasurable (show Measurable (fun x : Fin 2 → I =>
      (|((x 0 : ℝ) - 1 / 2) + ((x 1 : ℝ) - 1 / 2)| - centeredSumMean C) ^ 2) by fun_prop).aestronglyMeasurable
  have h := (sharp_variance_bounds (C.reflect {1})).1
  rw [← (centered_sum_statistics C).1, ← (centered_sum_statistics C).2, hvar, hmean] at h
  exact h

end Papers.AnsariRockel2026RhoFootrule
