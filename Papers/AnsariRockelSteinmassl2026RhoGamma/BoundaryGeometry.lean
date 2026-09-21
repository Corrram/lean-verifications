import Papers.AnsariRockelSteinmassl2026RhoGamma.ExactRegion
import Verification.CopulaOptimization
import Mathlib.Analysis.Convex.Continuous

/-! # Compactness and shape of the sharp boundary -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

theorem region_compact : IsCompact region := by
  let f : (Fin 2 → I) → ℝ := fun x => ((x 0 : ℝ) - x 1) ^ 2
  let g : (Fin 2 → I) → ℝ := fun x => |(x 0 : ℝ) + x 1 - 1| - |(x 0 : ℝ) - x 1|
  have hc := Verification.isCompact_copula_integral_pair
    (f := f) (g := g) (by fun_prop) (by fun_prop)
  have he : region = (fun y : ℝ × ℝ => (1 - 6 * y.1, 2 * y.2)) ''
      Set.range (fun C : Copula 2 => ((∫ x, f x ∂C.toMeasure), (∫ x, g x ∂C.toMeasure))) := by
    ext y
    constructor
    · rintro ⟨C, rfl⟩
      exact ⟨_, ⟨C, rfl⟩, Prod.ext (moment_representation C).1.symm (moment_representation C).2.symm⟩
    · rintro ⟨_, ⟨C, rfl⟩, rfl⟩
      exact ⟨C, Prod.ext (moment_representation C).1 (moment_representation C).2⟩
  rw [he]
  exact hc.image (by fun_prop)

theorem upperRho_endpoints : upperRho (-1) = -1 ∧ upperRho 1 = 1 :=
  ⟨upperRho_parameter .lowerEndpoint, upperRho_parameter .upperEndpoint⟩

theorem upperRho_concave : ConcaveOn ℝ (Icc (-1) 1) upperRho := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨C, hCx, hCr⟩ := upper_boundary_attained hx
  obtain ⟨D, hDy, hDr⟩ := upper_boundary_attained hy
  have h := sharp_upper_bound (C.mix D ⟨a, ha, by linarith⟩)
  rw [Copula.spearmanRho_mix, Copula.giniGamma_mix, hCx, hDy, hCr, hDr] at h
  have he : b = 1 - a := by linarith
  simpa only [smul_eq_mul, he] using h

/-- Strict increase follows from mixing a boundary optimizer with M. -/
theorem upperRho_strictMono : StrictMonoOn upperRho (Icc (-1) 1) := by
  intro x hx y hy hxy
  obtain ⟨C, hCx, hCr⟩ := upper_boundary_attained hx
  have hx1 : x < 1 := hxy.trans_le hy.2
  have hr1 : C.spearmanRho < 1 := lt_of_le_of_ne C.spearmanRho_mem_Icc.2 (by
    intro h
    have hC := C.spearmanRho_eq_one_iff.mp h
    rw [hC, Copula.giniGamma_comonotonic] at hCx
    linarith)
  let a : I := ⟨(1 - y) / (1 - x), div_nonneg (by linarith [hy.2]) (by linarith),
    (div_le_one (by linarith)).mpr (by linarith)⟩
  have ha : (a : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hgamma : (C.mix (Copula.comonotonic 2) a).giniGamma = y := by
    rw [Copula.giniGamma_mix, hCx, Copula.giniGamma_comonotonic]
    dsimp [a]
    field_simp [ne_of_gt (show 0 < 1 - x by linarith)]
    ring
  have h := sharp_upper_bound (C.mix (Copula.comonotonic 2) a)
  rw [hgamma, Copula.spearmanRho_mix, Copula.spearmanRho_comonotonic] at h
  have hp := mul_pos (sub_pos.mpr ha) (sub_pos.mpr hr1)
  rw [← hCr]
  nlinarith only [hp, h]

private theorem boundary_endpoint_continuous (x : ℝ) (hx : x = -1 ∨ x = 1) :
    ContinuousWithinAt upperRho (Icc (-1) 1) x := by
  let F : ℝ → ℝ × ℝ := fun g => (upperRho g, g)
  have hmem : ∀ᶠ g in nhdsWithin x (Icc (-1 : ℝ) 1), F g ∈ region := by
    filter_upwards [self_mem_nhdsWithin] with g hg
    obtain ⟨C, hCg, hCr⟩ := upper_boundary_attained hg
    exact ⟨C, Prod.ext hCr hCg⟩
  have ht : Filter.Tendsto F (nhdsWithin x (Icc (-1 : ℝ) 1)) (nhds (F x)) := by
    apply region_compact.tendsto_nhds_of_unique_mapClusterPt hmem
    intro y hy hcluster
    have hs := hcluster.continuousAt_comp (show ContinuousAt Prod.snd y from continuous_snd.continuousAt)
    have hs' : ClusterPt y.2 (nhdsWithin x (Icc (-1 : ℝ) 1)) := by
      exact mapClusterPt_id_iff.mp hs
    have hxy : y.2 = x := eq_of_nhds_neBot (hs'.mono nhdsWithin_le_nhds)
    obtain ⟨C, hC⟩ := hy
    have hg : C.giniGamma = x := (congrArg Prod.snd hC).trans hxy
    apply Prod.ext
    · change y.1 = upperRho x
      have hr : C.spearmanRho = y.1 := congrArg Prod.fst hC
      rcases hx with rfl | rfl
      · have he := C.giniGamma_eq_neg_one_iff.mp hg
        rw [he, Copula.spearmanRho_countermonotonic] at hr
        rw [upperRho_endpoints.1, ← hr]
      · have he := C.giniGamma_eq_one_iff.mp hg
        rw [he, Copula.spearmanRho_comonotonic] at hr
        rw [upperRho_endpoints.2, ← hr]
    · exact hxy
  exact continuous_fst.continuousAt.tendsto.comp ht

/-- Continuity includes both limiting endpoints, using compactness and endpoint rigidity. -/
theorem upperRho_continuous : ContinuousOn upperRho (Icc (-1) 1) := by
  intro x hx
  by_cases hm : x = -1
  · exact boundary_endpoint_continuous x (Or.inl hm)
  by_cases hp : x = 1
  · exact boundary_endpoint_continuous x (Or.inr hp)
  have hi : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hm), lt_of_le_of_ne hx.2 hp⟩
  have h := upperRho_concave.continuousOn_interior
  rw [interior_Icc] at h
  exact ((h x hi).continuousAt (isOpen_Ioo.mem_nhds hi)).continuousWithinAt

end Papers.AnsariRockelSteinmassl2026RhoGamma
