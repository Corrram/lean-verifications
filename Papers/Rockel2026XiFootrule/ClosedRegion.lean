import Papers.Rockel2026XiFootrule.RegionGeometry
import Verification.XiClosedRegion

open MeasureTheory ProbabilityTheory Set Filter Verification
open scoped unitInterval Topology

namespace Papers.Rockel2026XiFootrule

theorem footrule_tendsto_of_cdf (C : ℕ → Copula 2) (D : Copula 2)
    (hC : ∀ u v : I, Tendsto (fun n => (C n).cdf ![u,v]) atTop (𝓝 (D.cdf ![u,v]))) :
    Tendsto (fun n => (C n).spearmanFootrule) atTop (𝓝 D.spearmanFootrule) := by
  have he := tendsto_integral_of_dominated_convergence (μ := (volume : Measure I)) (fun _ : I => (1 : ℝ))
    (fun n => ((C n).continuous_cdf.comp (show Continuous (fun t : I => ![t,t]) by fun_prop)).measurable.aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall fun t => by
      dsimp only [Function.comp_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg ((C n).cdf_nonneg _)]
      exact (C n).cdf_le_one _)
    (Eventually.of_forall fun t => hC t t)
  exact (he.const_mul 6).sub_const 2

/-- Theorem 3.3: closedness of the full attained region, including its negative part. -/
theorem attainable_region_closed : IsClosed attainableRegion :=
  isClosed_xiCoefficientRegion _ footrule_tendsto_of_cdf fixed_footrule_upward

/-- Compactness concerns actual coefficient pairs, not the relaxed lower-bound profile. -/
theorem attainable_region_compact : IsCompact attainableRegion :=
  isCompact_xiCoefficientRegion _ attainable_region_closed (-1/2) 1 (fun C => C.spearmanFootrule_mem_Icc)

/-- The lower footrule boundary is attained at every prescribed xi. -/
theorem minimal_footrule_attained (x : ℝ) (hx : x ∈ Icc 0 1) :
    ∃ C : Copula 2, C.chatterjeeXi=x ∧
      ∀ D : Copula 2, D.chatterjeeXi=x → C.spearmanFootrule ≤ D.spearmanFootrule := by
  let a : I := ⟨Real.sqrt x,Real.sqrt_nonneg _,(Real.sqrt_le_one).mpr hx.2⟩
  have ha : (upperBoundary a).chatterjeeXi=x := by rw [xi_upperBoundary]; exact Real.sq_sqrt hx.1
  obtain ⟨L,U,hL,_,he⟩ := xi_slice_extrema _ attainable_region_compact (upperBoundary a)
  refine ⟨L,hL.trans ha,fun D hD => (he D (hD.trans ha.symm)).1⟩

/-- Every horizontal slice, including negative footrule, attains its least xi. -/
theorem minimal_xi_attained (y : ℝ) (hy : y ∈ Icc (-1/2) 1) :
    ∃ C : Copula 2, C.spearmanFootrule=y ∧
      ∀ D : Copula 2, D.spearmanFootrule=y → C.chatterjeeXi ≤ D.chatterjeeXi := by
  obtain ⟨C,_,hC⟩ := (xi_one_slice y).mpr hy
  obtain ⟨L,hL,hmin⟩ := coefficient_slice_minimum _ attainable_region_compact C
  exact ⟨L,hL.trans hC,fun D hD => hmin D (hD.trans hC.symm)⟩

end Papers.Rockel2026XiFootrule
