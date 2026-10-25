import Proofread.Library.UnitSquareModel
import Copula.CDF.Extensionality
import Copula.Dependence.Basic
import Copula.Independence
import Copula.Rank.SpearmanCDF
import Copula.Rank.Basic
import Copula.Reflection.Bivariate

/-! # Copulas of the unit-square vocabulary are library copulas

An article compiled with `Proofread.UnitSquare.withCore` speaks of functions
`F : I → I → ℝ` that are distribution functions on `[0,1]^2` with uniform
marginals (`Proofread.UnitSquare.distFn2 F ∧ dfUniformMarginals F`). These are
exactly the distribution functions `cdfOf K` of the copula library's `Copula 2`.
The theorems here are proved once and used by every compiled article:
`isCopula_cdfOf`, `exists_cdfOf`, and the integral forms of Spearman's rho and
Gini's gamma. -/

namespace Papers.Common
open MeasureTheory ProbabilityTheory Proofread
open scoped unitInterval

/-- The distribution function of a library copula, on `[0,1]^2`. -/
noncomputable def cdfOf (K : Copula 2) : I → I → ℝ := fun u v => K.cdf ![u, v]

theorem cdfOf_injective : Function.Injective cdfOf := by
  intro K L h
  apply Copula.ext_cdf
  intro x
  have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  rw [hx]
  exact congrFun (congrFun h (x 0)) (x 1)

theorem iic_one : Set.Iic (1 : I) = Set.univ := Set.eq_univ_of_forall fun x => x.2.2

theorem pair_preimage_iic (u v : I) :
    (MeasurableEquiv.finTwoArrow : (Fin 2 → I) ≃ᵐ I × I) ⁻¹' (Set.Iic u ×ˢ Set.Iic v) = Set.Iic ![u, v] := by
  ext x
  simp [MeasurableEquiv.finTwoArrow, Pi.le_def, Fin.forall_fin_two]

theorem pair_symm_preimage_iic (u v : I) :
    (MeasurableEquiv.finTwoArrow : (Fin 2 → I) ≃ᵐ I × I).symm ⁻¹' Set.Iic ![u, v] = Set.Iic u ×ˢ Set.Iic v := by
  ext p
  simp [MeasurableEquiv.finTwoArrow, Pi.le_def, Fin.forall_fin_two, Prod.le_def]

/-- Library copulas are copulas of the vocabulary. -/
theorem isCopula_cdfOf (K : Copula 2) :
    UnitSquare.distFn2 (cdfOf K) ∧ UnitSquare.dfUniformMarginals (cdfOf K) := by
  let e : (Fin 2 → I) ≃ᵐ I × I := MeasurableEquiv.finTwoArrow
  refine ⟨⟨K.toMeasure.map e, inferInstance, fun u v => ?_⟩, fun u => ?_, fun v => ?_⟩
  · rw [Measure.map_apply e.measurable (measurableSet_Iic.prod measurableSet_Iic), pair_preimage_iic]
    rfl
  · exact Copula.cdf_two_one_right K u
  · exact Copula.cdf_two_one_left K v

/-- Copulas of the vocabulary are library copulas. -/
theorem exists_cdfOf {F : I → I → ℝ}
    (hF : UnitSquare.distFn2 F ∧ UnitSquare.dfUniformMarginals F) : ∃ K : Copula 2, F = cdfOf K := by
  obtain ⟨⟨μ, hμ, hrect⟩, hu, hv⟩ := hF
  let e : (Fin 2 → I) ≃ᵐ I × I := MeasurableEquiv.finTwoArrow
  have hrectE : ∀ u v : I, μ (Set.Iic u ×ˢ Set.Iic v) = ENNReal.ofReal (F u v) := by
    intro u v; rw [hrect, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have marg0 : (μ.map e.symm).map (fun x => x 0) = (volume : Measure I) := by
    rw [Measure.map_map (measurable_pi_apply 0) e.symm.measurable]
    apply Measure.ext_of_Iic
    intro a
    rw [Measure.map_apply ((measurable_pi_apply 0).comp e.symm.measurable) measurableSet_Iic,
      unitInterval.volume_Iic]
    have : ((fun x : Fin 2 → I => x 0) ∘ e.symm) ⁻¹' Set.Iic a = Set.Iic a ×ˢ Set.Iic 1 := by
      ext p; simp [e, MeasurableEquiv.finTwoArrow, iic_one]
    rw [this, hrectE, hu]
  have marg1 : (μ.map e.symm).map (fun x => x 1) = (volume : Measure I) := by
    rw [Measure.map_map (measurable_pi_apply 1) e.symm.measurable]
    apply Measure.ext_of_Iic
    intro a
    rw [Measure.map_apply ((measurable_pi_apply 1).comp e.symm.measurable) measurableSet_Iic,
      unitInterval.volume_Iic]
    have : ((fun x : Fin 2 → I => x 1) ∘ e.symm) ⁻¹' Set.Iic a = Set.Iic 1 ×ˢ Set.Iic a := by
      ext p; simp [e, MeasurableEquiv.finTwoArrow, iic_one]
    rw [this, hrectE, hv]
  have marg : ∀ i : Fin 2, (μ.map e.symm).map (fun x => x i) = (volume : Measure I) := by
    intro i; fin_cases i
    · exact marg0
    · exact marg1
  refine ⟨⟨⟨μ.map e.symm, inferInstance⟩, marg⟩, ?_⟩
  funext u v
  change F u v = (μ.map e.symm).real (Set.Iic ![u, v])
  rw [map_measureReal_apply e.symm.measurable measurableSet_Iic, pair_symm_preimage_iic, measureReal_def,
    hrect]

theorem isCopula_iff (F : I → I → ℝ) :
    (UnitSquare.distFn2 F ∧ UnitSquare.dfUniformMarginals F) ↔ ∃ K : Copula 2, F = cdfOf K :=
  ⟨exists_cdfOf, fun ⟨K, h⟩ => h ▸ isCopula_cdfOf K⟩

/-! ## Continuity and integrals -/

theorem continuous_cdfOf (K : Copula 2) : Continuous (fun p : I × I => cdfOf K p.1 p.2) :=
  K.continuous_cdf.comp (by fun_prop)

theorem integrable_section {h : I → I → ℝ} (hc : Continuous (fun p : I × I => h p.1 p.2)) (v : I) :
    Prelude.integrable (fun u => h u v) :=
  (hc.comp (Continuous.prodMk continuous_id continuous_const)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem continuous_integral {h : I → I → ℝ} (hc : Continuous (fun p : I × I => h p.1 p.2)) :
    Continuous (fun v : I => ∫ u : I, h u v) := by
  have := continuous_parametric_integral_of_continuous (μ := (volume : Measure I))
    (f := fun v u => h u v) (hc.comp continuous_swap) (s := Set.univ) isCompact_univ
  simpa only [Measure.restrict_univ] using this

theorem integrable_integral {h : I → I → ℝ} (hc : Continuous (fun p : I × I => h p.1 p.2)) :
    Prelude.integrable (fun v => ∫ u : I, h u v) :=
  (continuous_integral hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_of_continuous {f : I → ℝ} (hf : Continuous f) : Prelude.integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- `12 ∫∫ C - 3` is Spearman's rho. -/
theorem spearmanRho_cdfOf (K : Copula 2) :
    12 * (∫ v : I, ∫ u : I, cdfOf K u v) - 3 = K.spearmanRho := by
  change 12 * (∫ v : I, ∫ u : I, K.cdf ![u, v]) - 3 = K.spearmanRho
  rw [K.spearmanRho_eq_integral_cdf, Copula.toMeasure_independence]
  have hm := ((volume_preserving_finTwoArrow I).symm MeasurableEquiv.finTwoArrow).integral_comp
    MeasurableEquiv.finTwoArrow.symm.measurableEmbedding K.cdf
  have hi : Integrable (fun p : I × I => K.cdf ![p.1, p.2]) ((volume : Measure I).prod volume) :=
    (K.continuous_cdf.comp (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  congr 2
  change (∫ v : I, ∫ u : I, K.cdf ![u, v]) = ∫ x : Fin 2 → I, K.cdf x
  rw [← hm]
  exact (integral_prod_symm _ hi).symm

theorem reflectUnit (w : I) : Set.projIcc (0 : ℝ) 1 zero_le_one (1 - (w : ℝ)) = σ w := by
  apply Subtype.ext
  rw [Set.coe_projIcc, unitInterval.coe_symm_eq, min_eq_right (by linarith [w.2.1]),
    max_eq_right (by linarith [w.2.2])]

/-- `4 ∫ {C(u,u) + C(u,1-u)} du - 2` is Gini's gamma. -/
theorem giniGamma_cdfOf (K : Copula 2) :
    4 * (∫ u : I, (cdfOf K u u + cdfOf K u (Set.projIcc (0 : ℝ) 1 zero_le_one (1 - (u : ℝ))))) - 2 =
      K.giniGamma := by
  unfold Copula.giniGamma
  simp only [cdfOf, reflectUnit]
  rw [integral_add (K.integrable_diagonal_cdf) (K.integrable_antidiagonal_cdf)]

end Papers.Common
