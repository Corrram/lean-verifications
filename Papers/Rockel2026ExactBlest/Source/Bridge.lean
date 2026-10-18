import Papers.Rockel2026ExactBlest.Source.Article
import Papers.Rockel2026ExactBlest.ExactBlestPaperParams
import Mathlib

/-! # The article's definitions are the library's notions

Theorems identifying each definition compiled from `article.tex` with the
corresponding notion of the copula library and of the companion development:
`copulas` are exactly the distribution functions of `Copula 2`, the article's
`ν`, `ρ`, transposition, reflection and survival transform are `blestNu`,
`spearmanRho`, `transpose`, `reflect {1}` and `survivalCopula`, `ζ_c` is the
companion's `quadraticRank (1 - c)` and `D_c` is `paperD c`. These are proved,
so the companion's results apply to the article's statements without any
choice of interpretation. -/

namespace Papers.Rockel2026ExactBlest.Source.Bridge
open Papers.Rockel2026ExactBlest.Source LeanMirror.Tex MeasureTheory ProbabilityTheory
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

/-- Library copulas give article copulas. -/
theorem copulas_cdfOf (K : Copula 2) : copulas (cdfOf K) := by
  let e : (Fin 2 → I) ≃ᵐ I × I := MeasurableEquiv.finTwoArrow
  refine ⟨⟨K.toMeasure.map e, inferInstance, fun u v => ?_⟩, fun u => ?_, fun v => ?_⟩
  · rw [Measure.map_apply e.measurable (measurableSet_Iic.prod measurableSet_Iic), pair_preimage_iic]
    rfl
  · exact Copula.cdf_two_one_right K u
  · exact Copula.cdf_two_one_left K v

/-- Article copulas are library copulas. -/
theorem exists_of_copulas {F : I → I → ℝ} (hF : copulas F) : ∃ K : Copula 2, F = cdfOf K := by
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

theorem copulas_iff (F : I → I → ℝ) : copulas F ↔ ∃ K : Copula 2, F = cdfOf K :=
  ⟨exists_of_copulas, fun ⟨K, h⟩ => h ▸ copulas_cdfOf K⟩

/-! ## Coefficients -/

theorem rho_cdfOf (K : Copula 2) : rho (cdfOf K) = K.spearmanRho := by
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

theorem nu_cdfOf (K : Copula 2) : nu (cdfOf K) = Papers.Rockel2026XiBlest.blestNu K := by
  change 24 * (∫ v : I, ∫ u : I, (1 - (u : ℝ)) * K.cdf ![u, v]) - 2 = _
  exact (Papers.Rockel2026XiBlest.blest_integral_formula K).symm

theorem reflectUnit (w : I) : Set.projIcc (0 : ℝ) 1 zero_le_one (1 - (w : ℝ)) = σ w := by
  apply Subtype.ext
  rw [Set.coe_projIcc, unitInterval.coe_symm_eq, min_eq_right (by linarith [w.2.1]),
    max_eq_right (by linarith [w.2.2])]

theorem transpose_cdfOf (K : Copula 2) : transpose (cdfOf K) = cdfOf K.transpose := by
  funext u v
  exact (Copula.cdf_transpose K u v).symm

theorem survival_cdfOf (K : Copula 2) : survival (cdfOf K) = cdfOf K.survivalCopula := by
  funext u v
  simp only [survival, cdfOf, reflectUnit]
  exact (Copula.cdf_survivalCopula K u v).symm

theorem reflection_cdfOf (K : Copula 2) : reflection (cdfOf K) = cdfOf (K.reflect {1}) := by
  funext u v
  simp only [reflection, cdfOf, reflectUnit]
  exact (Copula.cdf_reflect_second K u v).symm

theorem eta_cdfOf (K : Copula 2) : eta (cdfOf K) = Papers.Rockel2026ExactBlest.eta K := by
  simp only [eta, transpose_cdfOf, nu_cdfOf, Papers.Rockel2026ExactBlest.eta]

/-! ## The boundary `Φ` -/

theorem Phi_eq (r : ℝ) (hr : -1 ≤ r ∧ r ≤ 1) : Phi r = Papers.Rockel2026ExactBlest.rhoBoundary r := by
  unfold Phi Papers.Rockel2026ExactBlest.rhoBoundary
  by_cases h : -1 ≤ r ∧ r ≤ 0
  · rw [ite_eq_left h]
    by_cases h0 : 0 ≤ r
    · have : r = 0 := le_antisymm h.2 h0
      subst this; rw [ite_eq_left h0]; norm_num
    · rw [ite_eq_right h0]
  · have h0 : 0 ≤ r := by
      by_contra hn; exact h ⟨hr.1, le_of_lt (lt_of_not_ge hn)⟩
    rw [ite_eq_right h, ite_eq_left ⟨h0, hr.2⟩, ite_eq_left h0]

/-! ## The rank map `ζ_c` and the family `D_c` -/

theorem leb_rank (c x : I) :
    Leb (fun t : I => |(t : ℝ) + c - 1| ≤ |(x : ℝ) + c - 1|) =
      (Papers.Rockel2026ExactBlest.quadraticRank (σ c) x : ℝ) := by
  have hpre : Papers.Rockel2026ExactBlest.quadraticScore (σ c : ℝ) ⁻¹'
      Set.Iic (Papers.Rockel2026ExactBlest.quadraticScore (σ c : ℝ) x) =
      {t : I | |(t : ℝ) + c - 1| ≤ |(x : ℝ) + c - 1|} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq, Papers.Rockel2026ExactBlest.quadraticScore,
      unitInterval.coe_symm_eq]
    rw [sq_le_sq]
    rw [show (t : ℝ) - (1 - c) = t + c - 1 by ring, show (x : ℝ) - (1 - c) = x + c - 1 by ring]
  simp only [Papers.Rockel2026ExactBlest.quadraticRank, coe_cdfUnit]
  rw [ProbabilityTheory.cdf_eq_real, Papers.Rockel2026ExactBlest.quadraticLaw,
    map_measureReal_apply (by unfold Papers.Rockel2026ExactBlest.quadraticScore; fun_prop) measurableSet_Iic,
    hpre]
  rfl

theorem zeta_eq (c : I) : zeta c = Papers.Rockel2026ExactBlest.quadraticRank (σ c) := by
  funext x
  simp only [zeta, leb_rank, Set.projIcc_val]

theorem measurable_zeta (c : I) : Measurable (zeta c) := by
  rw [zeta_eq]; exact (Papers.Rockel2026ExactBlest.quadraticRank_uniform _).measurable

theorem D_eq (c : I) : D c = cdfOf (Papers.Rockel2026ExactBlest.paperD c) := by
  set q := Papers.Rockel2026ExactBlest.quadraticRank (σ c : ℝ)
  have hq : Measurable q := (Papers.Rockel2026ExactBlest.quadraticRank_uniform _).measurable
  have hg : Measurable (fun t : I => ![t, q t]) := by fun_prop
  have hr : Measurable (Copula.reflectPoint (Finset.univ : Finset (Fin 2))) := Copula.measurable_reflectPoint _
  have hP : (Papers.Rockel2026ExactBlest.paperD c).toMeasure =
      (volume : Measure I).map (Copula.reflectPoint Finset.univ ∘ fun t => ![t, q t]) := by
    conv_lhs => rw [← Copula.survivalCopula_survivalCopula (Papers.Rockel2026ExactBlest.paperD c)]
    rw [Copula.survivalCopula, Copula.toMeasure_reflect, Papers.Rockel2026ExactBlest.paperD_graph_law,
      Measure.map_map hr hg]
  funext u v
  simp only [D, copulaAssociatedWith, gamma, Prelude.leb, cdfOf, Copula.cdf, zeta_eq]
  rw [hP, map_measureReal_apply (hr.comp hg) measurableSet_Iic, measureReal_def]
  congr 2
  ext t
  simp [Copula.reflectPoint, Pi.le_def, Fin.forall_fin_two, ← Subtype.coe_le_coe, unitInterval.coe_symm_eq, q]

theorem copulas_D (c : I) : copulas (D c) := D_eq c ▸ copulas_cdfOf _

end Papers.Rockel2026ExactBlest.Source.Bridge
