import Papers.Rockel2026XiBlest.ExtremalFamily
import Copula.Reflection
import Copula.Order.Orthant
import Copula.CDF.Continuity

/-! # Endpoint-safe version of the corrected shuffling path

The author revision flips the upper interval [1-p,1]. Its printed
endpoint convention sends both 1-p and 1 to 1-p. This file uses the
measure-equivalent convention that flips the closed upper interval,
so the map is an exact involution. The two conventions differ only at
the split point, which is null under the uniform marginal.
-/

open MeasureTheory Set ProbabilityTheory
open scoped unitInterval

namespace Papers.Rockel2026XiBlest

/-- Source split point 1-p. -/
noncomputable def shuffleCut (p : I) : I :=
  ⟨1 - (p : ℝ), by constructor <;> linarith [p.property.1, p.property.2]⟩

/-- The printed piecewise transformation, as a real-valued function. -/
noncomputable def printedShuffleReal (p : I) (u : I) : ℝ :=
  if (u : ℝ) ≤ (shuffleCut p : ℝ) then u
  else (shuffleCut p : ℝ) + 1 - u

/-- An endpoint-safe version that flips the closed upper interval. -/
noncomputable def shuffleReal (p : I) (u : I) : ℝ :=
  if (u : ℝ) < (shuffleCut p : ℝ) then u
  else (shuffleCut p : ℝ) + 1 - u

theorem shuffleReal_mem (p u : I) : shuffleReal p u ∈ Icc (0 : ℝ) 1 := by
  unfold shuffleReal
  split_ifs with h
  · exact u.property
  · have hc : (shuffleCut p : ℝ) ≤ u := le_of_not_gt h
    constructor
    · linarith [(shuffleCut p).property.1, u.property.2]
    · linarith

/-- The endpoint-safe shuffle, interpreted on the unit interval. -/
noncomputable def shufflePoint (p : I) (u : I) : I :=
  ⟨shuffleReal p u, shuffleReal_mem p u⟩

@[fun_prop] theorem measurable_shufflePoint (p : I) : Measurable (shufflePoint p) := by
  apply Measurable.subtype_mk
  unfold shuffleReal
  exact Measurable.ite
    (measurableSet_lt measurable_subtype_coe measurable_const)
    measurable_subtype_coe (by fun_prop)

/-- The endpoint-safe convention is an exact involution. -/
theorem shufflePoint_involution (p u : I) :
    shufflePoint p (shufflePoint p u) = u := by
  apply Subtype.ext
  change shuffleReal p (shufflePoint p u) = (u : ℝ)
  by_cases h : (u : ℝ) < (shuffleCut p : ℝ)
  · have hfirst : shufflePoint p u = u := Subtype.ext (by
      simp [shufflePoint, shuffleReal, h])
    rw [hfirst]
    simp [shuffleReal, h]
  · have hsecond : ¬ ((shufflePoint p u : I) : ℝ) < (shuffleCut p : ℝ) := by
      change ¬ shuffleReal p u < (shuffleCut p : ℝ)
      simp only [shuffleReal, ite_eq_right h]
      have hc : (shuffleCut p : ℝ) ≤ u := le_of_not_gt h
      linarith [u.property.2]
    rw [shuffleReal, ite_eq_right hsecond]
    change (shuffleCut p : ℝ) + 1 - shuffleReal p u = (u : ℝ)
    rw [shuffleReal, ite_eq_right h]
    ring

@[simp] theorem shuffleCut_zero : shuffleCut (0 : I) = 1 := by
  apply Subtype.ext
  norm_num [shuffleCut]

@[simp] theorem shuffleCut_one : shuffleCut (1 : I) = 0 := by
  apply Subtype.ext
  norm_num [shuffleCut]

/-- At p=0 the canonical map is exactly the identity. -/
theorem shufflePoint_zero (u : I) : shufflePoint 0 u = u := by
  apply Subtype.ext
  change shuffleReal 0 u = (u : ℝ)
  by_cases hu : u < (1 : I)
  · simp [shuffleReal, shuffleCut_zero, hu]
  · have he : u = 1 := le_antisymm u.property.2 (le_of_not_gt hu)
    subst u
    norm_num [shuffleReal, shuffleCut_zero]

/-- At p=1 the canonical map is exactly the coordinate reflection. -/
theorem shufflePoint_one (u : I) : shufflePoint 1 u = unitInterval.symm u := by
  apply Subtype.ext
  simp [shufflePoint, shuffleReal, shuffleCut_one, unitInterval.coe_symm_eq,
    not_lt.mpr u.property.1]

/-- Except at the split point, the exact involution is the printed map. -/
theorem shuffleReal_eq_printed_of_ne (p u : I)
    (h : u ≠ shuffleCut p) :
    shuffleReal p u = printedShuffleReal p u := by
  unfold shuffleReal printedShuffleReal
  by_cases hu : (u : ℝ) < (shuffleCut p : ℝ)
  · simp [hu, hu.le]
  · have hgt : (shuffleCut p : ℝ) < u := by
      have hne : (u : ℝ) ≠ (shuffleCut p : ℝ) :=
        fun he => h (Subtype.ext he)
      exact lt_of_le_of_ne (le_of_not_gt hu) hne.symm
    simp [hu, not_le.mpr hgt]

/-- The source and endpoint-safe formulas agree under the uniform law. -/
theorem shuffleReal_ae_printed (p : I) :
    shuffleReal p =ᵐ[volume] printedShuffleReal p := by
  filter_upwards [volume.ae_ne (shuffleCut p)] with u hu
  exact shuffleReal_eq_printed_of_ne p u hu

/-- The endpoint-safe upper-interval flip preserves uniform measure. -/
theorem shufflePoint_measurePreserving (p : I) :
    MeasurePreserving (shufflePoint p) volume volume := by
  refine ⟨measurable_shufflePoint p, ?_⟩
  apply Measure.ext_of_Iic
  intro v
  rw [Measure.map_apply (measurable_shufflePoint p) measurableSet_Iic]
  let c := shuffleCut p
  by_cases hv : v < c
  · have he : shufflePoint p ⁻¹' Iic v = Iic v := by
      ext u
      simp only [mem_preimage, mem_Iic]
      by_cases hu : u < c
      · have hf : shufflePoint p u = u := Subtype.ext (by
          simp [shufflePoint, shuffleReal, c, hu])
        simp [hf]
      · have hcu : c ≤ shufflePoint p u := by
          change (c : ℝ) ≤ shuffleReal p u
          change (c : ℝ) ≤
            (if (u : ℝ) < (c : ℝ) then (u : ℝ) else (c : ℝ) + 1 - u)
          rw [ite_eq_right (show ¬ (u : ℝ) < (c : ℝ) from hu)]
          linarith [u.property.2]
        exact ⟨fun h => False.elim ((not_le_of_gt hv) (hcu.trans h)),
          fun h => False.elim ((not_le_of_gt hv) ((le_of_not_gt hu).trans h))⟩
    rw [he]
  · have hcv : c ≤ v := le_of_not_gt hv
    have hcvR : (c : ℝ) ≤ (v : ℝ) := hcv
    let r : I := ⟨(c : ℝ) + 1 - v,
      ⟨by linarith [c.property.1, v.property.2], by linarith⟩⟩
    have hcr : c ≤ r := by change (c : ℝ) ≤ (c : ℝ) + 1 - v; linarith [v.property.2]
    have he : shufflePoint p ⁻¹' Iic v = Iio c ∪ Ici r := by
      ext u
      simp only [mem_preimage, mem_Iic, mem_union, mem_Iio, mem_Ici]
      by_cases hu : u < c
      · have hf : shufflePoint p u = u := Subtype.ext (by
          simp [shufflePoint, shuffleReal, c, hu])
        simp [hf, hu, hu.le.trans hcv, not_le.mpr (lt_of_lt_of_le hu hcr)]
      · have hcu : ¬ (u : ℝ) < (c : ℝ) := hu
        change (if (u : ℝ) < (c : ℝ) then (u : ℝ) else
          (c : ℝ) + 1 - u) ≤ v ↔ u < c ∨ r ≤ u
        rw [ite_eq_right hcu]
        simp only [hu, false_or]
        change (c : ℝ) + 1 - u ≤ v ↔ (c : ℝ) + 1 - v ≤ u
        constructor <;> intro h <;> linarith
    rw [he, measure_union]
    · rw [unitInterval.volume_Iio, unitInterval.volume_Ici, unitInterval.volume_Iic]
      have hr : 1 - (r : ℝ) = (v : ℝ) - c := by dsimp [r]; ring
      rw [hr, ← ENNReal.ofReal_add c.property.1 (sub_nonneg.mpr hcvR)]
      congr 1
      ring
    · exact disjoint_left.mpr (by
        intro u hu hr
        change u < c at hu
        change r ≤ u at hr
        exact (not_lt_of_ge (hcr.trans hr)) hu)
    · exact measurableSet_Ici


/-- Disintegration of a copula over any measurable first-coordinate
set, extending the usual lower-rectangle conditional-CDF identity. -/
theorem copula_measureReal_conditional_set (C : Copula 2)
    (s : Set I) (hs : MeasurableSet s) (v : I) :
    C.toMeasure.real {x | x 0 ∈ s ∧ x 1 ≤ v} =
      ∫ u in s, C.conditionalCDF u v := by
  have hm := compProd_map_condDistrib (μ := C.toMeasure) (mα := inferInstance)
    (mβ := inferInstance) (X := fun x : Fin 2 → I => x 0) (Y := fun x => x 1)
    (measurable_pi_apply 0).aemeasurable (measurable_pi_apply 1).aemeasurable
  rw [C.map_eval] at hm
  have h := congrArg (fun μ : Measure (I × I) => μ (s ×ˢ Iic v)) hm
  rw [Measure.compProd_apply_prod hs measurableSet_Iic,
    Measure.map_apply (by fun_prop) (hs.prod measurableSet_Iic)] at h
  have he : (fun x : Fin 2 → I => (x 0, x 1)) ⁻¹' (s ×ˢ Iic v) =
      {x | x 0 ∈ s ∧ x 1 ≤ v} := by
    ext x
    simp
  rw [he] at h
  unfold Copula.conditionalCDF Measure.real
  rw [integral_toReal (C.conditionalKernel.measurable_coe measurableSet_Iic).aemeasurable
    (Filter.Eventually.of_forall fun t => measure_lt_top _ _)]
  exact congrArg ENNReal.toReal h.symm

/-- Change of variables through the measure-preserving involution. -/
theorem shuffle_setIntegral (p : I) (s : Set I) (hs : MeasurableSet s)
    (g : I → ℝ) (hg : Measurable g) :
    (∫ u in s, g (shufflePoint p u)) =
      ∫ u in shufflePoint p ⁻¹' s, g u := by
  have h := setIntegral_map (μ := (volume : Measure I))
    (g := shufflePoint p) (f := fun y => g (shufflePoint p y))
    hs ((hg.comp (measurable_shufflePoint p)).aestronglyMeasurable)
    (measurable_shufflePoint p).aemeasurable
  rw [(shufflePoint_measurePreserving p).map_eq] at h
  simpa only [shufflePoint_involution] using h

/-- The source transformation applied to the first copula coordinate. -/
noncomputable def shuffleTransform (p : I) (x : Fin 2 → I) : Fin 2 → I :=
  ![shufflePoint p (x 0), x 1]

@[fun_prop] theorem measurable_shuffleTransform (p : I) :
    Measurable (shuffleTransform p) := by
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact (measurable_shufflePoint p).comp (measurable_pi_apply 0)
  · exact measurable_pi_apply 1

theorem shuffleTransform_zero (x : Fin 2 → I) : shuffleTransform 0 x = x := by
  funext i
  fin_cases i
  · simp [shuffleTransform, shufflePoint_zero]
  · simp [shuffleTransform]

theorem shuffleTransform_one (x : Fin 2 → I) :
    shuffleTransform 1 x = Copula.reflectPoint {0} x := by
  funext i
  fin_cases i
  · simp [shuffleTransform, shufflePoint_one, Copula.reflectPoint]
  · simp [shuffleTransform, Copula.reflectPoint]

/-- Pushforward law along the corrected shuffle, before proving uniformity
of its first marginal for every parameter. -/
noncomputable def shuffledLaw (C : Copula 2) (p : I) :
    Measure (Fin 2 → I) := C.toMeasure.map (shuffleTransform p)

theorem shuffledLaw_zero (C : Copula 2) : shuffledLaw C 0 = C.toMeasure := by
  have h : shuffleTransform 0 = id := funext (shuffleTransform_zero ·)
  simp [shuffledLaw, h]

theorem shuffledLaw_one (C : Copula 2) :
    shuffledLaw C 1 = (C.reflect {0}).toMeasure := by
  have h : shuffleTransform 1 = Copula.reflectPoint {0} :=
    funext shuffleTransform_one
  simp [shuffledLaw, h]

/-- Every parameter of the corrected shuffle is a copula: the first
marginal stays uniform by the interval-flip theorem, and the second
marginal is unchanged. No SI assumption is needed for this construction. -/
noncomputable def shuffledCopula (C : Copula 2) (p : I) : Copula 2 :=
  Copula.ofMap C.measure (shuffleTransform p) (measurable_shuffleTransform p) (by
    intro i
    fin_cases i
    · change C.toMeasure.map (fun x => shufflePoint p (x 0)) = volume
      calc
        C.toMeasure.map (fun x => shufflePoint p (x 0)) =
            (C.toMeasure.map (fun x => x 0)).map (shufflePoint p) := by
          rw [Measure.map_map (measurable_shufflePoint p) (measurable_pi_apply 0)]
          rfl
        _ = volume := by
          rw [C.map_eval 0]
          exact (shufflePoint_measurePreserving p).map_eq
    · change C.toMeasure.map (fun x => x 1) = volume
      exact C.map_eval 1)

theorem toMeasure_shuffledCopula (C : Copula 2) (p : I) :
    (shuffledCopula C p).toMeasure = shuffledLaw C p := rfl

/-- Corrected shuffling lemma (i), initial endpoint. -/
theorem shuffledCopula_zero (C : Copula 2) : shuffledCopula C 0 = C := by
  apply Copula.ext
  rw [toMeasure_shuffledCopula, shuffledLaw_zero]

/-- Corrected shuffling lemma (i), reflected endpoint. -/
theorem shuffledCopula_one (C : Copula 2) :
    shuffledCopula C 1 = C.reflect {0} := by
  apply Copula.ext
  rw [toMeasure_shuffledCopula, shuffledLaw_one]

/-- Conditional CDFs of the shuffle are obtained by composing the
original conditional CDF with the inverse first-coordinate map. -/
theorem shuffledCopula_conditionalCDF_ae (C : Copula 2) (p v : I) :
    (fun u => (shuffledCopula C p).conditionalCDF u v) =ᵐ[volume]
      fun u => C.conditionalCDF (shufflePoint p u) v := by
  apply Copula.conditionalCDF_ae_eq_of_integral
    (shuffledCopula C p) v
    ((shufflePoint_measurePreserving p).integrable_comp_of_integrable
      (C.integrable_conditionalCDF v))
    (fun u => C.conditionalCDF_nonneg (shufflePoint p u) v)
  intro u
  let s : Set I := shufflePoint p ⁻¹' Iic u
  have hs : MeasurableSet s :=
    measurableSet_Iic.preimage (measurable_shufflePoint p)
  have he : shuffleTransform p ⁻¹' Iic ![u,v] =
      {x : Fin 2 → I | x 0 ∈ s ∧ x 1 ≤ v} := by
    ext x
    simp [shuffleTransform, s, Pi.le_def, Fin.forall_fin_two]
  calc
    (∫ t in Iic u, C.conditionalCDF (shufflePoint p t) v) =
        ∫ t in s, C.conditionalCDF t v :=
      shuffle_setIntegral p (Iic u) measurableSet_Iic
        (fun t => C.conditionalCDF t v) (C.measurable_conditionalCDF_left v)
    _ = C.toMeasure.real {x | x 0 ∈ s ∧ x 1 ≤ v} :=
      (copula_measureReal_conditional_set C s hs v).symm
    _ = (shuffledCopula C p).cdf ![u,v] := by
      change (C.toMeasure {x | x 0 ∈ s ∧ x 1 ≤ v}).toReal =
        ((C.toMeasure.map (shuffleTransform p)) (Iic ![u,v])).toReal
      rw [Measure.map_apply (measurable_shuffleTransform p)
        measurableSet_Iic, he]

/-- Uniform integration is invariant under the exact shuffle. -/
theorem shuffle_integral_comp (p : I) (g : I → ℝ) :
    (∫ u : I, g (shufflePoint p u)) = ∫ u : I, g u := by
  let e : I ≃ᵐ I := MeasurableEquiv.ofInvolutive (shufflePoint p)
    (shufflePoint_involution p) (measurable_shufflePoint p)
  exact (shufflePoint_measurePreserving p).integral_comp e.measurableEmbedding g

/-- Corrected shuffling lemma (ii): any measurable rearrangement of the
conditioning coordinate by this involution preserves directional xi. -/
theorem shuffledCopula_xi (C : Copula 2) (p : I) :
    (shuffledCopula C p).chatterjeeXi = C.chatterjeeXi := by
  have hinner (v : I) :
      (∫ u : I, (shuffledCopula C p).conditionalCDF u v ^ 2) =
        ∫ u : I, C.conditionalCDF u v ^ 2 := by
    calc
      _ = ∫ u : I, C.conditionalCDF (shufflePoint p u) v ^ 2 := by
        apply integral_congr_ae
        filter_upwards [shuffledCopula_conditionalCDF_ae C p v] with u hu
        rw [hu]
      _ = _ := shuffle_integral_comp p (fun u => C.conditionalCDF u v ^ 2)
  unfold Copula.chatterjeeXi
  congr 2
  exact integral_congr_ae (Filter.Eventually.of_forall hinner)

/-- The shuffled CDF is an integral of the original conditional
section over the inverse image of its first-coordinate lower interval. -/
theorem shuffledCopula_cdf_setIntegral (C : Copula 2) (p u v : I) :
    (shuffledCopula C p).cdf ![u,v] =
      ∫ t in shufflePoint p ⁻¹' Iic u, C.conditionalCDF t v := by
  rw [(shuffledCopula C p).cdf_eq_integral_conditionalCDF]
  calc
    (∫ t in Iic u, (shuffledCopula C p).conditionalCDF t v) =
        ∫ t in Iic u, C.conditionalCDF (shufflePoint p t) v := by
      apply integral_congr_ae
      exact ae_restrict_of_ae (shuffledCopula_conditionalCDF_ae C p v)
    _ = _ := shuffle_setIntegral p (Iic u) measurableSet_Iic
      (fun t => C.conditionalCDF t v) (C.measurable_conditionalCDF_left v)

/-- Below the split, the shuffle leaves each lower rectangle unchanged. -/
theorem shuffledCopula_cdf_below_cut (C : Copula 2) (p u v : I)
    (hu : u < shuffleCut p) :
    (shuffledCopula C p).cdf ![u,v] = C.cdf ![u,v] := by
  rw [shuffledCopula_cdf_setIntegral]
  have he : shufflePoint p ⁻¹' Iic u = Iic u := by
    ext t
    simp only [mem_preimage, mem_Iic]
    by_cases ht : t < shuffleCut p
    · have hf : shufflePoint p t = t := Subtype.ext (by
        simp [shufflePoint, shuffleReal, ht])
      simp [hf]
    · have hct : shuffleCut p ≤ shufflePoint p t := by
        change (shuffleCut p : ℝ) ≤ shuffleReal p t
        simp only [shuffleReal, ite_eq_right (show ¬ (t : ℝ) <
          (shuffleCut p : ℝ) from ht)]
        linarith [t.property.2]
      exact ⟨fun h => False.elim ((not_le_of_gt hu) (hct.trans h)),
        fun h => False.elim ((not_le_of_gt hu) ((le_of_not_gt ht).trans h))⟩
  rw [he, ← C.cdf_eq_integral_conditionalCDF]

/-- Above the split, the CDF is the lower unflipped mass plus the
upper tail mass reflected from the source copula. -/
theorem shuffledCopula_cdf_above_cut (C : Copula 2) (p u v r : I)
    (hu : shuffleCut p ≤ u)
    (hr : (r : ℝ) = (shuffleCut p : ℝ) + 1 - u) :
    (shuffledCopula C p).cdf ![u,v] =
      C.cdf ![shuffleCut p,v] + (v : ℝ) - C.cdf ![r,v] := by
  let c := shuffleCut p
  have hcr : c ≤ r := by
    change (c : ℝ) ≤ (r : ℝ)
    rw [hr]
    linarith [u.property.2]
  rw [shuffledCopula_cdf_setIntegral]
  have he : shufflePoint p ⁻¹' Iic u = Iio c ∪ Ici r := by
    ext t
    simp only [mem_preimage, mem_Iic, mem_union, mem_Iio, mem_Ici]
    by_cases ht : t < c
    · have hf : shufflePoint p t = t := Subtype.ext (by
        simp [shufflePoint, shuffleReal, c, ht])
      simp [hf, ht, ht.le.trans hu, not_le.mpr (lt_of_lt_of_le ht hcr)]
    · change shuffleReal p t ≤ (u : ℝ) ↔ t < c ∨ r ≤ t
      have htc : ¬ (t : ℝ) < (c : ℝ) := ht
      change (if (t : ℝ) < (c : ℝ) then (t : ℝ) else
        (c : ℝ) + 1 - t) ≤ u ↔ t < c ∨ r ≤ t
      rw [ite_eq_right htc]
      simp only [ht, false_or]
      change (c : ℝ) + 1 - t ≤ u ↔ (r : ℝ) ≤ t
      rw [hr]
      constructor <;> intro h <;> linarith
  rw [he]
  have hg : Integrable (fun t : I => C.conditionalCDF t v) :=
    C.integrable_conditionalCDF v
  have hd : Disjoint (Iio c) (Ici r) := disjoint_left.mpr (by
    intro t ht hrt
    change t < c at ht
    change r ≤ t at hrt
    exact (not_lt_of_ge (hcr.trans hrt)) ht)
  rw [setIntegral_union hd measurableSet_Ici hg.integrableOn hg.integrableOn]
  have hc : (∫ t in Iio c, C.conditionalCDF t v) = C.cdf ![c,v] := by
    rw [← integral_Iic_eq_integral_Iio]
    exact (C.cdf_eq_integral_conditionalCDF c v).symm
  have hr' : (∫ t in Iio r, C.conditionalCDF t v) = C.cdf ![r,v] := by
    rw [← integral_Iic_eq_integral_Iio]
    exact (C.cdf_eq_integral_conditionalCDF r v).symm
  have hsplit : (∫ t in Iio r, C.conditionalCDF t v) +
      (∫ t in Ici r, C.conditionalCDF t v) =
        ∫ t : I, C.conditionalCDF t v := by
    rw [← setIntegral_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici
      hg.integrableOn hg.integrableOn, Iio_union_Ici, setIntegral_univ]
  rw [hc]
  change C.cdf ![c,v] + (∫ t in Ici r, C.conditionalCDF t v) =
    C.cdf ![c,v] + (v : ℝ) - C.cdf ![r,v]
  rw [← hr']
  rw [C.integral_conditionalCDF] at hsplit
  linarith

/-- Equal-length increments of an SI copula's concave CDF section
decrease as the interval moves right. The four-point form also covers
overlapping intervals. -/
theorem si_cdf_cross (C : Copula 2) (hC : C.IsSI)
    (a b c d v : I) (hab : a ≤ b) (hbd : b ≤ d)
    (hac : a ≤ c) (hcd : c ≤ d)
    (hsum : (a : ℝ) + d = (b : ℝ) + c) :
    C.cdf ![a,v] + C.cdf ![d,v] ≤
      C.cdf ![b,v] + C.cdf ![c,v] := by
  by_cases heq : a = d
  · have hb : b = a := le_antisymm (hbd.trans heq.symm.le) hab
    have hc : c = a := le_antisymm (hcd.trans heq.symm.le) hac
    subst d
    subst b
    subst c
    exact le_refl _
  · have hpos : 0 < (d : ℝ) - a := by
      have had : a < d := lt_of_le_of_ne (hab.trans hbd) heq
      exact sub_pos.mpr had
    have h1 := hC a b d v hab hbd
    have h2 := hC a c d v hac hcd
    have he1 : (((b : ℝ) + c) - a - d) * C.cdf ![a,v] = 0 := by
      rw [← hsum]
      ring
    have he2 : (((b : ℝ) + c) - a - d) * C.cdf ![d,v] = 0 := by
      rw [← hsum]
      ring
    have hp : 0 ≤ ((d : ℝ) - a) *
        (C.cdf ![b,v] + C.cdf ![c,v] -
          C.cdf ![a,v] - C.cdf ![d,v]) := by
      nlinarith [h1, h2, he1, he2]
    nlinarith

/-- Corrected shuffling lemma (iii): increasing the flipped upper
length decreases the copula in lower orthant order. -/
theorem shuffledCopula_lowerOrthant (C : Copula 2) (hC : C.IsSI)
    (p q : I) (hpq : q ≤ p) :
    (shuffledCopula C p).LowerOrthantLE (shuffledCopula C q) := by
  intro x
  let u := x 0
  let v := x 1
  have hx : x = ![u,v] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  let c := shuffleCut p
  let d := shuffleCut q
  have hcd : c ≤ d := by
    have hpqR : (q : ℝ) ≤ p := hpq
    change 1 - (p : ℝ) ≤ 1 - (q : ℝ)
    linarith
  by_cases huc : u < c
  · have hud : u < d := lt_of_lt_of_le huc hcd
    rw [shuffledCopula_cdf_below_cut C p u v huc,
      shuffledCopula_cdf_below_cut C q u v hud]
  have hcu : c ≤ u := le_of_not_gt huc
  have hcuR : (c : ℝ) ≤ u := hcu
  have hcdR : (c : ℝ) ≤ d := hcd
  by_cases hud : u < d
  · let r : I := ⟨(c : ℝ) + 1 - u,
      ⟨by linarith [c.property.1, u.property.2], by linarith [hcuR]⟩⟩
    have hr : (r : ℝ) = (c : ℝ) + 1 - u := rfl
    have hcr : c ≤ r := by change (c : ℝ) ≤ (r : ℝ); dsimp [r]; linarith [u.property.2]
    have hsum : (c : ℝ) + (1 : I) = (u : ℝ) + r := by dsimp [r]; ring
    have hcross := si_cdf_cross C hC c u r 1 v hcu u.property.2
      hcr r.property.2 hsum
    rw [shuffledCopula_cdf_above_cut C p u v r hcu hr,
      shuffledCopula_cdf_below_cut C q u v hud]
    simp only [Copula.cdf_two_one_left] at hcross
    linarith
  · have hdu : d ≤ u := le_of_not_gt hud
    have hduR : (d : ℝ) ≤ u := hdu
    let r : I := ⟨(c : ℝ) + 1 - u,
      ⟨by linarith [c.property.1, u.property.2], by linarith [hcuR]⟩⟩
    let t : I := ⟨(d : ℝ) + 1 - u,
      ⟨by linarith [d.property.1, u.property.2], by linarith [hduR]⟩⟩
    have hr : (r : ℝ) = (c : ℝ) + 1 - u := rfl
    have ht : (t : ℝ) = (d : ℝ) + 1 - u := rfl
    have hcr : c ≤ r := by change (c : ℝ) ≤ (r : ℝ); dsimp [r]; linarith [u.property.2]
    have hdt : d ≤ t := by change (d : ℝ) ≤ (t : ℝ); dsimp [t]; linarith [u.property.2]
    have hrt : r ≤ t := by change (r : ℝ) ≤ (t : ℝ); dsimp [r,t]; linarith [hcdR]
    have hsum : (c : ℝ) + t = (d : ℝ) + r := by dsimp [r,t]; ring
    have hcross := si_cdf_cross C hC c d r t v hcd hdt hcr hrt hsum
    rw [shuffledCopula_cdf_above_cut C p u v r hcu hr,
      shuffledCopula_cdf_above_cut C q u v t hdu ht]
    linarith

/-- The same corrected order in the source's concordance convention. -/
theorem shuffledCopula_concordance (C : Copula 2) (hC : C.IsSI)
    (p q : I) (hpq : q ≤ p) :
    (shuffledCopula C p).ConcordanceLE (shuffledCopula C q) :=
  (Copula.concordanceLE_iff_lowerOrthantLE _ _).mpr
    (shuffledCopula_lowerOrthant C hC p q hpq)

/-- A copula CDF is one-Lipschitz in its first coordinate. -/
theorem cdf_first_lipschitz (C : Copula 2) (a b v : I) :
    |C.cdf ![a,v] - C.cdf ![b,v]| ≤ |(a : ℝ) - b| := by
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, abs_zero, add_zero] using
      C.abs_cdf_sub_le_sum_abs ![a,v] ![b,v]

/-- For ordered parameters, every CDF value changes by at most twice
the parameter difference. This does not require SI. -/
theorem shuffledCopula_cdf_bound_ordered (C : Copula 2)
    (p q u v : I) (hpq : q ≤ p) :
    |(shuffledCopula C p).cdf ![u,v] -
      (shuffledCopula C q).cdf ![u,v]| ≤
        2 * ((p : ℝ) - q) := by
  let c := shuffleCut p
  let d := shuffleCut q
  have hpqR : (q : ℝ) ≤ p := hpq
  have hcd : c ≤ d := by
    change 1 - (p : ℝ) ≤ 1 - (q : ℝ)
    linarith
  have hcdR : (c : ℝ) ≤ d := hcd
  have hdelta : (d : ℝ) - c = (p : ℝ) - q := by
    change (1 - (q : ℝ)) - (1 - (p : ℝ)) = _
    ring
  rw [← hdelta]
  by_cases huc : u < c
  · have hud : u < d := lt_of_lt_of_le huc hcd
    rw [shuffledCopula_cdf_below_cut C p u v huc,
      shuffledCopula_cdf_below_cut C q u v hud, sub_self, abs_zero]
    linarith
  have hcu : c ≤ u := le_of_not_gt huc
  have hcuR : (c : ℝ) ≤ u := hcu
  by_cases hud : u < d
  · let r : I := ⟨(c : ℝ) + 1 - u,
      ⟨by linarith [c.property.1, u.property.2], by linarith [hcuR]⟩⟩
    have hr : (r : ℝ) = (c : ℝ) + 1 - u := rfl
    have h1 := cdf_first_lipschitz C c u v
    rw [abs_of_nonpos (sub_nonpos.mpr hcuR)] at h1
    have h2raw := cdf_first_lipschitz C 1 r v
    have h2 : |(v : ℝ) - C.cdf ![r,v]| ≤ 1 - r := by
      simpa only [Copula.cdf_two_one_left,
        show ((1 : I) : ℝ) = 1 by norm_num,
        abs_of_nonneg (sub_nonneg.mpr r.property.2)] using h2raw
    rw [shuffledCopula_cdf_above_cut C p u v r hcu hr,
      shuffledCopula_cdf_below_cut C q u v hud]
    have huR : (u : ℝ) ≤ d := hud.le
    have h1a := (abs_le.mp h1).1
    have h1b := (abs_le.mp h1).2
    have h2a := (abs_le.mp h2).1
    have h2b := (abs_le.mp h2).2
    apply abs_le.mpr
    constructor <;> linarith
  · have hdu : d ≤ u := le_of_not_gt hud
    have hduR : (d : ℝ) ≤ u := hdu
    let r : I := ⟨(c : ℝ) + 1 - u,
      ⟨by linarith [c.property.1, u.property.2], by linarith [hcuR]⟩⟩
    let t : I := ⟨(d : ℝ) + 1 - u,
      ⟨by linarith [d.property.1, u.property.2], by linarith [hduR]⟩⟩
    have hr : (r : ℝ) = (c : ℝ) + 1 - u := rfl
    have ht : (t : ℝ) = (d : ℝ) + 1 - u := rfl
    have h1 := cdf_first_lipschitz C c d v
    rw [abs_of_nonpos (sub_nonpos.mpr hcdR)] at h1
    have hrt : (r : ℝ) ≤ t := by dsimp [r,t]; linarith [hcdR]
    have h2 := cdf_first_lipschitz C r t v
    rw [abs_of_nonpos (sub_nonpos.mpr hrt)] at h2
    rw [shuffledCopula_cdf_above_cut C p u v r hcu hr,
      shuffledCopula_cdf_above_cut C q u v t hdu ht]
    have h1a := (abs_le.mp h1).1
    have h1b := (abs_le.mp h1).2
    have h2a := (abs_le.mp h2).1
    have h2b := (abs_le.mp h2).2
    apply abs_le.mpr
    constructor <;> linarith

/-- The uniform CDF bound for arbitrary parameter pairs. -/
theorem shuffledCopula_cdf_bound (C : Copula 2) (p q u v : I) :
    |(shuffledCopula C p).cdf ![u,v] -
      (shuffledCopula C q).cdf ![u,v]| ≤
        2 * |(p : ℝ) - q| := by
  rcases le_total q p with h | h
  · have hR : (q : ℝ) ≤ p := h
    rw [abs_of_nonneg (sub_nonneg.mpr hR)]
    exact shuffledCopula_cdf_bound_ordered C p q u v h
  · have hR : (p : ℝ) ≤ q := h
    have hb := shuffledCopula_cdf_bound_ordered C q p u v h
    rw [abs_of_nonpos (sub_nonpos.mpr hR)]
    rw [abs_sub_comm]
    linarith [hb]

/-- Corrected shuffling lemma (iv), in a quantitative uniform-CDF form.
The same parameter modulus works at every point of the closed square. -/
theorem shuffledCopula_uniformCDF_continuous (C : Copula 2) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ p q : I,
        |(p : ℝ) - q| < δ →
          ∀ x : Fin 2 → I,
            |(shuffledCopula C p).cdf x -
              (shuffledCopula C q).cdf x| < ε := by
  intro ε hε
  refine ⟨ε / 2, by linarith, ?_⟩
  intro p q hpq x
  have hx : x = ![x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  have hb := shuffledCopula_cdf_bound C p q (x 0) (x 1)
  linarith

/-- The boundary convention used in the source changes no transformed
copula law because every copula has a uniform, atomless first marginal. -/
theorem shuffleReal_ae_printed_copula (C : Copula 2) (p : I) :
    ∀ᵐ x ∂C.toMeasure,
      (shufflePoint p (x 0) : ℝ) = printedShuffleReal p (x 0) := by
  filter_upwards [C.ae_eval_ne 0 (shuffleCut p)] with x hx
  exact shuffleReal_eq_printed_of_ne p (x 0) hx

end Papers.Rockel2026XiBlest
