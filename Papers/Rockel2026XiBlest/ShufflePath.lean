import Papers.Rockel2026XiBlest.ExtremalFamily
import Copula.Reflection

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

/-- The boundary convention used in the source changes no transformed
copula law because every copula has a uniform, atomless first marginal. -/
theorem shuffleReal_ae_printed_copula (C : Copula 2) (p : I) :
    ∀ᵐ x ∂C.toMeasure,
      (shufflePoint p (x 0) : ℝ) = printedShuffleReal p (x 0) := by
  filter_upwards [C.ae_eval_ne 0 (shuffleCut p)] with x hx
  exact shuffleReal_eq_printed_of_ne p (x 0) hx

end Papers.Rockel2026XiBlest
