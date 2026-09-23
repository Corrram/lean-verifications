import Papers.Rockel2026XiBlest.FamilyOrder
import Papers.Rockel2026XiBlest.SubstitutionFormulas
import Verification.QuadraticBandTP2

/-! # The revised manuscript's positive-parameter MTP2 assertion -/

open MeasureTheory ProbabilityTheory Verification Set
open scoped unitInterval

namespace Papers.Rockel2026XiBlest

/-- A concrete Lebesgue density for the extremal copula, obtained by standardizing
the second marginal of the increasing band law. The revision's formula in
terms of the derivative of q remains a separate identification obligation. -/
theorem extremal_standardized_density (b : ℝ) (hb : 0 ≤ b) :
    (extremalCopula b hb).toMeasure =
      (volume : Measure (Fin 2 → I)).withDensity
        (fun x => ENNReal.ofReal
          ((quadraticRawBand b hb).standardizedDensity (x 0, x 1))) := by
  rw [extremalCopula, ← quadraticRawBand_copula b hb]
  exact (quadraticRawBand b hb).copula_density

/-- Every finite nonnegative member has an actual Lebesgue MTP2 density. -/
theorem extremal_hasMTP2Density (b : ℝ) (hb : 0 ≤ b) :
    (extremalCopula b hb).HasMTP2Density := quadraticBand_hasMTP2Density b hb

/-- Positive signed parameters give the same density-certified copulas. -/
theorem signed_extremal_hasMTP2Density (b : ℝ) (hb : 0 < b) :
    (signedExtremalCopula b).HasMTP2Density := by
  rw [signedExtremal_nonneg b hb.le]
  exact extremal_hasMTP2Density b hb.le

/-- The two switch points in the revised manuscript, expressed using the
unclamped band endpoints. -/
noncomputable def extremalLowerSwitch (b : ℝ) (hb : 0 < b) (v : I) : ℝ :=
  1 - quadraticUpper b (extremalQ b hb v)

noncomputable def extremalUpperSwitch (b : ℝ) (hb : 0 < b) (v : I) : ℝ :=
  1 - quadraticLower (extremalQ b hb v)

theorem extremalLowerSwitch_source (b : ℝ) (hb : 0 < b) (v : I) :
    extremalLowerSwitch b hb v =
      max 0 (1 - Real.sqrt (extremalQ b hb v + 1/b)) := by
  unfold extremalLowerSwitch quadraticUpper
  rcases le_total 1 (Real.sqrt (extremalQ b hb v + 1/b)) with h | h
  · rw [min_eq_left h]
    rw [max_eq_left (by linarith : 1 - Real.sqrt (extremalQ b hb v + 1/b) ≤ 0)]
    ring
  · rw [min_eq_right h]
    rw [max_eq_right (by linarith : 0 ≤ 1 - Real.sqrt (extremalQ b hb v + 1/b))]

theorem extremalUpperSwitch_source (b : ℝ) (hb : 0 < b) (v : I) :
    extremalUpperSwitch b hb v =
      if 0 < extremalQ b hb v then
        1 - Real.sqrt (extremalQ b hb v) else 1 := by
  unfold extremalUpperSwitch quadraticLower
  split_ifs with h
  · rw [max_eq_right h.le]
  · rw [max_eq_left (le_of_not_gt h)]
    simp

/-- The manuscript's open support band is exactly the reflection of the
active interval in the clamped-square normalization integral. -/
theorem extremal_switch_support (b : ℝ) (hb : 0 < b) (v u : I) :
    (extremalLowerSwitch b hb v < (u : ℝ) ∧
      (u : ℝ) < extremalUpperSwitch b hb v) ↔
    (quadraticLower (extremalQ b hb v) < 1 - (u : ℝ) ∧
      1 - (u : ℝ) < quadraticUpper b (extremalQ b hb v)) := by
  unfold extremalLowerSwitch extremalUpperSwitch
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The nonnegative reciprocal-width form of the density printed in the
revision. Its equality with the copula's measure is still to be shown. -/
noncomputable def extremalWidthDensity (b : ℝ) (hb : 0 < b)
    (x : Fin 2 → I) : ℝ :=
  if extremalLowerSwitch b hb (x 1) < (x 0 : ℝ) ∧
      (x 0 : ℝ) < extremalUpperSwitch b hb (x 1) then
    (quadraticUpper b (extremalQ b hb (x 1)) -
      quadraticLower (extremalQ b hb (x 1)))⁻¹
  else 0

/-- The exact derivative-based expression appearing in the revised lemma. -/
noncomputable def extremalDerivativeDensity (b : ℝ) (hb : 0 < b)
    (x : Fin 2 → I) : ℝ :=
  if extremalLowerSwitch b hb (x 1) < (x 0 : ℝ) ∧
      (x 0 : ℝ) < extremalUpperSwitch b hb (x 1) then
    -b * deriv (extremalQExtension b hb) (x 1 : ℝ)
  else 0

theorem extremalDerivativeDensity_eq_width_of_interior (b : ℝ) (hb : 0 < b)
    (x : Fin 2 → I) (hv : (x 1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1) :
    extremalDerivativeDensity b hb x = extremalWidthDensity b hb x := by
  unfold extremalDerivativeDensity extremalWidthDensity
  split_ifs with h
  · simpa only [one_div] using extremalQExtension_density_coefficient b hb (x 1) hv
  · rfl

/-- The derivative-based formula and reciprocal-width candidate agree
almost everywhere on the square; only the second-coordinate endpoints
are excluded. -/
theorem extremalDerivativeDensity_ae_eq_width (b : ℝ) (hb : 0 < b) :
    extremalDerivativeDensity b hb =ᵐ[volume] extremalWidthDensity b hb := by
  have hm : MeasurableSet {p : I × I | (p.2 : ℝ) ∈ Ioo (0 : ℝ) 1} :=
    measurableSet_Ioo.preimage (measurable_subtype_coe.comp measurable_snd)
  have hp : ∀ᵐ p : I × I, (p.2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    exact Filter.Eventually.of_forall fun u => by
      filter_upwards [volume.ae_ne (0 : I), volume.ae_ne (1 : I)] with v hv0 hv1
      exact ⟨lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv0 (Subtype.ext h))),
        lt_of_le_of_ne v.property.2 (fun h => hv1 (Subtype.ext h))⟩
  have hc := (volume_preserving_finTwoArrow I).quasiMeasurePreserving.ae hp
  filter_upwards [hc] with x hx
  exact extremalDerivativeDensity_eq_width_of_interior b hb x hx

theorem extremalWidthDensity_nonneg (b : ℝ) (hb : 0 < b)
    (x : Fin 2 → I) : 0 ≤ extremalWidthDensity b hb x := by
  unfold extremalWidthDensity
  split_ifs with h
  · have hs : quadraticLower (extremalQ b hb (x 1)) <
        quadraticUpper b (extremalQ b hb (x 1)) := by
      unfold extremalLowerSwitch extremalUpperSwitch at h
      linarith
    exact inv_nonneg.mpr (sub_pos.mpr hs).le
  · exact le_refl 0

theorem extremalWidthDensity_measurable (b : ℝ) (hb : 0 < b) :
    Measurable (extremalWidthDensity b hb) := by
  have hq : Measurable (fun x : Fin 2 → I => extremalQ b hb (x 1)) :=
    (extremalQ_continuous b hb).measurable.comp (measurable_pi_apply 1)
  have hl : Measurable (fun x : Fin 2 → I =>
      1 - min 1 (Real.sqrt (extremalQ b hb (x 1) + 1/b))) := by
    fun_prop
  have hu : Measurable (fun x : Fin 2 → I =>
      1 - Real.sqrt (max 0 (extremalQ b hb (x 1)))) := by
    fun_prop
  have hw : Measurable (fun x : Fin 2 → I =>
      (min 1 (Real.sqrt (extremalQ b hb (x 1) + 1/b)) -
        Real.sqrt (max 0 (extremalQ b hb (x 1))))⁻¹) := by
    fun_prop
  have hx : Measurable (fun x : Fin 2 → I => (x 0 : ℝ)) := by
    fun_prop
  have hs : MeasurableSet {x : Fin 2 → I |
      (1 - min 1 (Real.sqrt (extremalQ b hb (x 1) + 1/b))) < (x 0 : ℝ) ∧
        (x 0 : ℝ) < (1 - Real.sqrt (max 0 (extremalQ b hb (x 1))))} :=
    (measurableSet_lt hl hx).inter (measurableSet_lt hx hu)
  unfold extremalWidthDensity extremalLowerSwitch extremalUpperSwitch
    quadraticUpper quadraticLower
  exact Measurable.ite hs hw measurable_const

end Papers.Rockel2026XiBlest
