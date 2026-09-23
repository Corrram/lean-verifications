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

/-- The quantile used by the already verified standardized-band density
has exactly the manuscript's normalization parameter. -/
theorem extremal_raw_quantile_parameter (b : ℝ) (hb : 0 < b) (v : I) :
    (b+1) * (unitQuantile (quadraticRawBand b hb.le).marginal v : ℝ) - b =
      -b * extremalQ b hb v := by
  let t := unitQuantile (quadraticRawBand b hb.le).marginal v
  have hm : quadraticMean b ((b+1)*(t : ℝ)-b) = (v : ℝ) := by
    have hh := unitCDF_quantile (quadraticRawBand b hb.le).marginal v
    rw [quadraticRawBand_marginal] at hh
    exact congrArg ((↑) : I → ℝ) hh
  have ha : (b+1)*(t : ℝ)-b = quadraticIntercept b hb.le v := by
    apply (quadraticMean_strictMonoOn hb.le).injOn
      (quadraticRawBand_intercept_mem b hb.le t)
      (quadraticIntercept_mem b hb.le v)
    rw [hm, quadraticIntercept_mean]
  rw [ha]
  unfold extremalQ
  field_simp

/-- The raw band's closed-strip condition is the clamped quadratic's
active interval, before switching to the manuscript's open-band version. -/
theorem extremal_raw_band_condition (b : ℝ) (hb : 0 < b) (v u : I) :
    let B := quadraticRawBand b hb.le
    let t := unitQuantile B.marginal v
    (B.lower u ≤ (t : ℝ) ∧ (t : ℝ) ≤ B.lower u + B.width) ↔
      (0 ≤ b * ((1-(u : ℝ))^2 - extremalQ b hb v) ∧
        b * ((1-(u : ℝ))^2 - extremalQ b hb v) ≤ 1) := by
  dsimp
  let B := quadraticRawBand b hb.le
  let t := unitQuantile B.marginal v
  have hw : 0 < B.width := B.width_pos
  have hr := quadraticRawBand_ratio b hb.le t u
  have hp := extremal_raw_quantile_parameter b hb v
  change ((t : ℝ) - B.lower u) / B.width =
    ((b+1)*(t : ℝ)-b) + b*(1-(u : ℝ))^2 at hr
  rw [hp] at hr
  constructor
  · rintro ⟨hlo, hhi⟩
    have hz : 0 ≤ ((t : ℝ) - B.lower u) / B.width :=
      div_nonneg (sub_nonneg.mpr hlo) hw.le
    have ho : ((t : ℝ) - B.lower u) / B.width ≤ 1 :=
      (div_le_one hw).mpr (by linarith)
    rw [hr] at hz ho
    constructor <;> nlinarith
  · rintro ⟨hz, ho⟩
    have hz' : 0 ≤ ((t : ℝ) - B.lower u) / B.width := by
      rw [hr]
      nlinarith
    have ho' : ((t : ℝ) - B.lower u) / B.width ≤ 1 := by
      rw [hr]
      nlinarith
    constructor
    · have h := (le_div_iff₀ hw).mp hz'
      linarith
    · have h := (div_le_one hw).mp ho'
      linarith

/-- At the marginal quantile for v, the raw band's column density is
(b+1) times the length of the manuscript's active interval. -/
theorem extremal_raw_columnDensity (b : ℝ) (hb : 0 < b) (v : I) :
    let B := quadraticRawBand b hb.le
    B.columnDensity (unitQuantile B.marginal v) =
      (b+1) * (quadraticUpper b (extremalQ b hb v) -
        quadraticLower (extremalQ b hb v)) := by
  dsimp
  let B := quadraticRawBand b hb.le
  let t := unitQuantile B.marginal v
  have hw : 1/B.width = b+1 := by
    change 1/(1/(b+1)) = b+1
    field_simp
  have hq : extremalQ b hb v ∈ Icc (-1/b) (1 : ℝ) := by
    have ha := quadraticIntercept_mem b hb.le v
    unfold extremalQ
    constructor
    · apply (div_le_div_iff_of_pos_right hb).mpr
      linarith [ha.2]
    · apply (div_le_one hb).mpr
      linarith [ha.1]
  have hf : (fun u : I => B.density (u,t)) =
      fun u : I => (b+1) * (if 0 ≤ b*((1-(u : ℝ))^2-extremalQ b hb v) ∧
          b*((1-(u : ℝ))^2-extremalQ b hb v) ≤ 1 then (1 : ℝ) else 0) := by
    funext u
    have hc := extremal_raw_band_condition b hb v u
    change (B.lower u ≤ (t : ℝ) ∧ (t : ℝ) ≤ B.lower u+B.width) ↔
      (0 ≤ b*((1-(u : ℝ))^2-extremalQ b hb v) ∧
        b*((1-(u : ℝ))^2-extremalQ b hb v) ≤ 1) at hc
    change (if B.lower u ≤ (t : ℝ) ∧ (t : ℝ) ≤ B.lower u+B.width
      then 1/B.width else 0) = _
    by_cases h : B.lower u ≤ (t : ℝ) ∧ (t : ℝ) ≤ B.lower u+B.width
    · simp only [ite_eq_left h, ite_eq_left (hc.mp h), mul_one, hw]
    · simp only [ite_eq_right h, ite_eq_right (fun hh => h (hc.mpr hh)), mul_zero]
  rw [IncreasingBand.columnDensity, hf, integral_const_mul,
    quadratic_closed_active_reflected_integral b (extremalQ b hb v) hb hq]

/-- For interior v, the raw band's closed-strip predicate agrees almost
everywhere in u with the manuscript's open switching band. -/
theorem extremal_raw_support_ae (b : ℝ) (hb : 0 < b) (v : I)
    (hv : (v : ℝ) ∈ Ioo (0 : ℝ) 1) :
    let B := quadraticRawBand b hb.le
    let t := unitQuantile B.marginal v
    ∀ᵐ u : I, (B.lower u ≤ (t : ℝ) ∧
        (t : ℝ) ≤ B.lower u+B.width) ↔
      (extremalLowerSwitch b hb v < (u : ℝ) ∧
        (u : ℝ) < extremalUpperSwitch b hb v) := by
  dsimp
  let B := quadraticRawBand b hb.le
  let t := unitQuantile B.marginal v
  let q := extremalQ b hb v
  have hq := extremalQ_interior b hb v hv
  have hsq0 := unitInterval.measurePreserving_symm.quasiMeasurePreserving.ae
    (square_ae_ne q)
  have hsq1 := unitInterval.measurePreserving_symm.quasiMeasurePreserving.ae
    (square_ae_ne (q+1/b))
  filter_upwards [volume.ae_ne (0 : I), volume.ae_ne (1 : I), hsq0, hsq1]
    with u hu0 hu1 hs0 hs1
  simp only [unitInterval.coe_symm_eq] at hs0 hs1
  have hup : 0 < (u : ℝ) :=
    lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have hul : (u : ℝ) < 1 :=
    lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))
  have ht : 1-(u : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  let z := b*((1-(u : ℝ))^2-q)
  have hz0 : z ≠ 0 := mul_ne_zero hb.ne' (sub_ne_zero.mpr hs0)
  have hz1 : z ≠ 1 := by
    intro he
    apply hs1
    have hdiv : (1-(u : ℝ))^2-q=1/b :=
      (eq_div_iff hb.ne').mpr (by nlinarith [he])
    linarith
  have hclosed : (0 ≤ z ∧ z ≤ 1) ↔ (0 < z ∧ z < 1) := by
    constructor
    · rintro ⟨hlo,hhi⟩
      exact ⟨lt_of_le_of_ne hlo (Ne.symm hz0),
        lt_of_le_of_ne hhi hz1⟩
    · rintro ⟨hlo,hhi⟩
      exact ⟨hlo.le,hhi.le⟩
  have hraw := extremal_raw_band_condition b hb v u
  change (B.lower u ≤ (t : ℝ) ∧ (t : ℝ) ≤ B.lower u+B.width) ↔
    (0 ≤ z ∧ z ≤ 1) at hraw
  exact hraw.trans (hclosed.trans
    ((quadratic_active_iff_switch b q (1-(u : ℝ)) hb
      ⟨hq.1.le,hq.2.le⟩ ht).trans
      (extremal_switch_support b hb v u).symm))

/-- The nonnegative reciprocal-width form of the density printed in the
revision. Its equality with the copula measure is proved below. -/
noncomputable def extremalWidthDensity (b : ℝ) (hb : 0 < b)
    (x : Fin 2 → I) : ℝ :=
  if extremalLowerSwitch b hb (x 1) < (x 0 : ℝ) ∧
      (x 0 : ℝ) < extremalUpperSwitch b hb (x 1) then
    (quadraticUpper b (extremalQ b hb (x 1)) -
      quadraticLower (extremalQ b hb (x 1)))⁻¹
  else 0

/-- Once their support predicates agree, the standardized density and the
reciprocal-width source candidate agree pointwise. -/
theorem extremal_standardized_eq_width_of_support (b : ℝ) (hb : 0 < b)
    (v u : I) (hv : (v : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hs : let B := quadraticRawBand b hb.le
      let t := unitQuantile B.marginal v
      (B.lower u ≤ (t : ℝ) ∧ (t : ℝ) ≤ B.lower u+B.width) ↔
        (extremalLowerSwitch b hb v < (u : ℝ) ∧
          (u : ℝ) < extremalUpperSwitch b hb v)) :
    (quadraticRawBand b hb.le).standardizedDensity (u,v) =
      extremalWidthDensity b hb ![u,v] := by
  classical
  let B := quadraticRawBand b hb.le
  let t := unitQuantile B.marginal v
  have hw : 1/B.width = b+1 := by
    change 1/(1/(b+1)) = b+1
    field_simp
  have hq := extremalQ_interior b hb v hv
  have hL := quadratic_switch_strict b (extremalQ b hb v) hb hq
  have hcol := extremal_raw_columnDensity b hb v
  change B.columnDensity t =
    (b+1)*(quadraticUpper b (extremalQ b hb v) -
      quadraticLower (extremalQ b hb v)) at hcol
  change (B.density (u,t)) / B.columnDensity t = _
  rw [hcol]
  unfold extremalWidthDensity
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change (if B.lower u ≤ (t : ℝ) ∧ (t : ℝ) ≤ B.lower u+B.width
    then 1/B.width else 0) /
      ((b+1)*(quadraticUpper b (extremalQ b hb v) -
        quadraticLower (extremalQ b hb v))) =
    (if extremalLowerSwitch b hb v < (u : ℝ) ∧
        (u : ℝ) < extremalUpperSwitch b hb v then
      (quadraticUpper b (extremalQ b hb v) -
        quadraticLower (extremalQ b hb v))⁻¹ else 0)
  by_cases h : B.lower u ≤ (t : ℝ) ∧ (t : ℝ) ≤ B.lower u+B.width
  · rw [ite_eq_left h, ite_eq_left (hs.mp h), hw]
    have hbp : b+1 ≠ 0 := by linarith
    have hln : quadraticUpper b (extremalQ b hb v) -
        quadraticLower (extremalQ b hb v) ≠ 0 :=
      ne_of_gt (sub_pos.mpr hL)
    field_simp
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (hs.mpr hh))]
    simp

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

/-- The source's reciprocal-width density candidate is the same
Lebesgue density as the verified standardized-band witness, up to a null
set of switching curves and response endpoints. -/
theorem extremalWidthDensity_ae_standardized (b : ℝ) (hb : 0 < b) :
    extremalWidthDensity b hb =ᵐ[volume]
      fun x : Fin 2 → I =>
        (quadraticRawBand b hb.le).standardizedDensity (x 0,x 1) := by
  let B := quadraticRawBand b hb.le
  have hmeas : Measurable (fun p : I × I =>
      extremalWidthDensity b hb ![p.1,p.2]) :=
    (extremalWidthDensity_measurable b hb).comp (by fun_prop)
  have hm : MeasurableSet {p : I × I |
      extremalWidthDensity b hb ![p.1,p.2] = B.standardizedDensity p} :=
    measurableSet_eq_fun hmeas B.standardizedDensity_measurable
  have hp : (fun p : I × I => extremalWidthDensity b hb ![p.1,p.2])
      =ᵐ[volume] B.standardizedDensity := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    apply (Measure.ae_ae_comm hm).mpr
    filter_upwards [volume.ae_ne (0 : I), volume.ae_ne (1 : I)] with v hv0 hv1
    have hv : (v : ℝ) ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv0 (Subtype.ext h))),
        lt_of_le_of_ne v.property.2 (fun h => hv1 (Subtype.ext h))⟩
    filter_upwards [extremal_raw_support_ae b hb v hv] with u hs
    exact (extremal_standardized_eq_width_of_support b hb v u hv hs).symm
  have hc := (volume_preserving_finTwoArrow I).quasiMeasurePreserving.ae hp
  filter_upwards [hc] with x hx
  have he : x = ![x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  simpa only [MeasurableEquiv.finTwoArrow_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] using hx

/-- The revised manuscript's reciprocal-width expression is the density
of the Xi–Blest copula measure, with equality of measures rather than
merely a formal candidate formula. -/
theorem extremal_toMeasure_widthDensity (b : ℝ) (hb : 0 < b) :
    (extremalCopula b hb.le).toMeasure =
      (volume : Measure (Fin 2 → I)).withDensity
        (fun x => ENNReal.ofReal (extremalWidthDensity b hb x)) := by
  rw [extremal_standardized_density b hb.le]
  apply withDensity_congr_ae
  exact (extremalWidthDensity_ae_standardized b hb).symm.fun_comp ENNReal.ofReal

/-- The revised manuscript's derivative form of the density is the
actual Xi–Blest copula density almost everywhere. -/
theorem extremal_toMeasure_derivativeDensity (b : ℝ) (hb : 0 < b) :
    (extremalCopula b hb.le).toMeasure =
      (volume : Measure (Fin 2 → I)).withDensity
        (fun x => ENNReal.ofReal (extremalDerivativeDensity b hb x)) := by
  rw [extremal_toMeasure_widthDensity b hb]
  apply withDensity_congr_ae
  exact (extremalDerivativeDensity_ae_eq_width b hb).symm.fun_comp ENNReal.ofReal

end Papers.Rockel2026XiBlest
