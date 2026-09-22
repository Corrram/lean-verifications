import Papers.AnsariRockel2026XiRho.BandDensity

/-! # The open-band density convention in source equation (23) -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

/-- Exactly the open-band convention in equation (23). -/
noncomputable def sourceBandDensityOpen (b : ℝ) (x : Fin 2 → I) : ℝ :=
  if b*(x 0 : ℝ) < sourceBandIntercept b (x 1) ∧
    sourceBandIntercept b (x 1) < b*(x 0 : ℝ)+1 then sourceBandHeight b (x 1) else 0

theorem sourceBandDensityOpen_measurable {b : ℝ} (hb : 0 < b) : Measurable (sourceBandDensityOpen b) := by
  have ha := (sourceBandIntercept_monotone hb).measurable
  have hw : Measurable (sourceBandHeight b) := by
    unfold sourceBandHeight sqrtSlope
    apply Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const) (by fun_prop)
    exact Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
      measurable_const (by fun_prop)
  unfold sourceBandDensityOpen
  apply Measurable.ite
  · exact (measurableSet_lt (by fun_prop) (ha.comp (measurable_pi_apply 1))).inter
      (measurableSet_lt (ha.comp (measurable_pi_apply 1)) (by fun_prop))
  · exact hw.comp (measurable_pi_apply 1)
  · exact measurable_const

/-- The two versions differ only on a null boundary curve. -/
theorem sourceBandDensityOpen_ae_eq {b : ℝ} (hb : 0 < b) :
    sourceBandDensityOpen b =ᵐ[volume] sourceBandDensity b := by
  have ha := (sourceBandIntercept_monotone hb).measurable
  have hp : ∀ᵐ p : I × I, sourceBandIntercept b p.2 ≠ b*(p.1 : ℝ)+1 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_eq_fun (ha.comp measurable_snd) (by fun_prop)).compl)).mpr
    apply Filter.Eventually.of_forall
    intro u
    have hs : {v : I | sourceBandIntercept b v = b*(u : ℝ)+1}.Subsingleton := by
      intro v hv w hw
      exact (sourceBandIntercept_strictMono hb).injective (hv.trans hw.symm)
    exact (ae_iff).mpr (by simpa only [not_not, Set.mem_ofPred_eq, Function.comp_apply, Prod.snd, Prod.fst] using hs.countable.measure_zero (volume : Measure I))
  have hc := (volume_preserving_finTwoArrow I).quasiMeasurePreserving.ae hp
  filter_upwards [hc] with x hx
  change sourceBandIntercept b (x 1) ≠ b*(x 0 : ℝ)+1 at hx
  unfold sourceBandDensityOpen sourceBandDensity
  have he : sourceBandIntercept b (x 1) < b*(x 0 : ℝ)+1 ↔
      sourceBandIntercept b (x 1) ≤ b*(x 0 : ℝ)+1 := lt_iff_le_and_ne.trans (and_iff_left hx)
  simp only [he]

/-- The actual copula also has precisely the source's open-band density version. -/
theorem sourceBand_toMeasure_densityOpen (b : ℝ) (hb : 0 < b) :
    (sourceBand b hb).toMeasure =
      (volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (sourceBandDensityOpen b x)) := by
  rw [sourceBand_toMeasure_density]
  apply withDensity_congr_ae
  exact (sourceBandDensityOpen_ae_eq hb).symm.fun_comp ENNReal.ofReal

/-- Equation (24), expressed using the source's explicit square roots. -/
theorem sourceBandDensityOpen_formula (b : ℝ) (x : Fin 2 → I) :
    sourceBandDensityOpen b x =
      if b*(x 0 : ℝ) < sourceBandIntercept b (x 1) ∧ sourceBandIntercept b (x 1) < b*(x 0 : ℝ)+1 then
        if (x 1 : ℝ) ≤ bandCut b then b/Real.sqrt (2*b*(x 1 : ℝ))
        else if (x 1 : ℝ) ≤ 1-bandCut b then max b 1
        else b/Real.sqrt (2*b*(1-(x 1 : ℝ)))
      else 0 := rfl

end Papers.AnsariRockel2026XiRho
