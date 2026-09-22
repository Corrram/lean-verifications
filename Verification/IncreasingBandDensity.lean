import Verification.IncreasingBandMarginal
import Verification.ExclusionBandDensity

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval ENNReal

namespace Verification

namespace IncreasingBand

variable (B : IncreasingBand)

noncomputable def marginal : Measure I := B.measure.map Prod.snd

instance : IsProbabilityMeasure B.marginal := by unfold marginal; infer_instance

instance : NullSingletonClass B.marginal := by
  constructor
  intro t
  rw [marginal,B.map_snd]
  exact withDensity_absolutelyContinuous volume _ (measure_singleton t)

theorem marginal_real : B.marginal.map ((↑) : I → ℝ)=B.secondLaw := by
  rw [marginal,Measure.map_map measurable_subtype_coe measurable_snd]
  rfl

theorem marginal_cdf (t : I) : unitCDF B.marginal t=cdfUnit B.secondLaw t := by
  rw [unitCDF_eq,B.marginal_real]

/-- The numerator vanishes almost everywhere on zero-density marginal fibers. -/
theorem density_zero_ae : ∀ᵐ p : I × I, B.columnDensity p.2=0 → B.density p=0 := by
  have hm : MeasurableSet {p : I × I | B.columnDensity p.2=0 → B.density p=0} :=
    by
      simp only [imp_iff_not_or]
      exact ((measurableSet_eq_fun (B.columnDensity_measurable.comp measurable_snd) measurable_const).compl).union
        (measurableSet_eq_fun B.density_measurable measurable_const)
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  apply (Measure.ae_ae_comm hm).mpr
  filter_upwards with t
  by_cases ht : B.columnDensity t=0
  · have hi : Integrable (fun u : I => B.density (u,t)) :=
      (integrable_const (1/B.width)).mono' (B.density_measurable.comp (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun u => by rw [Real.norm_eq_abs,abs_of_nonneg (B.density_mem (u,t)).1]; exact (B.density_mem (u,t)).2)
    have hz := (integral_eq_zero_iff_of_nonneg (fun u => (B.density_mem (u,t)).1) hi).mp ht
    filter_upwards [hz] with u hu using fun _ => hu
  · exact Eventually.of_forall fun _ h => (ht h).elim

noncomputable def conditionalDensity (p : I × I) : ℝ := B.density p/B.columnDensity p.2

theorem conditionalDensity_measurable : Measurable B.conditionalDensity :=
  B.density_measurable.div (B.columnDensity_measurable.comp measurable_snd)

/-- Disintegration as a density relative to the product of the two marginals. -/
theorem measure_eq_conditional : B.measure=
    ((volume : Measure I).prod B.marginal).withDensity (fun p => ENNReal.ofReal (B.conditionalDensity p)) := by
  have hq : Measurable (fun p : I × I => ENNReal.ofReal (B.columnDensity p.2)) :=
    (B.columnDensity_measurable.comp measurable_snd).ennreal_ofReal
  rw [marginal,B.map_snd,prod_withDensity_right B.columnDensity_measurable.ennreal_ofReal,
    ← withDensity_mul _ hq B.conditionalDensity_measurable.ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [B.density_zero_ae] with p hp
  simp only [Pi.mul_apply,conditionalDensity]
  rw [← ENNReal.ofReal_mul (B.columnDensity_nonneg p.2)]
  congr 1
  by_cases hq : B.columnDensity p.2=0
  · rw [hq,hp hq]; simp
  · rw [← mul_div_assoc,mul_div_cancel_left₀ _ hq]

noncomputable def standardizedDensity (p : I × I) : ℝ :=
  B.conditionalDensity (p.1,unitQuantile B.marginal p.2)

theorem standardizedDensity_measurable : Measurable B.standardizedDensity :=
  B.conditionalDensity_measurable.comp (measurable_fst.prodMk ((measurable_unitQuantile _).comp measurable_snd))

/-- Standardization really has the displayed density, even when the marginal has flat intervals. -/
theorem standardized_law :
    B.measure.map (fun p => (p.1,unitCDF B.marginal p.2))=
      (volume : Measure (I × I)).withDensity (fun p => ENNReal.ofReal (B.standardizedDensity p)) := by
  let T : I × I → I × I := fun p => (p.1,unitCDF B.marginal p.2)
  have hT : Measurable T := measurable_fst.prodMk ((unitCDF_continuous _).measurable.comp measurable_snd)
  have hm : ((volume : Measure I).prod B.marginal).map T=volume := by
    change ((volume : Measure I).prod B.marginal).map (Prod.map id (unitCDF B.marginal))=volume.prod volume
    rw [← Measure.map_prod_map _ _ measurable_id (unitCDF_continuous _).measurable,Measure.map_id,unitCDF_map]
  have hi : (fun p : I × I => B.conditionalDensity p)=ᵐ[(volume : Measure I).prod B.marginal]
      (fun p => B.standardizedDensity (T p)) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun B.conditionalDensity_measurable
      (B.standardizedDensity_measurable.comp hT))).mpr
    filter_upwards with u
    filter_upwards [quantile_unitCDF_ae B.marginal] with t ht
    change B.conditionalDensity (u,t)=B.conditionalDensity (u,unitQuantile B.marginal (unitCDF B.marginal t))
    rw [ht]; rfl
  have hi' : (fun p => ENNReal.ofReal (B.conditionalDensity p))=ᵐ[(volume : Measure I).prod B.marginal]
      (fun p => ENNReal.ofReal (B.standardizedDensity (T p))) := hi.fun_comp ENNReal.ofReal
  rw [B.measure_eq_conditional,withDensity_congr_ae hi']
  change (((volume : Measure I).prod B.marginal).withDensity
    ((fun p => ENNReal.ofReal (B.standardizedDensity p)) ∘ T)).map T=_
  rw [map_withDensity_comp _ hT B.standardizedDensity_measurable.ennreal_ofReal,hm]

/-- The copula measure itself, in the package's two-coordinate representation. -/
theorem copula_density : B.copula.toMeasure=
    (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (B.standardizedDensity (x 0,x 1))) := by
  let e : (Fin 2 → I) ≃ᵐ I × I := MeasurableEquiv.finTwoArrow
  have he : (volume : Measure (I × I)).map e.symm=volume :=
    (volume_preserving_finTwoArrow I).symm.map_eq
  have hs : B.sample=e.symm ∘ (fun p => (p.1,unitCDF B.marginal p.2)) := by
    funext p
    dsimp only [Function.comp_apply]
    rw [B.marginal_cdf]
    rfl
  have hT : Measurable (fun p : I × I => (p.1,unitCDF B.marginal p.2)) :=
    measurable_fst.prodMk ((unitCDF_continuous _).measurable.comp measurable_snd)
  rw [B.copula_law,hs,← Measure.map_map e.symm.measurable hT,B.standardized_law]
  have hh : Measurable (fun x : Fin 2 → I => ENNReal.ofReal (B.standardizedDensity (x 0,x 1))) :=
    B.standardizedDensity_measurable.ennreal_ofReal.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
  have hh' : ((fun x : Fin 2 → I => ENNReal.ofReal (B.standardizedDensity (x 0,x 1))) ∘ e.symm)=
      (fun p => ENNReal.ofReal (B.standardizedDensity p)) := by
    funext p
    rcases p with ⟨u,v⟩
    rfl
  simpa only [he,hh'] using (map_withDensity_comp volume e.symm.measurable hh)

end IncreasingBand
end Verification
