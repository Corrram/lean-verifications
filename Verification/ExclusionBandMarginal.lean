import Verification.ExclusionBand

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval

namespace Verification.ExclusionBand

variable (B : ExclusionBand)

noncomputable def holeLength (v : I) : ℝ :=
  ∫ u : I, if B.lower u ≤ (v : ℝ) ∧ (v : ℝ) ≤ B.lower u+B.width then 1 else 0

noncomputable def columnDensity (v : I) : ℝ := ∫ u : I, B.density (u,v)

theorem columnDensity_measurable : Measurable B.columnDensity :=
  B.density_measurable.stronglyMeasurable.integral_prod_left'.measurable

theorem columnDensity_nonneg (v : I) : 0 ≤ B.columnDensity v :=
  integral_nonneg (fun u => (B.density_mem (u,v)).1)

theorem columnDensity_integrable : Integrable B.columnDensity := B.density_integrable.integral_prod_right

/-- Equation (31): the actual second-coordinate density. -/
theorem columnDensity_eq (v : I) : B.columnDensity v=(1-B.holeLength v)/(1-B.width) := by
  let g : I → ℝ := fun u => if B.lower u ≤ (v : ℝ) ∧ (v : ℝ) ≤ B.lower u+B.width then 1 else 0
  have hm : Measurable g := Measurable.ite
    ((measurableSet_le B.lower_measurable measurable_const).inter
      (measurableSet_le measurable_const (B.lower_measurable.add_const _))) measurable_const measurable_const
  have hi : Integrable g := (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun u => by dsimp [g]; split_ifs <;> norm_num)
  have he : (fun u : I => B.density (u,v))=fun u => (1/(1-B.width))*(1-g u) := by
    funext u
    dsimp [density,g]
    split_ifs <;> simp
  unfold columnDensity
  rw [he,integral_const_mul,integral_sub (integrable_const _) hi]
  simp only [integral_const,probReal_univ,smul_eq_mul,mul_one]
  change 1/(1-B.width)*(1-B.holeLength v)=_
  ring

theorem columnDensity_integral : (∫ v : I, B.columnDensity v)=1 := by
  unfold columnDensity
  rw [← integral_prod_symm _ B.density_integrable]
  exact B.density_integral

/-- The second marginal law is exactly the density obtained by integrating rows. -/
theorem map_snd : B.measure.map Prod.snd=(volume : Measure I).withDensity (fun v => ENNReal.ofReal (B.columnDensity v)) := by
  have : IsFiniteMeasure ((volume : Measure I).withDensity (fun v => ENNReal.ofReal (B.columnDensity v))) :=
    isFiniteMeasure_withDensity_ofReal B.columnDensity_integrable.2
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map measurable_snd.aemeasurable f.continuous.measurable.aestronglyMeasurable,B.integral_measure,
    integral_withDensity_eq_integral_toReal_smul B.columnDensity_measurable.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (B.columnDensity_nonneg _),smul_eq_mul]
  have hi : Integrable (fun p : I × I => B.density p*f p.2) :=
    B.density_integrable.mul_bdd (f.continuous.measurable.comp measurable_snd).aestronglyMeasurable
      (Eventually.of_forall fun p => f.norm_coe_le_norm p.2)
  change (∫ p : I × I, B.density p*f p.2 ∂(volume.prod volume))=_
  rw [integral_prod_symm _ hi]
  simp only [integral_mul_const,columnDensity]

end Verification.ExclusionBand
