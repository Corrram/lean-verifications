import Verification.GaussianNormalDensity
import Verification.NormalQuantile

/-! # A Lebesgue density for the actual Gaussian copula -/

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def gaussianCopulaDensity (r : ℝ) (u : Fin 2 → I) : ℝ :=
  if (u 0:ℝ)∈Ioo (0:ℝ) 1 ∧ (u 1:ℝ)∈Ioo (0:ℝ) 1 then
    gaussianPDFReal (r*normalQuantile (u 0)) (1-r^2).toNNReal (normalQuantile (u 1)) /
      gaussianPDFReal 0 1 (normalQuantile (u 1)) else 0

theorem gaussianCopulaDensity_nonneg (r : ℝ) (u : Fin 2 → I) : 0≤gaussianCopulaDensity r u := by
  unfold gaussianCopulaDensity
  split_ifs
  · exact div_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)
  · exact le_rfl

theorem measurable_gaussianCopulaDensity (r : ℝ) : Measurable (gaussianCopulaDensity r) := by
  have hq (i : Fin 2) : Measurable (fun u : Fin 2 → I => normalQuantile (u i)) :=
    measurable_normalQuantile.comp (measurable_pi_apply i)
  apply Measurable.ite
    ((measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 0))).inter
      (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 1))))
  · unfold gaussianPDFReal
    fun_prop
  · exact measurable_const

theorem gaussianCopulaDensity_normal (r x y : ℝ) :
    gaussianCopulaDensity r ![cdfUnit (gaussianReal 0 1) x,cdfUnit (gaussianReal 0 1) y]=
      gaussianPDFReal (r*x) (1-r^2).toNNReal y/gaussianPDFReal 0 1 y := by
  have h : ((![cdfUnit (gaussianReal 0 1) x,cdfUnit (gaussianReal 0 1) y] 0 : I):ℝ)∈Ioo (0:ℝ) 1 ∧
      ((![cdfUnit (gaussianReal 0 1) x,cdfUnit (gaussianReal 0 1) y] 1 : I):ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨normalCDF_mem_Ioo x,normalCDF_mem_Ioo y⟩
  rw [gaussianCopulaDensity,ite_eq_left h]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,normalQuantile_cdfUnit]

theorem gaussian_map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {F : α → β} (hF : Measurable F) {g : β → ENNReal} (hg : Measurable g) :
    (μ.withDensity (fun x => g (F x))).map F=(μ.map F).withDensity g := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hgF : Measurable (fun x => g (F x)) := hg.comp hF
  have hfF : Measurable (fun x => f (F x)) := hf.comp hF
  rw [lintegral_map hf hF,
    lintegral_withDensity_eq_lintegral_mul _ hgF hfF,
    lintegral_withDensity_eq_lintegral_mul _ hg hf,lintegral_map (hg.mul hf) hF]
  rfl

theorem gaussianBivariate_density {r : ℝ} (hr : r∈Ioo (-1) 1) :
    (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).toMeasure=
      volume.withDensity (fun u => ENNReal.ofReal (gaussianCopulaDensity r u)) := by
  let μ := gaussianReal 0 1
  let F := fun p : ℝ×ℝ => ![cdfUnit μ p.1,cdfUnit μ p.2]
  let g := fun u => ENNReal.ofReal (gaussianCopulaDensity r u)
  have hf : Measurable F := by fun_prop
  have hg : Measurable g := (measurable_gaussianCopulaDensity r).ennreal_ofReal
  have hmap : (μ.prod μ).map F=(volume : Measure (Fin 2 → I)) := by
    change (μ.prod μ).map F=(independence 2).toMeasure
    rw [← gaussianBivariate_zero,gaussianBivariate_toMeasure_independent]
    have he := Measure.map_map hf MeasurableEquiv.finTwoArrow.measurable
      (μ := Measure.pi (fun _ : Fin 2 => μ))
    rw [(measurePreserving_finTwoArrow μ).map_eq] at he
    simpa [F,Function.comp_def] using he
  have hd : (volume : Measure (ℝ×ℝ)).withDensity
      (fun p => gaussianPDF 0 1 p.1*gaussianPDF (r*p.1) (1-r^2).toNNReal p.2)=
      (μ.prod μ).withDensity (fun p => g (F p)) := by
    have hb : μ.prod μ=(volume : Measure (ℝ×ℝ)).withDensity
        (fun p => gaussianPDF 0 1 p.1*gaussianPDF 0 1 p.2) := by
      dsimp only [μ]
      rw [gaussianReal_of_var_ne_zero 0 (by norm_num),prod_withDensity
        (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),Measure.volume_eq_prod]
    have hbase : Measurable (fun p : ℝ×ℝ => gaussianPDF 0 1 p.1*gaussianPDF 0 1 p.2) := by fun_prop
    have hgF : Measurable (fun p => g (F p)) := hg.comp hf
    rw [hb,← withDensity_mul _ hbase hgF]
    congr 1
    funext p
    dsimp only [g,F,Pi.mul_apply]
    rw [gaussianCopulaDensity_normal]
    have hp : gaussianPDFReal 0 1 p.2≠0 := ne_of_gt (gaussianPDFReal_pos 0 1 p.2 (by norm_num))
    simp only [gaussianPDF,← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    rw [← ENNReal.ofReal_mul (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _))]
    congr 1
    field_simp [hp]
  rw [gaussianBivariate_toMeasure_normal_density hr,hd,gaussian_map_withDensity_comp _ hf hg,hmap]

end Verification
