import Verification.GaussianConditional
import Copula.Dependence.Frechet

/-! # The actual Gaussian CDF as an iterated density integral -/

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem standardNormal_affine_map (m s : ℝ) :
    (gaussianReal 0 1).map (fun x => m+s*x)=gaussianReal m (NNReal.mk (s^2) (sq_nonneg s)) := by
  calc
    _ = ((gaussianReal 0 1).map (fun x => s*x)).map (fun x => m+x) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by rw [gaussianReal_map_const_mul,gaussianReal_map_const_add]; simp

theorem standardNormal_affine_cdf (m b : ℝ) {s : ℝ} (hs : 0<s) :
    ProbabilityTheory.cdf (gaussianReal m (NNReal.mk (s^2) (sq_nonneg s))) b=
      ProbabilityTheory.cdf (gaussianReal 0 1) ((b-m)/s) := by
  rw [ProbabilityTheory.cdf_eq_real,← standardNormal_affine_map,
    map_measureReal_apply (by fun_prop) measurableSet_Iic,ProbabilityTheory.cdf_eq_real]
  congr 1
  ext x
  simp only [mem_preimage,mem_Iic,le_div_iff₀ hs]
  constructor <;> intro h <;> nlinarith

theorem gaussianReal_cdf_density (m b : ℝ) {v : NNReal} (hv : v≠0) :
    ProbabilityTheory.cdf (gaussianReal m v) b=∫ y in Iic b, gaussianPDFReal m v y := by
  rw [ProbabilityTheory.cdf_eq_real,Measure.real,gaussianReal_apply_eq_integral m hv,
    ENNReal.toReal_ofReal (integral_nonneg fun y => gaussianPDFReal_nonneg m v y)]

theorem gaussianBivariate_cdf_normal_density {r : ℝ} (hr : r∈Ioo (-1) 1) (a b : ℝ) :
    (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).cdf
      ![cdfUnit (gaussianReal 0 1) a,cdfUnit (gaussianReal 0 1) b]=
      ∫ x in Iic a, gaussianPDFReal 0 1 x*
        ∫ y in Iic b, gaussianPDFReal (r*x) (1-r^2).toNNReal y := by
  have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hvar : NNReal.mk ((Real.sqrt (1-r^2))^2) (sq_nonneg _)=(1-r^2).toNNReal := by
    apply Subtype.ext
    simp [Real.sq_sqrt hs.le,Real.toNNReal_of_nonneg hs.le]
  have hn : (1-r^2).toNNReal≠0 := ne_of_gt (Real.toNNReal_pos.mpr hs)
  rw [gaussianBivariate_cdf_normal hr,setIntegral_standardGaussian _ measurableSet_Iic]
  apply setIntegral_congr_fun measurableSet_Iic
  intro x _
  dsimp only
  rw [← standardNormal_affine_cdf (r*x) b (Real.sqrt_pos.2 hs),hvar,
    gaussianReal_cdf_density (r*x) b hn]

theorem standardNormal_joint_affine_density (r s : ℝ) (hs : s≠0) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ×ℝ => (p.1,r*p.1+s*p.2))=
      (volume : Measure (ℝ×ℝ)).withDensity
        (fun p => gaussianPDF 0 1 p.1*gaussianPDF (r*p.1) (NNReal.mk (s^2) (sq_nonneg s)) p.2) := by
  let v := NNReal.mk (s^2) (sq_nonneg s)
  have hv : v≠0 := by
    intro h
    have h' := congrArg (fun t : NNReal => (t:ℝ)) h
    have : s^2=0 := h'
    exact hs (sq_eq_zero_iff.mp this)
  have hd : Measurable (fun p : ℝ×ℝ => gaussianPDF 0 1 p.1*gaussianPDF (r*p.1) v p.2) := by
    unfold gaussianPDF gaussianPDFReal
    fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  have hfm : Measurable (fun p : ℝ×ℝ => f (p.1,r*p.1+s*p.2)) := hf.comp (by fun_prop)
  have hfx (x : ℝ) : Measurable (fun y : ℝ => f (x,y)) := hf.comp measurable_prodMk_left
  rw [lintegral_map hf (by fun_prop),lintegral_prod _ hfm.aemeasurable]
  have he (x : ℝ) : (∫⁻ y, f (x,r*x+s*y) ∂gaussianReal 0 1)=
      ∫⁻ y, f (x,y) ∂gaussianReal (r*x) v := by
    rw [← standardNormal_affine_map]
    rw [lintegral_map (hfx x) (by fun_prop)]
  simp_rw [he]
  have hinner (x : ℝ) : (∫⁻ y, f (x,y) ∂gaussianReal (r*x) v)=
      ∫⁻ y, gaussianPDF (r*x) v y*f (x,y) := by
    rw [gaussianReal_of_var_ne_zero _ hv]
    exact lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) (hfx x)
  simp_rw [hinner]
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num),lintegral_withDensity_eq_lintegral_mul _
    (measurable_gaussianPDF _ _) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hd hf]
  rw [Measure.volume_eq_prod,lintegral_prod _ (hd.mul hf).aemeasurable]
  apply lintegral_congr
  intro x
  dsimp only [Pi.mul_apply]
  rw [← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr
  intro y
  exact (mul_assoc _ _ _).symm

theorem gaussianBivariate_toMeasure_normal_density {r : ℝ} (hr : r∈Ioo (-1) 1) :
    (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).toMeasure=
      ((volume : Measure (ℝ×ℝ)).withDensity
        (fun p => gaussianPDF 0 1 p.1*gaussianPDF (r*p.1) (1-r^2).toNNReal p.2)).map
          (fun p => ![cdfUnit (gaussianReal 0 1) p.1,cdfUnit (gaussianReal 0 1) p.2]) := by
  let μ := gaussianReal 0 1
  have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hvar : NNReal.mk ((Real.sqrt (1-r^2))^2) (sq_nonneg _)=(1-r^2).toNNReal := by
    apply Subtype.ext
    simp [Real.sq_sqrt hs.le,Real.toNNReal_of_nonneg hs.le]
  have hd := standardNormal_joint_affine_density r (Real.sqrt (1-r^2))
    (ne_of_gt (Real.sqrt_pos.2 hs))
  rw [hvar] at hd
  rw [← hd,Measure.map_map (by fun_prop) (by fun_prop)]
  erw [gaussianBivariate_toMeasure_independent]
  have he := Measure.map_map
    (show Measurable (fun p : ℝ×ℝ =>
      ![cdfUnit μ p.1,cdfUnit μ (r*p.1+Real.sqrt (1-r^2)*p.2)]) by fun_prop)
    MeasurableEquiv.finTwoArrow.measurable (μ := Measure.pi (fun _ : Fin 2 => μ))
  rw [(measurePreserving_finTwoArrow μ).map_eq] at he
  exact he.symm

theorem gaussianBivariate_absolutelyContinuous {r : ℝ} (hr : r∈Ioo (-1) 1) :
    (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).toMeasure ≪ volume := by
  let μ := gaussianReal 0 1
  let F := fun p : ℝ×ℝ => ![cdfUnit μ p.1,cdfUnit μ p.2]
  have hf : Measurable F := by fun_prop
  have hinj : Function.Injective F := by
    intro p q hpq
    have h0 := congrFun hpq 0
    have h1 := congrFun hpq 1
    apply Prod.ext
    · apply standardNormalCDF_strictMono.injective
      exact congrArg Subtype.val h0
    · apply standardNormalCDF_strictMono.injective
      exact congrArg Subtype.val h1
  have hmap : (μ.prod μ).map F=(independence 2).toMeasure := by
    rw [← gaussianBivariate_zero,gaussianBivariate_toMeasure_independent]
    have he := Measure.map_map hf MeasurableEquiv.finTwoArrow.measurable
      (μ := Measure.pi (fun _ : Fin 2 => μ))
    rw [(measurePreserving_finTwoArrow μ).map_eq] at he
    simpa [F,Function.comp_def] using he
  have hab : (volume : Measure (ℝ×ℝ)) ≪ μ.prod μ := by
    rw [Measure.volume_eq_prod]
    exact (gaussianReal_absolutelyContinuous' 0 (by norm_num)).prod
      (gaussianReal_absolutelyContinuous' 0 (by norm_num))
  have hac := (withDensity_absolutelyContinuous
    (volume : Measure (ℝ×ℝ))
    (fun p : ℝ×ℝ => gaussianPDF 0 1 p.1*gaussianPDF (r*p.1) (1-r^2).toNNReal p.2)).trans hab
  have h := (hf.measurableEmbedding hinj).absolutelyContinuous_map hac
  rw [hmap] at h
  rw [gaussianBivariate_toMeasure_normal_density hr]
  exact h

theorem gaussianBivariate_absolutelyContinuous_iff {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).toMeasure ≪ volume ↔ r∈Ioo (-1) 1 := by
  constructor
  · intro h
    have hn : r≠ -1 := by
      intro he
      subst r
      rw [gaussianBivariate_negative_one,← mardia_neg_one] at h
      have hh := (mardia_absolutelyContinuous_iff (-1) (by norm_num)).mp h
      norm_num at hh
    have hp : r≠1 := by
      intro he
      subst r
      rw [gaussianBivariate_one,← mardia_one] at h
      have hh := (mardia_absolutelyContinuous_iff 1 (by norm_num)).mp h
      norm_num at hh
    exact ⟨lt_of_le_of_ne hr.1 (Ne.symm hn),lt_of_le_of_ne hr.2 hp⟩
  · intro hi
    exact gaussianBivariate_absolutelyContinuous hi

end Verification
