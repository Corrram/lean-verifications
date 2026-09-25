import Verification.GaussianBivariate
import Copula.Rank.Symmetry
import Verification.XiReflection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def gaussianNegSecond :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (![1,-1] i : ℝ) • EuclideanSpace.proj i)

theorem gaussianNegSecond_apply (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    gaussianNegSecond x i=(![1,-1] i : ℝ)*x i := by
  simp [gaussianNegSecond]

theorem map_gaussianNegSecond {r : ℝ} (hr : r∈Icc (-1) 1) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).map
      gaussianNegSecond = multivariateGaussian 0 (bivariateCorrelation (-r)) := by
  have hn : -r∈Icc (-1) 1 := by constructor <;> linarith [hr.1,hr.2]
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map,integral_id_multivariateGaussian,
      map_zero,integral_id_multivariateGaussian]
    exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply,ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov,covariance_map]
  · have hh (i : Fin 2) :
        (fun u => inner (𝕜 := ℝ) ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i) u) ∘
          gaussianNegSecond = fun u => (![1,-1] i : ℝ)*u i := by
      funext u
      simp [PiLp.inner_apply,gaussianNegSecond_apply]
    simp_rw [hh,covariance_const_mul_left,covariance_const_mul_right,
      covariance_eval_multivariateGaussian (bivariateCorrelation_posSemidef hr),
      covarianceBilin_multivariateGaussian (bivariateCorrelation_posSemidef hn)]
    fin_cases i <;> fin_cases j <;> simp [bivariateCorrelation]
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

theorem standardNormalCDF_neg (x : ℝ) :
    ProbabilityTheory.cdf (gaussianReal 0 1) (-x)=1-ProbabilityTheory.cdf (gaussianReal 0 1) x := by
  let μ := gaussianReal 0 1
  let : NullSingletonClass μ := nullSingletonClass_gaussianReal one_ne_zero
  have hm : μ.map (fun z : ℝ => -z)=μ := by
    simp only [μ,gaussianReal_map_neg,neg_zero]
  have hs : (fun z : ℝ => -z) ⁻¹' Iic (-x)=Ici x := by
    ext z
    simp
  have he : μ.real (Ici x)=μ.real (Ioi x) := by
    apply measureReal_congr
    filter_upwards [Measure.ae_ne μ x] with z hz
    apply propext
    simp only [mem_Ici,mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm hz),fun h => h.le⟩
  rw [ProbabilityTheory.cdf_eq_real,ProbabilityTheory.cdf_eq_real]
  change μ.real (Iic (-x))=1-μ.real (Iic x)
  calc
    _ = (μ.map (fun z : ℝ => -z)).real (Iic (-x)) := by rw [hm]
    _ = μ.real (Ici x) := by rw [map_measureReal_apply (by fun_prop) measurableSet_Iic,hs]
    _ = 1-μ.real (Iic x) := by
      rw [he,← compl_Iic,measureReal_compl measurableSet_Iic,probReal_univ]

theorem standardNormalCDFUnit_neg (x : ℝ) :
    cdfUnit (gaussianReal 0 1) (-x)=unitInterval.symm (cdfUnit (gaussianReal 0 1) x) := by
  apply Subtype.ext
  exact standardNormalCDF_neg x

theorem gaussianBivariate_neg {r : ℝ} (hr : r∈Icc (-1) 1) :
    gaussianBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])=
      (gaussianBivariate r hr).reflect {1} := by
  apply Copula.ext
  rw [toMeasure_reflect]
  change (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation (-r))).map
      (fun x i => cdfUnit (gaussianReal 0 1) (x i)) =
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).map
      (fun x i => cdfUnit (gaussianReal 0 1) (x i))).map (reflectPoint {1})
  rw [← map_gaussianNegSecond hr,Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (measurable_reflectPoint _) (by fun_prop)]
  congr 1
  funext x i
  fin_cases i <;> simp [gaussianNegSecond_apply,reflectPoint,standardNormalCDFUnit_neg]

theorem gaussianBivariate_negative_one :
    gaussianBivariate (-1) (by norm_num)=countermonotonic := by
  rw [gaussianBivariate_neg (r := 1) (by norm_num),gaussianBivariate_one,
    reflect_comonotonic_eq_countermonotonic]

theorem gaussianBivariate_xi_neg {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])).chatterjeeXi=
      (gaussianBivariate r hr).chatterjeeXi := by
  rw [gaussianBivariate_neg hr,xi_reflect_second]

theorem gaussianBivariate_rho_neg {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])).spearmanRho=
      -(gaussianBivariate r hr).spearmanRho := by
  rw [gaussianBivariate_neg hr,spearmanRho_reflect_second]

theorem gaussianBivariate_tau_neg {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])).kendallTau=
      -(gaussianBivariate r hr).kendallTau := by
  rw [gaussianBivariate_neg hr,kendallTau_reflect_second]

noncomputable def gaussianPrintedXi (r : ℝ) : ℝ :=
  3/Real.pi*Real.arcsin (gaussianPrintedXiArgument r)-1/2

theorem gaussianPrintedXi_negative_half : gaussianPrintedXi (-(1/2))=1 := by
  norm_num [gaussianPrintedXi,gaussianPrintedXiArgument,Real.arcsin_one]
  field_simp
  ring

theorem gaussianPrintedXi_half_lt_one : gaussianPrintedXi (1/2)<1 := by
  have ha : Real.arcsin (2/3)<Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr (by norm_num)
  have hh := mul_lt_mul_of_pos_left ha (show 0<3/Real.pi by positivity)
  have he : (3/Real.pi)*(Real.pi/2)=(3/2:ℝ) := by field_simp
  rw [he] at hh
  norm_num [gaussianPrintedXi,gaussianPrintedXiArgument]
  linarith

theorem gaussian_printed_xi_formula_false :
    ¬∀ (r : ℝ) (hr : r∈Icc (-1) 1),
      (gaussianBivariate r hr).chatterjeeXi=gaussianPrintedXi r := by
  intro h
  have hn := h (-(1/2)) (by norm_num)
  have hp := h (1/2) (by norm_num)
  have he := gaussianBivariate_xi_neg (r := 1/2) (by norm_num)
  rw [hn,hp,gaussianPrintedXi_negative_half] at he
  linarith [gaussianPrintedXi_half_lt_one]

end Verification
