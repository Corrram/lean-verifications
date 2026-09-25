import Verification.ScaleMixtureJointCDF
import Verification.ScaleMixtureReflection
import Copula.TailDependence.Basic

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem gaussianScaleMixture_transpose {r : ℝ} (hr : r∈Icc (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).transpose=
    gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp := by
  let C := gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
    (by intro i; fin_cases i <;> rfl) μ s hs hp
  let M := normalScaleMixtureMarginal μ s
  have hm (i : Fin 2) : marginal (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s) i=M :=
    gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef hr)
      (by intro j; fin_cases j <;> rfl) μ s hs i
  have hc : Continuous (ProbabilityTheory.cdf M) := by
    rw [← hm 0]
    exact continuous_gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp 0
  have hcdf (a b : ℝ) : C.cdf ![cdfUnit M a,cdfUnit M b]=
      ∫ t, (gaussianBivariate r hr).cdf
        ![cdfUnit (gaussianReal 0 1) (a/s t),cdfUnit (gaussianReal 0 1) (b/s t)] ∂μ.toMeasure := by
    have h := isSklarCopula_gaussianScaleMixture (bivariateCorrelation r)
      (bivariateCorrelation_posSemidef hr) (by intro i; fin_cases i <;> rfl) μ s hs hp ![a,b]
    have he : marginalTransform (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s) ![a,b]=
        ![cdfUnit M a,cdfUnit M b] := by
      ext i
      dsimp only [marginalTransform]
      rw [hm i]
      fin_cases i <;> rfl
    rw [he] at h
    exact h.trans (gaussianScaleMixtureLaw_rectangle hr μ s hs hp a b)
  have hd : DenseRange (fun x : Fin 2 → ℝ => fun i => cdfUnit M (x i)) :=
    DenseRange.piMap (fun _ => denseRange_cdfUnit_of_continuous M hc)
  apply ext_cdf
  intro u
  change C.transpose.cdf u=C.cdf u
  apply hd.induction_on (p := fun u => C.transpose.cdf u=C.cdf u) u
    (isClosed_eq C.transpose.continuous_cdf C.continuous_cdf)
  intro x
  have he : (fun i => cdfUnit M (x i))=![cdfUnit M (x 0),cdfUnit M (x 1)] := by
    ext i; fin_cases i <;> rfl
  rw [he,cdf_transpose,hcdf,hcdf]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    have h := cdf_transpose (gaussianBivariate r hr)
      (cdfUnit (gaussianReal 0 1) (x 0/s t)) (cdfUnit (gaussianReal 0 1) (x 1/s t))
    rw [gaussianBivariate_transpose hr] at h
    exact h.symm

theorem gaussianScaleMixture_radiallySymmetric {r : ℝ} (hr : r∈Icc (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).IsRadiallySymmetric := by
  have hn : -r∈Icc (-1) 1 := by constructor <;> linarith [hr.1,hr.2]
  have hf : (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).reflect {0}=
      gaussianScaleMixture (bivariateCorrelation (-r)) (bivariateCorrelation_posSemidef hn)
        (by intro i; fin_cases i <;> rfl) μ s hs hp := by
    have h := transpose_reflect_first (gaussianScaleMixture (bivariateCorrelation r)
      (bivariateCorrelation_posSemidef hr) (by intro i; fin_cases i <;> rfl) μ s hs hp)
    rw [gaussianScaleMixture_transpose hr μ s hs hp,← gaussianScaleMixture_neg hr μ s hs hp] at h
    have he := congrArg Copula.transpose h
    simpa only [transpose_transpose,gaussianScaleMixture_transpose hn μ s hs hp] using he
  unfold IsRadiallySymmetric
  rw [← reflect_first_second,hf,← gaussianScaleMixture_neg hn μ s hs hp]
  simp only [neg_neg]

end Verification

