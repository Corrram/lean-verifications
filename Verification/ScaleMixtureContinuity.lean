import Verification.GaussianContinuity
import Verification.ScaleMixtureSymmetry

open ProbabilityTheory MeasureTheory Set Copula Filter
open scoped unitInterval Topology

namespace Verification

theorem gaussianScaleMixture_cdf_marginal {r : ℝ} (hr : r∈Icc (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) (a b : ℝ) :
    (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).cdf
      ![cdfUnit (normalScaleMixtureMarginal μ s) a,cdfUnit (normalScaleMixtureMarginal μ s) b]=
      ∫ t, (gaussianBivariate r hr).cdf
        ![cdfUnit (gaussianReal 0 1) (a/s t),cdfUnit (gaussianReal 0 1) (b/s t)] ∂μ.toMeasure := by
  have h := isSklarCopula_gaussianScaleMixture (bivariateCorrelation r)
    (bivariateCorrelation_posSemidef hr) (by intro i; fin_cases i <;> rfl) μ s hs hp ![a,b]
  have hm (i : Fin 2) : marginal (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s) i=
      normalScaleMixtureMarginal μ s :=
    gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef hr)
      (by intro j; fin_cases j <;> rfl) μ s hs i
  have he : marginalTransform (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s) ![a,b]=
      ![cdfUnit (normalScaleMixtureMarginal μ s) a,cdfUnit (normalScaleMixtureMarginal μ s) b] := by
    ext i
    dsimp only [marginalTransform]
    rw [hm i]
    fin_cases i <;> rfl
  rw [he] at h
  exact h.trans (gaussianScaleMixtureLaw_rectangle hr μ s hs hp a b)

theorem gaussianScaleMixture_cdf_continuous (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) (u : Fin 2 → I) :
    Continuous (fun r : Icc (-1:ℝ) 1 =>
      (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef r.property)
        (by intro i; fin_cases i <;> rfl) μ s hs hp).cdf u) := by
  let C := fun r : Icc (-1:ℝ) 1 =>
    gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef r.property)
      (by intro i; fin_cases i <;> rfl) μ s hs hp
  change Continuous (fun r => (C r).cdf u)
  by_cases h0 : u 0=0
  · have he : (fun r => (C r).cdf u)=fun _ => (0:ℝ) :=
      funext fun r => (C r).cdf_eq_zero_of_coord_eq_zero u 0 h0
    rw [he]
    exact continuous_const
  by_cases h1 : u 1=0
  · have he : (fun r => (C r).cdf u)=fun _ => (0:ℝ) :=
      funext fun r => (C r).cdf_eq_zero_of_coord_eq_zero u 1 h1
    rw [he]
    exact continuous_const
  have hu : u=![u 0,u 1] := by ext i; fin_cases i <;> rfl
  by_cases h01 : u 0=1
  · have he : (fun r => (C r).cdf u)=fun _ => (u 1:ℝ) := by
      funext r
      conv_lhs => rw [hu,h01]
      exact cdf_two_one_left _ _
    rw [he]
    exact continuous_const
  by_cases h11 : u 1=1
  · have he : (fun r => (C r).cdf u)=fun _ => (u 0:ℝ) := by
      funext r
      conv_lhs => rw [hu,h11]
      exact cdf_two_one_right _ _
    rw [he]
    exact continuous_const
  let M := normalScaleMixtureMarginal μ s
  have hc : Continuous (ProbabilityTheory.cdf M) := by
    have hm := gaussianScaleMixtureLaw_marginal (bivariateCorrelation 0)
      (bivariateCorrelation_posSemidef (by norm_num)) (by intro i; fin_cases i <;> rfl) μ s hs 0
    change marginal (gaussianScaleMixtureLaw (bivariateCorrelation 0) μ s) 0=M at hm
    rw [← hm]
    exact continuous_gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef (by norm_num))
      (by intro i; fin_cases i <;> rfl) μ s hs hp 0
  have hu0 : (u 0:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne (u 0).property.1 (by exact fun h => h0 (Subtype.ext h.symm)),
      lt_of_le_of_ne (u 0).property.2 (by exact fun h => h01 (Subtype.ext h))⟩
  have hu1 : (u 1:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne (u 1).property.1 (by exact fun h => h1 (Subtype.ext h.symm)),
      lt_of_le_of_ne (u 1).property.2 (by exact fun h => h11 (Subtype.ext h))⟩
  obtain ⟨a,ha⟩ := exists_cdf_eq_of_continuous M hc hu0.1 hu0.2
  obtain ⟨b,hb⟩ := exists_cdf_eq_of_continuous M hc hu1.1 hu1.2
  have hev : u=![cdfUnit M a,cdfUnit M b] := by
    rw [hu,show cdfUnit M a=u 0 from Subtype.ext ha,show cdfUnit M b=u 1 from Subtype.ext hb]
  let F := fun r : Icc (-1:ℝ) 1 => fun t : ℝ => (gaussianBivariate r r.property).cdf
    ![cdfUnit (gaussianReal 0 1) (a/s t),cdfUnit (gaussianReal 0 1) (b/s t)]
  have he : (fun r => (C r).cdf u)=fun r => ∫ t,F r t ∂μ.toMeasure := by
    funext r
    rw [hev]
    exact gaussianScaleMixture_cdf_marginal r.property μ s hs hp a b
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro r
  have hm (q : Icc (-1:ℝ) 1) : Measurable (F q) :=
    (gaussianBivariate q q.property).continuous_cdf.measurable.comp (by fun_prop)
  apply continuousAt_of_dominated (μ := μ.toMeasure) (bound := fun _ => (1:ℝ))
    (Eventually.of_forall fun q => (hm q).aestronglyMeasurable)
    (Eventually.of_forall fun q => Eventually.of_forall fun t => by
      dsimp only [F]
      rw [Real.norm_eq_abs,abs_of_nonneg (Copula.cdf_nonneg _ _)]
      exact Copula.cdf_le_one _ _) (integrable_const _)
  exact Eventually.of_forall fun t => (gaussianBivariate_cdf_continuous _).continuousAt

end Verification
