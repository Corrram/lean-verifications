import Verification.GaussianDifference

/-! # Gaussian Kendall tau on the closed correlation interval

Strict normal-CDF monotonicity and Gaussian difference stability reduce the
actual copula's Kendall functional to its Gaussian lower-quadrant probability.
The singular endpoints are handled by their benchmark copulas.
-/

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem gaussianBivariate_tau_quadrant {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).kendallTau=
      4*(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).real
        {x | x 0≤0 ∧ x 1≤0}-1 := by
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  let f := fun x : EuclideanSpace ℝ (Fin 2) => fun i => cdfUnit (gaussianReal 0 1) (x i)
  have hf : Measurable f := by fun_prop
  have hC : (gaussianBivariate r hr).toMeasure=μ.map f := rfl
  have hS : MeasurableSet {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hQ : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) | x 0≤0 ∧ x 1≤0} := by
    apply MeasurableSet.inter
    · exact measurableSet_le
        (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 0) by fun_prop) measurable_const
    · exact measurableSet_le
        (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 1) by fun_prop) measurable_const
  have hs : (Prod.map f f) ⁻¹' {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2}=
      gaussianDifference ⁻¹' {x | x 0≤0 ∧ x 1≤0} := by
    ext p
    change (∀ i, ProbabilityTheory.cdf (gaussianReal 0 1) (p.1 i)≤
      ProbabilityTheory.cdf (gaussianReal 0 1) (p.2 i)) ↔
      (Real.sqrt 2)⁻¹*(p.1 0-p.2 0)≤0 ∧ (Real.sqrt 2)⁻¹*(p.1 1-p.2 1)≤0
    have hc : 0<(Real.sqrt 2)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by norm_num))
    have hh (a b : ℝ) : (Real.sqrt 2)⁻¹*(a-b)≤0 ↔ a≤b := by
      constructor
      · intro h
        nlinarith
      · intro h
        exact mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr h)
    simp only [standardNormalCDF_strictMono.le_iff_le,Fin.forall_fin_two,hh]
  rw [kendallTau_probability,hC,Measure.map_prod_map _ _ hf hf,
    map_measureReal_apply (hf.prodMap hf) hS,hs,
    ← map_measureReal_apply (by fun_prop) hQ,map_gaussianDifference]

theorem gaussianBivariate_kendallTau {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).kendallTau=2/Real.pi*Real.arcsin r := by
  by_cases hneg : r= -1
  · subst r
    rw [gaussianBivariate_negative_one,kendallTau_countermonotonic,Real.arcsin_neg,
      Real.arcsin_one]
    field_simp
  by_cases hpos : r=1
  · subst r
    rw [gaussianBivariate_one,kendallTau_comonotonic,Real.arcsin_one]
    field_simp
  have hi : r∈Ioo (-1) 1 := ⟨lt_of_le_of_ne hr.1 (Ne.symm hneg),lt_of_le_of_ne hr.2 hpos⟩
  rw [gaussianBivariate_tau_quadrant hr,multivariateGaussian_lower_quadrant hi]
  ring

end Verification
