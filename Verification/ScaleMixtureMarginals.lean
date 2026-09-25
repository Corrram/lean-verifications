import Copula.Elliptical.ScaleMixture

open ProbabilityTheory MeasureTheory Set Copula

namespace Verification

theorem gaussianScaleMixtureLaw_marginal {d : ℕ} (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (hd : ∀ i,R i i=1) (μ : ProbabilityMeasure ℝ)
    (s : ℝ → ℝ) (hs : Measurable s) (i : Fin d) :
    marginal (gaussianScaleMixtureLaw R μ s) i=
      ((gaussianReal 0 1).prod μ.toMeasure).map (fun p : ℝ×ℝ => s p.2*p.1) := by
  let G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R
  have he : G.map (fun x => x i)=gaussianReal 0 1 := by
    have h := (measurePreserving_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ (Fin d))) hR (i := i)).map_eq
    simpa only [PiLp.zero_apply,hd,Real.toNNReal_one] using h
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin d) × ℝ => fun j => s p.2*p.1 j) := by fun_prop
  have hf : Measurable (fun p : ℝ×ℝ => s p.2*p.1) := by fun_prop
  change ((G.prod μ.toMeasure).map (fun p j => s p.2*p.1 j)).map (fun x => x i)=_
  rw [Measure.map_map (measurable_pi_apply i) hm,← he,← Measure.map_id (μ := μ.toMeasure),
    Measure.map_prod_map G μ.toMeasure (by fun_prop) measurable_id,
    Measure.map_map hf (by fun_prop)]
  rw [Measure.map_id]
  rfl

end Verification
