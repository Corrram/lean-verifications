import Papers.Rockel2026XiBlest.FamilyOrder
import Verification.QuadraticBandEndpoint
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! # Uniform copula limits of the full real-parameter family -/

open MeasureTheory ProbabilityTheory Set Verification Filter
open scoped unitInterval Topology

namespace Papers.Rockel2026XiBlest

/-- Uniform error at independence from either side of the signed parameter. -/
theorem signed_extremal_independence_error (b : ℝ) (u v : I) :
    |(signedExtremalCopula b).cdf ![u,v] - (u:ℝ)*v| ≤ 2*|b| := by
  by_cases hb : 0 ≤ b
  · rw [signedExtremal_nonneg b hb]
    have h := quadraticBand_cdf_abs_sub_le b 0 hb (by norm_num) u v
    change |(extremalCopula b hb).cdf ![u,v] - (extremalCopula 0 _).cdf ![u,v]| ≤ _ at h
    simpa [extremal_zero,Copula.cdf_independence,Fin.prod_univ_two] using h
  · rw [signedExtremal_neg b (lt_of_not_ge hb),Copula.cdf_reflect_second]
    have h := quadraticBand_cdf_abs_sub_le (-b) 0 (by linarith) (by norm_num) u (unitInterval.symm v)
    change |(extremalCopula (-b) _).cdf ![u,unitInterval.symm v] -
      (extremalCopula 0 _).cdf ![u,unitInterval.symm v]| ≤ _ at h
    simp only [extremal_zero,Copula.cdf_independence,Fin.prod_univ_two,
      Matrix.cons_val_zero,Matrix.cons_val_one,unitInterval.coe_symm_eq,sub_zero,abs_neg] at h
    have he : (u:ℝ) - (extremalCopula (-b) (by linarith)).cdf ![u,unitInterval.symm v] - (u:ℝ)*v =
        -((extremalCopula (-b) (by linarith)).cdf ![u,unitInterval.symm v] - (u:ℝ)*(1-v)) := by ring
    rw [he,abs_neg]
    exact h

/-- The family converges uniformly to independence as the real parameter tends to zero. -/
theorem signed_extremal_uniform_zero :
    TendstoUniformly (fun b : ℝ => fun p : I × I => (signedExtremalCopula b).cdf ![p.1,p.2])
      (fun p : I × I => (Copula.independence 2).cdf ![p.1,p.2]) (𝓝 0) := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he : ∀ᶠ b : ℝ in 𝓝 0, |b| < ε/2 := by
    exact (continuous_abs.tendsto (0:ℝ)).eventually
      (eventually_lt_nhds (show |(0:ℝ)| < ε/2 by simpa using (show (0:ℝ) < ε/2 by linarith)))
  filter_upwards [he] with b hb
  intro p
  rw [Real.dist_eq,abs_sub_comm]
  simp only [Copula.cdf_independence,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact (signed_extremal_independence_error b p.1 p.2).trans_lt (by linarith)

/-- Uniform convergence for the entire real parameter at positive infinity. -/
theorem signed_extremal_uniform_top :
    TendstoUniformly (fun b : ℝ => fun p : I × I => (signedExtremalCopula b).cdf ![p.1,p.2])
      (fun p : I × I => (Copula.comonotonic 2).cdf ![p.1,p.2]) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [eventually_ge_atTop (max 1 (1/(ε/2)^2))] with b hb
  have hb1 : 1 ≤ b := (le_max_left _ _).trans hb
  have hbr : 1 ≤ b*(ε/2)^2 := by
    have hh := (le_max_right 1 (1/(ε/2)^2)).trans hb
    exact (div_le_iff₀ (sq_pos_of_pos (by linarith))).mp hh
  intro p
  rw [Real.dist_eq,abs_sub_comm,signedExtremal_nonneg b (by linarith),Copula.cdf_comonotonic_two]
  exact (quadraticBand_comonotonic_error b (ε/2) (by linarith) (by linarith) hbr p.1 p.2).trans_lt
    (by linarith)

/-- Uniform convergence for the entire real parameter at negative infinity. -/
theorem signed_extremal_uniform_bot :
    TendstoUniformly (fun b : ℝ => fun p : I × I => (signedExtremalCopula b).cdf ![p.1,p.2])
      (fun p : I × I => Copula.countermonotonic.cdf ![p.1,p.2]) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hh := tendsto_neg_atBot_atTop.eventually
    (Metric.tendstoUniformly_iff.mp signed_extremal_uniform_top ε hε)
  filter_upwards [hh,eventually_lt_atBot (0:ℝ)] with b hb hn
  intro p
  have h := hb (p.1,unitInterval.symm p.2)
  rw [signedExtremal_nonneg (-b) (by linarith)] at h
  rw [signedExtremal_neg b hn,← Copula.reflect_comonotonic_eq_countermonotonic,
    Copula.cdf_reflect_second,Copula.cdf_reflect_second,dist_sub_left]
  exact h

end Papers.Rockel2026XiBlest
