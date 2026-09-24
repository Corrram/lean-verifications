import Verification.NormalizedConditionalCDF
import Copula.Rank.Chatterjee
import Copula.Rank.ConditionalDerivative
import Verification.ContinuousDensityMinors

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval Topology

namespace Verification

theorem normalizedCDF_affine_energy (C : Copula 2) (a b : ℝ) :
    (∫ v : I, ∫ u : I, (a+b*normalizedCDF C u v)^2) = a^2+a*b+b^2*(C.chatterjeeXi+2)/6 := by
  have he (v : I) : (∫ u : I, (a+b*normalizedCDF C u v)^2) =
      a^2+2*a*b*(v : ℝ)+b^2*(∫ u : I, C.conditionalCDF u v^2) := by
    have hae : (fun u => (a+b*normalizedCDF C u v)^2) =ᵐ[volume] fun u => (a+b*C.conditionalCDF u v)^2 := by
      filter_upwards [normalizedCDF_ae C v] with u hu
      rw [hu]
    rw [integral_congr_ae hae]
    have hp (u : I) : (a+b*C.conditionalCDF u v)^2 =
        a^2+(2*a*b)*C.conditionalCDF u v+b^2*C.conditionalCDF u v^2 := by ring
    simp_rw [hp]
    rw [integral_add (f := fun u : I => a^2+(2*a*b)*C.conditionalCDF u v) ((integrable_const (a^2)).add ((C.integrable_conditionalCDF v).const_mul (2*a*b)))
      ((C.integrable_conditionalCDF_sq v).const_mul (b^2)),
      integral_add (integrable_const (a^2)) ((C.integrable_conditionalCDF v).const_mul (2*a*b))]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,integral_const_mul,C.integral_conditionalCDF]
  simp_rw [he]
  have ha : Integrable (fun _ : I => a^2) := integrable_const _
  have hb : Integrable (fun v : I => (2*a*b)*(v : ℝ)) :=
    (Copula.integrable_continuous_unit volume continuous_subtype_val).const_mul _
  rw [integral_add (f := fun v : I => a^2+(2*a*b)*(v : ℝ)) (ha.add hb) (C.integrable_integral_conditionalCDF_sq.const_mul (b^2)),integral_add ha hb]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,integral_const_mul,Copula.integral_unit_id,
    Copula.chatterjeeXi]
  ring

/-- A locally continuous conditional probability strictly between zero and one
prevents maximal conditional energy at this threshold. -/
theorem conditional_energy_lt_of_local_deriv (C : Copula 2) (v q : I)
    (g : I → ℝ) (hg : ContinuousAt g q)
    (hd : ∀ᶠ u in 𝓝 q, HasDerivAt (Copula.cdfSection C v) (g u) (u : ℝ))
    (h0 : 0 < g q) (h1 : g q < 1) :
    (∫ u : I, C.conditionalCDF u v ^ 2) < (v : ℝ) := by
  by_contra hn
  have he := le_antisymm (C.integral_conditionalCDF_sq_le v) (le_of_not_gt hn)
  have hz : (∫ u : I, C.conditionalCDF u v - C.conditionalCDF u v ^ 2) = 0 := by
    rw [integral_sub (C.integrable_conditionalCDF v) (C.integrable_conditionalCDF_sq v),
      C.integral_conditionalCDF, he, sub_self]
  have hnon (u : I) : 0 ≤ C.conditionalCDF u v - C.conditionalCDF u v ^ 2 := by
    nlinarith [C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v]
  have ha := (integral_eq_zero_iff_of_nonneg hnon
    ((C.integrable_conditionalCDF v).sub (C.integrable_conditionalCDF_sq v))).mp hz
  have hb : ∀ᵐ u : I, HasDerivAt (Copula.cdfSection C v) (g u) (u : ℝ) →
      0 ≤ g u ^ 2 - g u := by
    filter_upwards [ha, C.conditionalCDF_eq_deriv v] with u hu heq hder
    simp only [Pi.zero_apply] at hu
    rw [heq, hder.deriv] at hu
    linarith
  have hc := continuousAt_nonneg_of_ae_imp (μ := (volume : Measure I))
    ((hg.pow 2).sub hg) hd hb
  change 0 ≤ g q ^ 2 - g q at hc
  nlinarith [mul_pos h0 (sub_pos.mpr h1)]

end Verification
