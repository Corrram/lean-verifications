import Verification.GumbelAssociation
import Verification.QuadrantIntegral

open MeasureTheory Set

namespace Verification

theorem gumbelPsiDeriv_weighted_sq {p t : ℝ} (ht : 0<t) :
    t*(gumbelPsiDeriv p t)^2 =
      p*((p*t^(p-1))*(t^p*Real.exp (-(2*t^p)))) := by
  have htP : t*t^(p-1)=t^p := by
    conv_lhs => lhs; rw [← Real.rpow_one t]
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have he : Real.exp (-(2*t^p))=(Real.exp (-t^p))^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  unfold gumbelPsiDeriv
  calc
    _ = p*((p*t^(p-1))*((t*t^(p-1))*(Real.exp (-t^p))^2)) := by ring
    _ = _ := by rw [htP]

theorem integral_gumbelPsiDeriv_weighted_sq {p : ℝ} (hp : 0<p) :
    (∫ t in Ioi (0:ℝ), t*(gumbelPsiDeriv p t)^2)=p/4 := by
  have he : (∫ t in Ioi (0:ℝ), t*(gumbelPsiDeriv p t)^2)=
      p*(∫ t in Ioi (0:ℝ), (p*t^(p-1))*(t^p*Real.exp (-(2*t^p)))) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact gumbelPsiDeriv_weighted_sq ht
  rw [he]
  have hh := integral_comp_rpow_Ioi_of_pos (g := fun t : ℝ => t*Real.exp (-(2*t))) hp
  simp only [smul_eq_mul] at hh
  rw [hh]
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 2)
    (by norm_num) (by norm_num)
  norm_num [Real.Gamma_add_one,Real.Gamma_one] at hi
  rw [hi]
  ring

theorem integral_gumbelPsiDeriv_quadrant {p : ℝ} (hp : 0<p) :
    (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), (gumbelPsiDeriv p (x+y))^2)=p/4 := by
  have hi : IntegrableOn (fun t => t*(gumbelPsiDeriv p t)^2) (Ioi (0:ℝ)) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_gumbelPsiDeriv_weighted_sq hp]
    exact (div_pos hp (by norm_num)).ne'
  rw [integral_quadrant_sum _ (by unfold gumbelPsiDeriv; fun_prop)
    (fun _ => sq_nonneg _) hi,integral_gumbelPsiDeriv_weighted_sq hp]

theorem gumbel_kendallTau {θ : ℝ} (hθ : 1≤θ) :
    (ProbabilityTheory.Copula.gumbel θ hθ).kendallTau=(θ-1)/θ := by
  have hp : 0<θ := lt_of_lt_of_le zero_lt_one hθ
  rw [gumbel_kendallTau_generator_integral hθ,integral_gumbelPsiDeriv_quadrant (inv_pos.mpr hp)]
  field_simp

end Verification
