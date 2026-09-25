import Verification.GumbelAssociation
import Copula.Rank.SpearmanCDF
import Verification.QuadrantScale

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval

namespace Verification

theorem gumbel_spearmanRho_real_integral {θ : ℝ} (hθ : 1≤θ) :
    (gumbel θ hθ).spearmanRho =
      12*(∫ u : I, ∫ v : I, gumbelRealCDF θ u v)-3 := by
  rw [spearmanRho_eq_integral_cdf,toMeasure_independence]
  change 12*(∫ z : Fin 2 → I, (gumbel θ hθ).cdf z)-3=_
  have hh := integral_cube_Iic_iterated ((gumbel θ hθ).integrable_cdf volume) 1 1
  have ht : (![1,1] : Fin 2 → I)=⊤ := by ext i; fin_cases i <;> rfl
  rw [ht] at hh
  simp only [show (1:I)=⊤ from rfl,Iic_top,Measure.restrict_univ] at hh
  rw [hh]
  congr 2
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with u hu
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv
  rw [gumbel,BivariateGenerator.cdf_copula,BivariateGenerator.cdf]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,hu,hv,false_or,ite_false]
  rfl

theorem gumbel_spearmanRho_log_integral {θ : ℝ} (hθ : 1≤θ) :
    (gumbel θ hθ).spearmanRho =
      12*(∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
        Real.exp (-(x+y+(x^θ+y^θ)^θ⁻¹)))-3 := by
  rw [gumbel_spearmanRho_real_integral hθ]
  have hv (u : ℝ) := integral_unit_neg_exp (fun v => gumbelRealCDF θ u v)
  simp_rw [hv]
  rw [integral_unit_neg_exp (fun u => ∫ y in Ioi (0:ℝ),
    Real.exp (-y)*gumbelRealCDF θ u (Real.exp (-y)))]
  congr 2
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  dsimp only
  unfold gumbelRealCDF gumbelInv
  simp only [Real.log_exp,neg_neg]
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  ring

theorem gumbel_log_kernel_integrable (θ : ℝ) :
    Integrable (fun z : ℝ × ℝ => Real.exp (-(z.1+z.2+(z.1^θ+z.2^θ)^θ⁻¹)))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi 0))) := by
  have hi := (integrableOn_exp_neg_Ioi 0).mul_prod (integrableOn_exp_neg_Ioi 0)
  apply hi.mono' (by fun_prop)
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hp := Real.rpow_nonneg
    (add_nonneg (Real.rpow_nonneg (le_of_lt hx) θ) (Real.rpow_nonneg (le_of_lt hy) θ)) θ⁻¹
  linarith

theorem gumbel_log_homogeneous {θ x s : ℝ} (hθ : 0<θ) (hx : 0<x) (hs : 0<s) :
    x+x*s+(x^θ+(x*s)^θ)^θ⁻¹=x*(1+s+(1+s^θ)^θ⁻¹) := by
  rw [Real.mul_rpow hx.le hs.le]
  have he : x^θ+x^θ*s^θ=x^θ*(1+s^θ) := by ring
  rw [he,Real.mul_rpow (Real.rpow_nonneg hx.le _) (by positivity),
    ← Real.rpow_mul hx.le,mul_inv_cancel₀ hθ.ne',Real.rpow_one]
  ring

theorem integral_gumbel_radial {θ s : ℝ} (hθ : 0<θ) (hs : 0<s) :
    (∫ x in Ioi (0:ℝ), max 0 x*Real.exp (-(x+x*s+(x^θ+(x*s)^θ)^θ⁻¹)))=
      (1/(1+s+(1+s^θ)^θ⁻¹))^2 := by
  have ha : 0<1+s+(1+s^θ)^θ⁻¹ := by positivity
  have he : (∫ x in Ioi (0:ℝ), max 0 x*Real.exp (-(x+x*s+(x^θ+(x*s)^θ)^θ⁻¹)))=
      ∫ x in Ioi (0:ℝ), x*Real.exp (-((1+s+(1+s^θ)^θ⁻¹)*x)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [max_eq_right (le_of_lt hx),gumbel_log_homogeneous hθ hx hs]
    simp only [mul_comm]
  rw [he]
  have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) ha
  norm_num [Real.Gamma_add_one,Real.Gamma_one] at hh
  simpa only [one_div,inv_pow] using hh

theorem gumbel_spearmanRho_ratio_integral {θ : ℝ} (hθ : 1≤θ) :
    (gumbel θ hθ).spearmanRho=
      12*(∫ s in Ioi (0:ℝ), (1/(1+s+(1+s^θ)^θ⁻¹))^2)-3 := by
  rw [gumbel_spearmanRho_log_integral hθ]
  rw [integral_quadrant_scale _ (by fun_prop) (fun _ => (Real.exp_pos _).le)
    (gumbel_log_kernel_integrable θ)]
  congr 2
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  exact integral_gumbel_radial (lt_of_lt_of_le zero_lt_one hθ) hs

end Verification
