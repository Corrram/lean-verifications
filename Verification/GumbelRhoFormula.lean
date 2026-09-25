import Verification.GumbelRho
import Verification.UnitOddsSubstitution

open ProbabilityTheory MeasureTheory Set Copula

namespace Verification

theorem gumbel_rho_odds_kernel (p : ℝ) {t : ℝ} (ht : t∈Ioo 0 1) :
    ((1-t)^2)⁻¹*((t/(1-t))^(p-1)/(1+(t/(1-t))^p+(1+t/(1-t))^p)^2)=
      (t*(1-t))^(p-1)/(1+t^p+(1-t)^p)^2 := by
  have hs : 0<1-t := sub_pos.mpr ht.2
  have h1 : 1+t/(1-t)=1/(1-t) := by field_simp; ring
  have hB : (1-t)^p=(1-t)*(1-t)^(p-1) := by
    conv_rhs => lhs; rw [← Real.rpow_one (1-t)]
    rw [← Real.rpow_add hs]
    congr 1
    ring
  rw [h1,Real.div_rpow ht.1.le hs.le,Real.div_rpow ht.1.le hs.le,
    Real.div_rpow zero_le_one hs.le,Real.one_rpow,Real.mul_rpow ht.1.le hs.le]
  have hden : 1+t^p/(1-t)^p+1/(1-t)^p=(1+t^p+(1-t)^p)/(1-t)^p := by
    field_simp
    ring
  rw [hden,div_pow,div_div,hB]
  have hb := (Real.rpow_pos_of_pos hs (p-1)).ne'
  have htp := Real.rpow_pos_of_pos ht.1 p
  have hsp := Real.rpow_pos_of_pos hs (p-1)
  have hd : 1+t^p+(1-t)*(1-t)^(p-1)≠0 := by positivity
  field_simp [hs.ne',hb,hd]

theorem gumbel_ratio_power_integral {θ : ℝ} (hθ : 0<θ) :
    (∫ s in Ioi (0:ℝ), (1/(1+s+(1+s^θ)^θ⁻¹))^2)=
      θ⁻¹*(∫ w in Ioi (0:ℝ), w^(θ⁻¹-1)/(1+w^θ⁻¹+(1+w)^θ⁻¹)^2) := by
  rw [← integral_comp_rpow_Ioi_of_pos (g := fun s : ℝ =>
    (1/(1+s+(1+s^θ)^θ⁻¹))^2) (inv_pos.mpr hθ),← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro w hw
  dsimp only
  rw [← Real.rpow_mul (le_of_lt hw),inv_mul_cancel₀ hθ.ne',Real.rpow_one]
  simp only [smul_eq_mul,div_pow,one_pow]
  ring

theorem gumbel_spearmanRho {θ : ℝ} (hθ : 1≤θ) :
    (gumbel θ hθ).spearmanRho=
      (12/θ)*(∫ t in (0:ℝ)..1,
        (t*(1-t))^(1/θ-1)/(1+t^(1/θ)+(1-t)^(1/θ))^2)-3 := by
  rw [gumbel_spearmanRho_ratio_integral hθ,
    gumbel_ratio_power_integral (lt_of_lt_of_le zero_lt_one hθ),integral_unit_odds]
  have he : (∫ t in (0:ℝ)..1,
      ((1-t)^2)⁻¹*((t/(1-t))^(θ⁻¹-1)/(1+(t/(1-t))^θ⁻¹+(1+t/(1-t))^θ⁻¹)^2))=
      ∫ t in (0:ℝ)..1, (t*(1-t))^(θ⁻¹-1)/(1+t^θ⁻¹+(1-t)^θ⁻¹)^2 := by
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    exact gumbel_rho_odds_kernel θ⁻¹ ht
  rw [he]
  simp only [one_div]
  ring

end Verification
