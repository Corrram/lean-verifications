import Verification.GumbelBarnettDependence
import Verification.CuadrasAugeRho
import Copula.Rank.ConditionalDerivative
import Verification.ExponentialIntegral

open ProbabilityTheory MeasureTheory Set Filter
open Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def gbExponent (θ v : I) : ℝ := 1-(θ:ℝ)*Real.log (v:ℝ)

theorem gbExponent_ge_one (θ v : I) : 1 ≤ gbExponent θ v := by
  have hl := Real.log_nonpos v.property.1 v.property.2
  dsimp [gbExponent]
  nlinarith [θ.property.1]

noncomputable def gbConditional (θ u v : I) : ℝ :=
  (v:ℝ)*gbExponent θ v*(u:ℝ)^(gbExponent θ v-1)

theorem gumbelBarnett_conditionalCDF (θ v : I) :
    (fun u => (gumbelBarnett θ).conditionalCDF u v) =ᵐ[volume]
      fun u => gbConditional θ u v := by
  filter_upwards [(gumbelBarnett θ).conditionalCDF_eq_deriv v,
    Measure.ae_ne volume (0:I), Measure.ae_ne volume (1:I)] with u hu hu0 hu1
  rw [hu]
  have h0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1
    (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have h1 : (u:ℝ) < 1 := lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))
  have he : cdfSection (gumbelBarnett θ) v =ᶠ[𝓝 (u:ℝ)]
      (fun x : ℝ => (v:ℝ)*x^(gbExponent θ v)) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with x hx
    have hh := gumbelBarnett_cdf_power θ (⟨x,hx.1.le,hx.2.le⟩:I) v
    simpa only [cdfSection, projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩,
      gbExponent] using hh
  have hd := ((hasDerivAt_id (u:ℝ)).rpow_const (p := gbExponent θ v) (Or.inl h0.ne')).const_mul (v:ℝ)
  convert (hd.congr_of_eventuallyEq he).deriv using 1
  dsimp [gbConditional]
  ring

theorem integral_gbConditional_sq (θ v : I) :
    (∫ u : I, gbConditional θ u v^2) =
      (v:ℝ)^2*(gbExponent θ v)^2/(2*gbExponent θ v-1) := by
  have hp : 0 ≤ 2*(gbExponent θ v-1) := by linarith [gbExponent_ge_one θ v]
  have he (u : I) : gbConditional θ u v^2 =
      ((v:ℝ)*gbExponent θ v)^2*(u:ℝ)^(2*(gbExponent θ v-1)) := by
    unfold gbConditional
    rw [mul_pow, ← Real.rpow_mul_natCast u.property.1]
    congr 2
    norm_num
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_unit_rpow_nonneg _ hp]
  have hden : 2*(gbExponent θ v-1)+1 = 2*gbExponent θ v-1 := by ring
  rw [hden]
  ring

theorem gumbelBarnett_xi_integral (θ : I) :
    (gumbelBarnett θ).chatterjeeXi =
      6*(∫ v : I, (v:ℝ)^2*(gbExponent θ v)^2/(2*gbExponent θ v-1))-2 := by
  unfold chatterjeeXi
  congr 2
  apply integral_congr_ae
  exact Eventually.of_forall fun v =>
    (integral_congr_ae ((gumbelBarnett_conditionalCDF θ v).fun_comp (fun x => x^2))).trans
      (integral_gbConditional_sq θ v)

theorem gumbelBarnett_chatterjeeXi (θ : I) (hθ : 0 < (θ:ℝ)) :
    (gumbelBarnett θ).chatterjeeXi =
      3*Real.exp (3/(2*(θ:ℝ)))/(4*(θ:ℝ))*
        exponentialIntegralE1 (3/(2*(θ:ℝ)))+(θ:ℝ)/3-1/2 := by
  rw [gumbelBarnett_xi_integral]
  unfold gbExponent
  rw [integral_unit_neg_exp (fun v : ℝ =>
    v^2*(1-(θ:ℝ)*Real.log v)^2/(2*(1-(θ:ℝ)*Real.log v)-1))]
  have he (t : ℝ) : Real.exp (-t) *
      (Real.exp (-t)^2*(1-(θ:ℝ)*Real.log (Real.exp (-t)))^2 /
        (2*(1-(θ:ℝ)*Real.log (Real.exp (-t)))-1)) =
      Real.exp (-3*t)*(1+(θ:ℝ)*t)^2/(1+2*(θ:ℝ)*t) := by
    rw [Real.log_exp]
    have hx : Real.exp (-3*t) = Real.exp (-t)*Real.exp (-t)^2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [hx]
    ring
  simp_rw [he]
  rw [integral_gb_exponential (θ:ℝ) hθ]
  ring

end Verification
