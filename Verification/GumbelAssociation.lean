import Verification.GumbelDensity
import Verification.KendallConditionalProduct
import Verification.ExponentialIntegral

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem integral_unit_neg_exp_rpow {p : ℝ} (hp : 0<p) (f : ℝ → ℝ) :
    (∫ u : I, f (u:ℝ)) = ∫ t in Ioi (0:ℝ),
      (p*t^(p-1))*Real.exp (-t^p)*f (Real.exp (-t^p)) := by
  rw [integral_unit_neg_exp]
  rw [← integral_comp_rpow_Ioi_of_pos (g := fun t => Real.exp (-t)*f (Real.exp (-t))) hp]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [smul_eq_mul,mul_assoc]

theorem gumbelInv_generator {θ t : ℝ} (hθ : 0<θ) (ht : 0<t) :
    gumbelInv θ (Real.exp (-t^θ⁻¹))=t := by
  unfold gumbelInv
  rw [Real.log_exp,neg_neg,← Real.rpow_mul ht.le,inv_mul_cancel₀ hθ.ne',Real.rpow_one]

theorem gumbelWeight_generator {θ t : ℝ} (hθ : 0<θ) (ht : 0<t) :
    (θ⁻¹*t^(θ⁻¹-1)*Real.exp (-t^θ⁻¹))*
      gumbelWeight θ (Real.exp (-t^θ⁻¹))=1 := by
  unfold gumbelWeight
  rw [Real.log_exp,neg_neg,← Real.rpow_mul ht.le]
  have he : θ⁻¹*(θ-1)=1-θ⁻¹ := by field_simp
  rw [he]
  have hp : t^(θ⁻¹-1)*t^(1-θ⁻¹)=1 := by
    rw [← Real.rpow_add ht]
    have hh : θ⁻¹-1+(1-θ⁻¹)=0 := by ring
    rw [hh,Real.rpow_zero]
  calc
    _ = (θ⁻¹*θ)*(t^(θ⁻¹-1)*t^(1-θ⁻¹))*
        (Real.exp (-t^θ⁻¹)/Real.exp (-t^θ⁻¹)) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hθ.ne',hp,div_self (Real.exp_ne_zero _)]; ring

theorem gumbel_product_generator {θ x y : ℝ} (hθ : 0<θ) (hx : 0<x) (hy : 0<y) :
    (θ⁻¹*x^(θ⁻¹-1)*Real.exp (-x^θ⁻¹))*
      ((θ⁻¹*y^(θ⁻¹-1)*Real.exp (-y^θ⁻¹))*
        (gumbelPartial θ (Real.exp (-x^θ⁻¹)) (Real.exp (-y^θ⁻¹))*
          gumbelPartial θ (Real.exp (-y^θ⁻¹)) (Real.exp (-x^θ⁻¹)))) =
      (gumbelPsiDeriv θ⁻¹ (x+y))^2 := by
  unfold gumbelPartial
  rw [gumbelInv_generator hθ hx,gumbelInv_generator hθ hy]
  rw [add_comm y x]
  calc
    _ = (gumbelPsiDeriv θ⁻¹ (x+y))^2 *
        ((θ⁻¹*x^(θ⁻¹-1)*Real.exp (-x^θ⁻¹))*gumbelWeight θ (Real.exp (-x^θ⁻¹))) *
        ((θ⁻¹*y^(θ⁻¹-1)*Real.exp (-y^θ⁻¹))*gumbelWeight θ (Real.exp (-y^θ⁻¹))) := by ring
    _ = _ := by rw [gumbelWeight_generator hθ hx,gumbelWeight_generator hθ hy]; ring

theorem gumbel_cdfSection_deriv {θ : ℝ} (hθ : 1≤θ) (v : I)
    (hv : (v:ℝ)∈Ioo 0 1) (u : ℝ) (hu : u∈Ioo 0 1) :
    HasDerivAt (cdfSection (gumbel θ hθ) v) (gumbelPartial θ u v) u := by
  apply (gumbelRealCDF_deriv hu hv).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
  have hx0 : (⟨x,hx.1.le,hx.2.le⟩:I)≠0 := by
    intro he
    have := congrArg (fun z : I => (z:ℝ)) he
    exact hx.1.ne' this
  have hv0 : v≠0 := by
    intro he
    exact hv.1.ne' (congrArg (fun z : I => (z:ℝ)) he)
  simp only [cdfSection,projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩]
  rw [gumbel,BivariateGenerator.cdf_copula,BivariateGenerator.cdf]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,hx0,hv0,false_or,ite_false]
  rfl

theorem gumbel_conditionalCDF {θ : ℝ} (hθ : 1≤θ) (v : I)
    (hv : (v:ℝ)∈Ioo 0 1) :
    (fun u => (gumbel θ hθ).conditionalCDF u v) =ᵐ[volume]
      fun u => gumbelPartial θ u v := by
  filter_upwards [(gumbel θ hθ).conditionalCDF_eq_deriv v,
    Measure.ae_ne volume (0:I),Measure.ae_ne volume (1:I)] with u hu hu0 hu1
  rw [hu]
  have h0 : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have h1 : (u:ℝ)<1 := lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))
  exact (gumbel_cdfSection_deriv hθ v hv u ⟨h0,h1⟩).deriv

theorem gumbel_transpose {θ : ℝ} (hθ : 1≤θ) :
    (gumbel θ hθ).transpose=gumbel θ hθ := by
  apply Copula.ext_cdf
  intro z
  have hz : z=![z 0,z 1] := by funext i; fin_cases i <;> rfl
  rw [hz,cdf_transpose,gumbel,BivariateGenerator.cdf_copula,BivariateGenerator.cdf_copula]
  simp only [BivariateGenerator.cdf,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [or_comm,add_comm]
  rfl

theorem gumbel_conditionalCDF_ae {θ : ℝ} (hθ : 1≤θ) :
    ∀ᵐ v : I, ∀ᵐ u : I, (gumbel θ hθ).conditionalCDF u v=gumbelPartial θ u v := by
  filter_upwards [Measure.ae_ne (volume : Measure I) 0,
    Measure.ae_ne (volume : Measure I) 1] with v hv0 hv1
  have h0 : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv0 (Subtype.ext h)))
  have h1 : (v:ℝ)<1 := lt_of_le_of_ne v.property.2 (fun h => hv1 (Subtype.ext h))
  exact gumbel_conditionalCDF hθ v ⟨h0,h1⟩

theorem gumbel_kendallTau_integral {θ : ℝ} (hθ : 1≤θ) :
    (gumbel θ hθ).kendallTau =
      1-4*(∫ u : I, ∫ v : I, gumbelPartial θ u v*gumbelPartial θ v u) := by
  have ha := gumbel_conditionalCDF_ae hθ
  have hb : ∀ᵐ u : I, ∀ᵐ v : I, (gumbel θ hθ).conditionalCDF u v=gumbelPartial θ u v := by
    apply (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun u v => (gumbel θ hθ).conditionalCDF u v=gumbelPartial θ u v)
      (measurableSet_eq_fun ((gumbel θ hθ).measurable_conditionalCDF.comp measurable_swap)
        (by unfold gumbelPartial gumbelPsiDeriv gumbelInv gumbelWeight; fun_prop))).mpr
    exact ha
  rw [kendallTau_conditional_product,gumbel_transpose hθ]
  congr 2
  apply integral_congr_ae
  filter_upwards [ha,hb] with u hu hu'
  apply integral_congr_ae
  filter_upwards [hu,hu'] with v hv hv'
  rw [hv,hv']

theorem gumbel_kendallTau_generator_integral {θ : ℝ} (hθ : 1≤θ) :
    (gumbel θ hθ).kendallTau =
      1-4*(∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), (gumbelPsiDeriv θ⁻¹ (x+y))^2) := by
  have hp : 0<θ⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hθ)
  rw [gumbel_kendallTau_integral hθ]
  have hv (u : ℝ) := integral_unit_neg_exp_rpow hp
    (fun v => gumbelPartial θ u v*gumbelPartial θ v u)
  simp_rw [hv]
  rw [integral_unit_neg_exp_rpow hp (fun u => ∫ t in Ioi (0:ℝ),
    θ⁻¹*t^(θ⁻¹-1)*Real.exp (-t^θ⁻¹)*
      (gumbelPartial θ u (Real.exp (-t^θ⁻¹))*gumbelPartial θ (Real.exp (-t^θ⁻¹)) u))]
  congr 2
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  simpa only [mul_assoc] using gumbel_product_generator
    (lt_of_lt_of_le zero_lt_one hθ) hx hy

end Verification
