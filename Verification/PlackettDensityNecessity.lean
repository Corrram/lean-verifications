import Verification.PlackettDensity
import Verification.PlackettConditional
import Verification.PlackettMinorPolynomial
import Verification.ContinuousDensityMinors
import Verification.MTP2ConditionalIncreasing

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem plackettDensity_continuousAt {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    ContinuousAt (fun p : I × I => plackettDensity θ p.1 p.2) (u,v) := by
  unfold plackettDensity
  apply ContinuousAt.div
  · fun_prop
  · unfold plackettD plackettA; fun_prop
  · exact pow_ne_zero _ (Real.sqrt_pos.mpr (plackettD_pos hθ u.property v.property)).ne'

theorem plackettDensity_zero {θ v : ℝ} (hθ : 0 < θ) (hv : v ∈ Icc 0 1) :
    plackettDensity θ 0 v = θ/(1+(θ-1)*v)^2 := by
  have hp : 0 < 1+(θ-1)*v := by
    by_cases h : 1 ≤ θ
    · nlinarith [mul_nonneg (sub_nonneg.mpr h) hv.1]
    · nlinarith [mul_nonneg (show 0 ≤ 1-θ by linarith) (sub_nonneg.mpr hv.2)]
  simp only [plackettDensity,plackettD,plackettA,zero_add,mul_zero,zero_mul,sub_zero]
  rw [Real.sqrt_sq hp.le]
  field_simp

theorem plackettDensity_one {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Icc 0 1) :
    plackettDensity θ u 1 = θ/(θ-(θ-1)*u)^2 := by
  have hp : 0 < θ-(θ-1)*u := by
    by_cases h : 1 ≤ θ
    · nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hu.2)]
    · nlinarith [mul_nonneg (show 0 ≤ 1-θ by linarith) hu.1]
  have hd : plackettD θ u 1 = (θ-(θ-1)*u)^2 := by unfold plackettD plackettA; ring
  rw [plackettDensity,hd,Real.sqrt_sq hp.le]
  field_simp
  ring

theorem plackett_minor_polynomial_nonneg {θ : ℝ} (hθ : 1 < θ)
    (hC : (plackett θ (by linarith)).HasMTP2Density) (t : I) (ht : 0 < (t:ℝ)) :
    0 ≤ plackettMinorPolynomial θ (θ-1) t := by
  have hp : 0 < θ := by linarith
  let f : (Fin 2 → I) → ℝ := fun x => plackettDensity θ (x 0) (x 1)
  have hm : Measurable f := by unfold f plackettDensity plackettD plackettA; fun_prop
  have hcont (u v : I) : ContinuousAt (fun p : I × I => f ![p.1,p.2]) (u,v) :=
    plackettDensity_continuousAt hp u v
  have hh := copula_continuous_density_minor hC f hm
    (fun x => plackettDensity_nonneg hp (x 0).property (x 1).property)
    (plackett_toMeasure_density hp hθ.ne') 0 t (unitInterval.symm t) 1
    (show (0:I)<t from ht) (by change 1-(t:ℝ)<1; linarith)
    (hcont _ _) (hcont _ _) (hcont _ _) (hcont _ _)
  change plackettDensity θ 0 1*plackettDensity θ t (1-(t:ℝ)) ≤
    plackettDensity θ 0 (1-(t:ℝ))*plackettDensity θ t 1 at hh
  have hsym : 1-(t:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by linarith [t.property.2],by linarith [t.property.1]⟩
  rw [plackettDensity_zero hp (by norm_num),plackettDensity_zero hp hsym,
    plackettDensity_one hp t.property] at hh
  let B := θ-(θ-1)*(t:ℝ)
  let D := θ^2-4*θ*(θ-1)*(t:ℝ)*(1-(t:ℝ))
  let N := θ-2*(θ-1)*(t:ℝ)*(1-(t:ℝ))
  have hB : 0 < B := by dsimp [B]; nlinarith [mul_nonneg (sub_nonneg.mpr hθ.le) (sub_nonneg.mpr t.property.2)]
  have hD : 0 < D := by
    convert plackettD_pos hp t.property hsym using 1
    dsimp [D,plackettD,plackettA]; ring
  have hN : 0 ≤ N := by
    have hh := mul_nonneg (sub_nonneg.mpr hθ.le) (sq_nonneg (2*(t:ℝ)-1))
    dsimp [N]; nlinarith
  have hden : plackettD θ t (1-(t:ℝ)) = D := by dsimp [D,plackettD,plackettA]; ring
  have hnum : 1+(θ-1)*((t:ℝ)+(1-(t:ℝ))-2*(t:ℝ)*(1-(t:ℝ))) = N := by dsimp [N]; ring
  have hb : 1+(θ-1)*(1-(t:ℝ)) = B := by dsimp [B]; ring
  have hb1 : 1+(θ-1)*1 = θ := by ring
  rw [hb,hb1,plackettDensity,hden,hnum] at hh
  change θ/θ^2*(θ*N/(Real.sqrt D)^3) ≤ θ/B^2*(θ/B^2) at hh
  have hroot := Real.sqrt_pos.mpr hD
  have hi : N*B^4 ≤ θ^2*(Real.sqrt D)^3 := by
    field_simp [hp.ne',hB.ne',hroot.ne'] at hh
    nlinarith [hh]
  have hisq := pow_le_pow_left₀ (mul_nonneg hN (pow_nonneg hB.le _)) hi 2
  have hpow : ((Real.sqrt D)^3)^2 = D^3 := by rw [← pow_mul, Nat.mul_comm 3 2,pow_mul,Real.sq_sqrt hD.le]
  have hn : 0 ≤ θ^4*D^3-N^2*B^8 := by
    simpa only [mul_pow,hpow,← pow_mul] using sub_nonneg.mpr hisq
  have he := plackettMinorPolynomial_identity θ (θ-1) (t:ℝ)
  change θ^4*D^3-N^2*B^8 = (t:ℝ)^2*plackettMinorPolynomial θ (θ-1) t at he
  rw [he] at hn
  exact nonneg_of_mul_nonneg_right hn (sq_pos_of_pos ht)

theorem plackett_density_tp2_requires_le_two {θ : ℝ} (hθ : 0 < θ)
    (hC : (plackett θ hθ).HasMTP2Density) : θ ≤ 2 := by
  by_contra hh
  have h2 : 2 < θ := lt_of_not_ge hh
  have hc : ContinuousAt (plackettMinorPolynomial θ (θ-1)) 0 := by
    unfold plackettMinorPolynomial; fun_prop
  have hn : 0 ≤ plackettMinorPolynomial θ (θ-1) 0 := by
    apply ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto _ (𝓝[>] (0:ℝ)) (𝓝 _))
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with t ht ht1
    exact plackett_minor_polynomial_nonneg (by linarith) hC ⟨t,ht.le,ht1.le⟩ ht
  rw [plackettMinorPolynomial_zero] at hn
  have hp : 0 < 8*θ^8*(θ-1) := mul_pos (by positivity) (by linarith)
  nlinarith

theorem plackett_density_tp2_necessary {θ : ℝ} (hθ : 0 < θ)
    (hC : (plackett θ hθ).HasMTP2Density) : θ ∈ Icc (1:ℝ) 2 :=
  ⟨(plackett_ci_iff hθ).mp (mtp2_isCI hC),plackett_density_tp2_requires_le_two hθ hC⟩

end Verification
