import Verification.Nelsen16Necessity
import Verification.ContinuousDensityMinors
import Verification.MTP2ConditionalIncreasing

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n16RawDensity (θ : ℝ) (p : I × I) : ℝ :=
  n16Second θ (n16Inv θ p.1+n16Inv θ p.2)*n16Weight θ p.1*n16Weight θ p.2

theorem n16RawDensity_continuousAt {θ : ℝ} (hθ : 0 < θ) (u v : I)
    (hu : 0 < (u:ℝ)) (hv : 0 < (v:ℝ)) : ContinuousAt (n16RawDensity θ) (u,v) := by
  have hu' : ContinuousAt (fun p : I × I => (p.1:ℝ)) (u,v) := by fun_prop
  have hv' : ContinuousAt (fun p : I × I => (p.2:ℝ)) (u,v) := by fun_prop
  exact (((n16Second_continuousAt hθ).comp
    (((n16Inv_deriv_pos hu).continuousAt.comp (f := fun p : I × I => (p.1:ℝ)) (x := (u,v)) hu').add
      ((n16Inv_deriv_pos hv).continuousAt.comp (f := fun p : I × I => (p.2:ℝ)) (x := (u,v)) hv'))).mul
    ((n16Weight_deriv hu).continuousAt.comp (f := fun p : I × I => (p.1:ℝ)) (x := (u,v)) hu')).mul
    ((n16Weight_deriv hv).continuousAt.comp (f := fun p : I × I => (p.2:ℝ)) (x := (u,v)) hv')

theorem n16RawDensity_ae_minors {θ : ℝ} (hθ : 0 < θ)
    (hC : (nelsen16 θ hθ.le).HasMTP2Density) :
    HasAEOrderedMinors 1 (fun u v => n16RawDensity θ (u,v)) := by
  obtain ⟨g,hg,hgn,hgt,hgd⟩ := hC
  have he := density_ae_eq hg (n16Density_measurable θ) hgn
    (fun x => n16DensityReal_nonneg hθ (x 0) (x 1))
    (hgd.symm.trans (n16_toMeasure_density hθ))
  apply ((aeOrderedMinors_of_tp2 ((Copula.isMTP2_fin_two_iff g).mp hgt)).congr
    (ae_curry_of_ae_eq he)).congr
  filter_upwards [volume.ae_ne (0:I), volume.ae_ne (1:I)] with u hu0 hu1
  filter_upwards [volume.ae_ne (0:I), volume.ae_ne (1:I)] with v hv0 hv1
  have hu : (u:ℝ) ∈ Ioo 0 1 := ⟨lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu0)),
    lt_of_le_of_ne u.property.2 (unitInterval.coe_ne_one.mpr hu1)⟩
  have hv : (v:ℝ) ∈ Ioo 0 1 := ⟨lt_of_le_of_ne v.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hv0)),
    lt_of_le_of_ne v.property.2 (unitInterval.coe_ne_one.mpr hv1)⟩
  simp [n16Density, n16DensityReal, n16RawDensity, hu, hv]

theorem n16_second_midpoint_of_mtp2 {θ : ℝ} (hθ : 0 < θ)
    (hC : (nelsen16 θ hθ.le).HasMTP2Density) (u : I) (hu : 0 < (u:ℝ)) (hu1 : u < 1) :
    n16Second θ (n16Inv θ u)^2 ≤ n16Second θ (2*n16Inv θ u)*n16Second θ 0 := by
  have hm : Measurable (n16RawDensity θ) := by
    unfold n16RawDensity n16Second n16Inv n16Rad n16Weight
    fun_prop
  have hh := continuous_density_minor_of_ae (n16RawDensity θ) hm
    (n16RawDensity_ae_minors hθ hC) u 1 u 1 hu1 hu1
    (n16RawDensity_continuousAt hθ u u hu hu)
    (n16RawDensity_continuousAt hθ u 1 hu (by norm_num))
    (n16RawDensity_continuousAt hθ 1 u (by norm_num) hu)
    (n16RawDensity_continuousAt hθ 1 1 (by norm_num) (by norm_num))
  have hz : n16Inv θ 1 = 0 := by simp [n16Inv]
  simp only [n16RawDensity, show ((1:I):ℝ) = 1 from rfl, hz, add_zero, zero_add,
    ← two_mul, mul_zero] at hh
  have hw : 0 < n16Weight θ u^2*n16Weight θ 1^2 :=
    mul_pos (sq_pos_of_pos (n16Weight_pos hθ)) (sq_pos_of_pos (n16Weight_pos hθ))
  apply (mul_le_mul_iff_left₀ hw).mp
  nlinarith only [hh]

theorem n16_rad_polynomial_of_second_midpoint {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t)
    (hh : n16Second θ t^2 ≤ n16Second θ (2*t)*n16Second θ 0) :
    0 ≤ t^2-4*(1-θ)*t+2*(1-θ)^2-8*θ := by
  have hp : 0 < n16Rad θ t := n16Rad_pos hθ
  have hp0 : 0 < n16Rad θ 0 := n16Rad_pos hθ
  have hp2 : 0 < n16Rad θ (2*t) := n16Rad_pos hθ
  have hh' : (2*θ)^2/(n16Rad θ t^3)^2 ≤
      (2*θ)^2/(n16Rad θ (2*t)^3*n16Rad θ 0^3) := by
    simpa only [n16Second, div_pow, ← mul_div_mul_comm, ← sq] using hh
  have hx := (div_le_div_iff₀ (sq_pos_of_pos (pow_pos hp 3))
    (mul_pos (pow_pos hp2 3) (pow_pos hp0 3))).mp hh'
  have hy : (n16Rad θ (2*t)*n16Rad θ 0)^3 ≤ (n16Rad θ t^2)^3 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (show 0 < 2*θ by positivity))).mp
    nlinarith only [hx]
  have hz := (pow_le_pow_iff_left₀ (mul_pos hp2 hp0).le (sq_nonneg (n16Rad θ t))
    (by norm_num : (3:ℕ) ≠ 0)).mp hy
  have hz2 := pow_le_pow_left₀ (mul_pos hp2 hp0).le hz 2
  have he : (n16Rad θ t^2)^2-(n16Rad θ (2*t)*n16Rad θ 0)^2 =
      t^2*(t^2-4*(1-θ)*t+2*(1-θ)^2-8*θ) := by
    rw [mul_pow, n16Rad_sq hθ.le, n16Rad_sq hθ.le, n16Rad_sq hθ.le]
    ring
  have hh0 : 0 ≤ t^2*(t^2-4*(1-θ)*t+2*(1-θ)^2-8*θ) := by
    rw [← he]
    exact sub_nonneg.mpr hz2
  exact nonneg_of_mul_nonneg_right hh0 (sq_pos_of_pos ht)

theorem n16_density_necessary_polynomial {θ : ℝ} (hθ : 0 < θ)
    (hC : (nelsen16 θ hθ.le).HasMTP2Density) : 4*θ ≤ (θ-1)^2 := by
  let F : ℝ → ℝ := fun u => (n16Inv θ u)^2-4*(1-θ)*n16Inv θ u+2*(1-θ)^2-8*θ
  have hc : ContinuousAt F 1 := by
    have hi := (n16Inv_deriv_pos (θ := θ) (by norm_num : (0:ℝ) < 1)).continuousAt
    exact ((hi.pow 2).sub (hi.const_mul (4*(1-θ)))).add_const (2*(1-θ)^2) |>.sub_const (8*θ)
  have hn : 0 ≤ F 1 := by
    apply ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds : Tendsto F (𝓝[<] (1:ℝ)) (𝓝 (F 1)))
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1))] with u hu hu0
    have hu1 : u < 1 := hu
    exact n16_rad_polynomial_of_second_midpoint hθ (n16Inv_pos hθ ⟨hu0,hu1⟩)
      (n16_second_midpoint_of_mtp2 hθ hC ⟨u,⟨hu0.le,hu1.le⟩⟩ hu0 hu1)
  dsimp [F, n16Inv] at hn
  nlinarith

theorem nelsen16_density_tp2_iff (θ : ℝ) (hθ : 0 ≤ θ) :
    (nelsen16 θ hθ).HasMTP2Density ↔ 3+2*Real.sqrt 2 ≤ θ := by
  constructor
  · intro hC
    have h3 := (nelsen16_ci_iff θ hθ).mp (mtp2_isCI hC)
    have hp : 0 < θ := by linarith
    have hh := n16_density_necessary_polynomial hp hC
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hs0 := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  · exact n16_hasMTP2Density

end Verification
