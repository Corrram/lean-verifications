import Copula.Rank.Integration
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory ProbabilityTheory Set Real
open scoped unitInterval

namespace Verification

/-- The classical real exponential integral in the source's convention. -/
noncomputable def exponentialIntegralE1 (a : ℝ) : ℝ :=
  ∫ s in Ioi (1:ℝ), Real.exp (-a*s)/s

theorem integral_unit_neg_exp (f : ℝ → ℝ) :
    (∫ u : I, f (u:ℝ)) = ∫ t in Ioi (0:ℝ), Real.exp (-t)*f (Real.exp (-t)) := by
  have himage : (fun t : ℝ => Real.exp (-t)) '' Ioi 0 = Ioo 0 1 := by
    ext u
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)⟩
    · intro hu
      refine ⟨-Real.log u, ?_, ?_⟩
      · exact neg_pos.mpr (Real.log_neg hu.1 hu.2)
      · simp [Real.exp_log hu.1]
  have hinj : InjOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    intro x _ y _ h
    exact neg_injective (Real.exp_injective h)
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t (_ : t ∈ Ioi (0:ℝ)) =>
      ((hasDerivAt_neg t).exp).hasDerivWithinAt) hinj f
  rw [himage] at hj
  rw [Copula.integral_unitInterval f, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  simpa only [mul_neg_one, abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul] using hj

theorem integral_exp_three : (∫ t in Ioi (0:ℝ), Real.exp (-3*t)) = 1/3 := by
  simpa using integral_exp_mul_Ioi (a := -3) (by norm_num) 0

theorem integral_t_exp_three : (∫ t in Ioi (0:ℝ), t*Real.exp (-3*t)) = 1/9 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 3)
    (by norm_num) (by norm_num)
  norm_num [show (2:ℝ) = (1:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial] at h
  simpa [neg_mul] using h

theorem integrable_exp_three : IntegrableOn (fun t : ℝ => Real.exp (-3*t)) (Ioi 0) :=
  integrableOn_exp_mul_Ioi (by norm_num : (-3:ℝ) < 0) 0

theorem integrable_t_exp_three : IntegrableOn (fun t : ℝ => t*Real.exp (-3*t)) (Ioi 0) := by
  by_contra h
  have he := integral_t_exp_three
  rw [integral_undef h] at he
  norm_num at he

theorem integrable_exp_three_div {θ : ℝ} (hθ : 0 ≤ θ) :
    IntegrableOn (fun t : ℝ => Real.exp (-3*t)/(1+2*θ*t)) (Ioi 0) := by
  apply integrable_exp_three.mono'
  · exact ((by fun_prop : Measurable (fun t : ℝ => Real.exp (-3*t)/(1+2*θ*t)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hd : 1 ≤ 1+2*θ*t := by nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le (by linarith))]
    exact div_le_self (Real.exp_pos _).le hd

theorem integral_exp_three_div {θ : ℝ} (hθ : 0 < θ) :
    (∫ t in Ioi (0:ℝ), Real.exp (-3*t)/(1+2*θ*t)) =
      Real.exp (3/(2*θ))/(2*θ)*exponentialIntegralE1 (3/(2*θ)) := by
  have himage : (fun t : ℝ => 1+2*θ*t) '' Ioi 0 = Ioi 1 := by
    ext s
    constructor
    · rintro ⟨t,ht,rfl⟩
      change 1 < 1+2*θ*t
      exact lt_add_of_pos_right 1 (mul_pos (by positivity) ht)
    · intro hs
      refine ⟨(s-1)/(2*θ), ?_, ?_⟩
      · change 0 < (s-1)/(2*θ)
        exact div_pos (sub_pos.mpr hs) (by positivity)
      field_simp
      ring
  have hinj : InjOn (fun t : ℝ => 1+2*θ*t) (Ioi 0) := by
    intro x _ y _ he
    nlinarith
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => 1+2*θ*x) (2*θ) t := by
    convert ((hasDerivAt_id t).const_mul (2*θ)).const_add 1 using 1 <;> simp
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t (_ : t ∈ Ioi (0:ℝ)) => (hd t).hasDerivWithinAt) hinj
    (fun s => Real.exp (-(3/(2*θ))*s)/s)
  rw [himage] at hj
  change exponentialIntegralE1 (3/(2*θ)) = _ at hj
  have he (t : ℝ) : |2*θ| • (Real.exp (-(3/(2*θ))*(1+2*θ*t))/(1+2*θ*t)) =
      (2*θ*Real.exp (-(3/(2*θ)))) * (Real.exp (-3*t)/(1+2*θ*t)) := by
    rw [abs_of_pos (by positivity : 0 < 2*θ), smul_eq_mul]
    have ha : -(3/(2*θ))*(1+2*θ*t) = -(3/(2*θ))+(-3*t) := by field_simp; ring
    rw [ha, Real.exp_add]
    ring
  simp_rw [he] at hj
  rw [integral_const_mul] at hj
  have hp : Real.exp (3/(2*θ))*Real.exp (-(3/(2*θ))) = 1 := by
    rw [← Real.exp_add]; simp
  rw [hj]
  have hfac : Real.exp (3/(2*θ))/(2*θ)*(2*θ*Real.exp (-(3/(2*θ)))) = 1 := by
    calc
      _ = Real.exp (3/(2*θ))*Real.exp (-(3/(2*θ))) := by field_simp
      _ = 1 := hp
  rw [← mul_assoc, hfac, one_mul]

theorem integral_gb_exponential (θ : ℝ) (hθ : 0 < θ) :
    (∫ t in Ioi (0:ℝ), Real.exp (-3*t)*(1+θ*t)^2/(1+2*θ*t)) =
      θ/18+1/4+Real.exp (3/(2*θ))/(8*θ)*exponentialIntegralE1 (3/(2*θ)) := by
  have he : (∫ t in Ioi (0:ℝ), Real.exp (-3*t)*(1+θ*t)^2/(1+2*θ*t)) =
      ∫ t in Ioi (0:ℝ), θ/2*(t*Real.exp (-3*t)) +
        (3/4)*Real.exp (-3*t) + (1/4)*(Real.exp (-3*t)/(1+2*θ*t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    have hd : 1+2*θ*t ≠ 0 := ne_of_gt (by nlinarith : 0 < 1+2*θ*t)
    have hp : (1+θ*t)^2/(1+2*θ*t) = θ*t/2+3/4+(1/4)/(1+2*θ*t) := by
      field_simp [hd]
      ring
    calc
      _ = Real.exp (-3*t)*((1+θ*t)^2/(1+2*θ*t)) := by ring
      _ = _ := by rw [hp]; ring
  rw [he]
  rw [integral_add, integral_add]
  · simp only [integral_const_mul]
    rw [integral_t_exp_three, integral_exp_three, integral_exp_three_div hθ]
    ring
  · exact integrable_t_exp_three.const_mul (θ/2)
  · exact integrable_exp_three.const_mul (3/4)
  · exact (integrable_t_exp_three.const_mul (θ/2)).add (integrable_exp_three.const_mul (3/4))
  · exact (integrable_exp_three_div hθ.le).const_mul (1/4)

end Verification
