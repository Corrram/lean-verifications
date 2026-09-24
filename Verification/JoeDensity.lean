import Verification.JoeDensityShape
import Verification.InteriorDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def joeInv (θ u : ℝ) : ℝ := -Real.log (1-(1-u)^θ)
noncomputable def joeWeight (θ u : ℝ) : ℝ := θ*(1-u)^(θ-1)/(1-(1-u)^θ)
noncomputable def joeDensityReal (θ u v : ℝ) : ℝ :=
  if u ∈ Ioo 0 1 ∧ v ∈ Ioo 0 1 then
    joeSecond θ⁻¹ (joeInv θ u+joeInv θ v)*joeWeight θ u*joeWeight θ v else 0
noncomputable def joeDensity (θ : ℝ) (x : Fin 2 → I) : ℝ := joeDensityReal θ (x 0) (x 1)
noncomputable def joePartial (θ u v : ℝ) : ℝ :=
  -joePsiDeriv θ⁻¹ (joeInv θ u+joeInv θ v)*joeWeight θ u
noncomputable def joeRealCDF (θ u v : ℝ) : ℝ :=
  1-(1-Real.exp (-(joeInv θ u+joeInv θ v)))^θ⁻¹

theorem joe_inv_base {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) :
    0 < 1-(1-u)^θ ∧ 1-(1-u)^θ < 1 := by
  have h₁ := Real.rpow_lt_one (by linarith [hu.2] : 0 ≤ 1-u) (by linarith [hu.1] : 1-u < 1) hθ
  have h₂ := Real.rpow_pos_of_pos (by linarith [hu.2] : 0 < 1-u) θ
  constructor <;> linarith

theorem joeInv_pos {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) : 0 < joeInv θ u :=
  neg_pos.mpr (Real.log_neg (joe_inv_base hθ hu).1 (joe_inv_base hθ hu).2)

theorem joeWeight_pos {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) : 0 < joeWeight θ u :=
  div_pos (mul_pos hθ (Real.rpow_pos_of_pos (by linarith [hu.2]) _)) (joe_inv_base hθ hu).1

theorem joeInv_deriv {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) :
    HasDerivAt (joeInv θ) (-joeWeight θ u) u := by
  have hh := (((((hasDerivAt_id u).const_sub 1).rpow_const
    (p := θ) (Or.inl (by linarith [hu.2] : 1-u ≠ 0))).const_sub 1).log (joe_inv_base hθ hu).1.ne').neg
  convert hh using 1
  · rfl
  · dsimp [joeWeight]; ring

theorem joeWeight_continuousAt {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) :
    ContinuousAt (joeWeight θ) u := by
  have ha : ContinuousAt (fun x : ℝ => 1-x) u := continuousAt_const.sub continuousAt_id
  exact (continuousAt_const.mul (ha.rpow_const (Or.inl (by linarith [hu.2] : 1-u ≠ 0)))).div
    (continuousAt_const.sub (ha.rpow_const (Or.inl (by linarith [hu.2] : 1-u ≠ 0))))
    (joe_inv_base hθ hu).1.ne'

theorem joeSecond_continuousAt {p t : ℝ} (ht : 0 < t) : ContinuousAt (joeSecond p) t := by
  have he : ContinuousAt (fun x : ℝ => Real.exp (-x)) t :=
    Real.continuous_exp.continuousAt.comp (f := fun x : ℝ => -x) (x := t) continuousAt_id.neg
  have ha : 1-Real.exp (-t) ≠ 0 := ne_of_gt
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)))
  exact ((continuousAt_const.mul he).mul ((continuousAt_const.sub he).rpow_const (Or.inl ha))).mul
    (continuousAt_const.sub (continuousAt_const.mul he))

theorem joePartial_deriv {θ u v : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (joePartial θ u) (joeDensityReal θ u v) v := by
  have hh := (((joePsiDeriv_deriv (p := θ⁻¹) (add_pos (joeInv_pos hθ hu) (joeInv_pos hθ hv))).comp v
    ((joeInv_deriv hθ hv).const_add (joeInv θ u))).neg).mul_const (joeWeight θ u)
  convert hh using 1
  · rfl
  · simp only [joeDensityReal, ite_eq_left (And.intro hu hv)]
    ring

theorem joeRealCDF_deriv {θ u v : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (fun x => joeRealCDF θ x v) (joePartial θ u v) u := by
  have hh := (joePsi_deriv (p := θ⁻¹) (add_pos (joeInv_pos hθ hu) (joeInv_pos hθ hv))).comp u
    ((joeInv_deriv hθ hu).add_const (joeInv θ v))
  convert hh using 1
  · rfl
  · dsimp [joePartial]; ring

theorem joeDensity_measurable (θ : ℝ) : Measurable (joeDensity θ) := by
  unfold joeDensity joeDensityReal joeSecond joeInv joeWeight
  apply Measurable.ite
  · exact (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 0))).inter
      (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 1)))
  · fun_prop
  · exact measurable_const

theorem joeDensityReal_nonneg {θ : ℝ} (hθ : 1 ≤ θ) (u v : ℝ) : 0 ≤ joeDensityReal θ u v := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  unfold joeDensityReal
  split_ifs with h
  · exact mul_nonneg (mul_nonneg
      (joeSecond_pos (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hθ)
        (add_pos (joeInv_pos hp h.1) (joeInv_pos hp h.2))).le
      (joeWeight_pos hp h.1).le) (joeWeight_pos hp h.2).le
  · exact le_rfl

theorem joeDensityReal_continuousAt {θ u v : ℝ} (hθ : 0 < θ)
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    ContinuousAt (Function.uncurry (joeDensityReal θ)) (u,v) := by
  have hiu := (joeInv_deriv hθ hu).continuousAt.comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hiv := (joeInv_deriv hθ hv).continuousAt.comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hwu := (joeWeight_continuousAt hθ hu).comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hwv := (joeWeight_continuousAt hθ hv).comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hh := (((joeSecond_continuousAt (p := θ⁻¹)
    (add_pos (joeInv_pos hθ hu) (joeInv_pos hθ hv))).comp
      (f := fun x : ℝ × ℝ => joeInv θ x.1+joeInv θ x.2) (x := (u,v)) (hiu.add hiv)).mul hwu).mul hwv
  apply hh.congr_of_eventuallyEq
  have he : ∀ᶠ x : ℝ × ℝ in nhds (u,v), x.1 ∈ Ioo 0 1 ∧ x.2 ∈ Ioo 0 1 :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hu,hv⟩
  filter_upwards [he] with x hx
  simp [Function.uncurry, joeDensityReal, hx]

theorem joePartial_continuousAt {θ u v : ℝ} (hθ : 0 < θ)
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) : ContinuousAt (fun x => joePartial θ x v) u := by
  exact (((joePsiDeriv_deriv (p := θ⁻¹) (add_pos (joeInv_pos hθ hu) (joeInv_pos hθ hv))).continuousAt.comp
    (f := fun x => joeInv θ x+joeInv θ v) (x := u)
    ((joeInv_deriv hθ hu).continuousAt.add continuousAt_const)).neg).mul (joeWeight_continuousAt hθ hu)

theorem joe_toMeasure_density {θ : ℝ} (hθ : 1 ≤ θ) :
    (joe θ hθ).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (joeDensity θ x)) := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  apply copula_density_of_interior_derivatives (joe θ hθ) (joeDensityReal θ) (joeRealCDF θ) (joePartial θ)
  · intro u v; exact joeDensityReal_nonneg hθ u v
  · intro u v hu hv; exact joeDensityReal_continuousAt hp hu hv
  · intro u v hu hv; exact joePartial_continuousAt hp hu hv
  · intro u v hu hv; exact joeRealCDF_deriv hp hu hv
  · intro u v hu hv; exact joePartial_deriv hp hu hv
  · intro u v hu _ hv _
    have hu0 : u ≠ 0 := ne_of_gt (show (0:I) < u from hu)
    have hv0 : v ≠ 0 := ne_of_gt (show (0:I) < v from hv)
    rw [joe, BivariateGenerator.cdf_copula, BivariateGenerator.cdf]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hv0, false_or, ite_false]
    rfl

theorem joeDensity_mtp2 {θ : ℝ} (hθ : 1 ≤ θ) : IsMTP2 (joeDensity θ) := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  rw [Copula.isMTP2_fin_two_iff]
  intro a b c d hab hcd
  by_cases ha : (a:ℝ) ∈ Ioo 0 1
  swap
  · simp [joeDensity, joeDensityReal, ha]
  by_cases hb : (b:ℝ) ∈ Ioo 0 1
  swap
  · simp [joeDensity, joeDensityReal, hb]
  by_cases hc : (c:ℝ) ∈ Ioo 0 1
  swap
  · simp [joeDensity, joeDensityReal, hc]
  by_cases hd : (d:ℝ) ∈ Ioo 0 1
  swap
  · simp [joeDensity, joeDensityReal, hd]
  have ha0 : a ≠ 0 := ne_of_gt (show (0:I) < a from ha.1)
  have hc0 : c ≠ 0 := ne_of_gt (show (0:I) < c from hc.1)
  have hxy : joeInv θ b ≤ joeInv θ a := (joeGenerator θ hθ).inv_antitone a b ha0 hab
  have hzw : joeInv θ d ≤ joeInv θ c := (joeGenerator θ hθ).inv_antitone c d hc0 hcd
  have hi := convex_increment_pos (joeSecond_logconvex (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hθ))
    (joeInv_pos hp hb) (joeInv_pos hp hd).le hxy hzw
  have hlog : Real.log (joeSecond θ⁻¹ (joeInv θ a+joeInv θ d))+
      Real.log (joeSecond θ⁻¹ (joeInv θ b+joeInv θ c)) ≤
      Real.log (joeSecond θ⁻¹ (joeInv θ a+joeInv θ c))+
      Real.log (joeSecond θ⁻¹ (joeInv θ b+joeInv θ d)) := by linarith
  have hpos (u v : ℝ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :=
    joeSecond_pos (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hθ) (add_pos (joeInv_pos hp hu) (joeInv_pos hp hv))
  have he := Real.exp_le_exp.mpr hlog
  simp only [Real.exp_add, Real.exp_log (hpos a d ha hd), Real.exp_log (hpos b c hb hc),
    Real.exp_log (hpos a c ha hc), Real.exp_log (hpos b d hb hd)] at he
  have hw : 0 ≤ joeWeight θ a*joeWeight θ b*joeWeight θ c*joeWeight θ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (joeWeight_pos hp ha).le (joeWeight_pos hp hb).le)
      (joeWeight_pos hp hc).le) (joeWeight_pos hp hd).le
  have hh := mul_le_mul_of_nonneg_right he hw
  simp only [joeDensity, joeDensityReal, Matrix.cons_val_zero, Matrix.cons_val_one,
    ha, hb, hc, hd, and_self, ite_true]
  nlinarith only [hh]

theorem joe_hasMTP2Density {θ : ℝ} (hθ : 1 ≤ θ) : (joe θ hθ).HasMTP2Density :=
  ⟨joeDensity θ, joeDensity_measurable θ, fun x => joeDensityReal_nonneg hθ (x 0) (x 1),
    joeDensity_mtp2 hθ, joe_toMeasure_density hθ⟩

end Verification
