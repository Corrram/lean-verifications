import Verification.GumbelDensityShape
import Verification.InteriorDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def gumbelInv (θ u : ℝ) : ℝ := (-Real.log u)^θ
noncomputable def gumbelWeight (θ u : ℝ) : ℝ := θ*(-Real.log u)^(θ-1)/u
noncomputable def gumbelDensityReal (θ u v : ℝ) : ℝ :=
  if u ∈ Ioo 0 1 ∧ v ∈ Ioo 0 1 then
    gumbelSecond θ⁻¹ (gumbelInv θ u+gumbelInv θ v)*gumbelWeight θ u*gumbelWeight θ v else 0
noncomputable def gumbelDensity (θ : ℝ) (x : Fin 2 → I) : ℝ := gumbelDensityReal θ (x 0) (x 1)
noncomputable def gumbelPartial (θ u v : ℝ) : ℝ :=
  -gumbelPsiDeriv θ⁻¹ (gumbelInv θ u+gumbelInv θ v)*gumbelWeight θ u
noncomputable def gumbelRealCDF (θ u v : ℝ) : ℝ :=
  Real.exp (-(gumbelInv θ u+gumbelInv θ v)^θ⁻¹)

theorem gumbelInv_pos {θ u : ℝ} (hu : u ∈ Ioo 0 1) : 0 < gumbelInv θ u :=
  Real.rpow_pos_of_pos (neg_pos.mpr (Real.log_neg hu.1 hu.2)) _

theorem gumbelWeight_pos {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) : 0 < gumbelWeight θ u :=
  div_pos (mul_pos hθ (Real.rpow_pos_of_pos (neg_pos.mpr (Real.log_neg hu.1 hu.2)) _)) hu.1

theorem gumbelInv_deriv {θ u : ℝ} (hu : u ∈ Ioo 0 1) :
    HasDerivAt (gumbelInv θ) (-gumbelWeight θ u) u := by
  have hh := ((Real.hasDerivAt_log hu.1.ne').neg).rpow_const
    (p := θ) (Or.inl (neg_pos.mpr (Real.log_neg hu.1 hu.2)).ne')
  convert hh using 1
  · rfl
  · dsimp [gumbelWeight]; ring

theorem gumbelWeight_continuousAt {θ u : ℝ} (hu : u ∈ Ioo 0 1) :
    ContinuousAt (gumbelWeight θ) u := by
  have ha : ContinuousAt (fun x : ℝ => -Real.log x) u := (Real.continuousAt_log hu.1.ne').neg
  exact (continuousAt_const.mul (ha.rpow_const (Or.inl (neg_pos.mpr (Real.log_neg hu.1 hu.2)).ne'))).div
    continuousAt_id hu.1.ne'

theorem gumbelSecond_continuousAt {p t : ℝ} (ht : 0 < t) : ContinuousAt (gumbelSecond p) t := by
  have hP : ContinuousAt (fun x : ℝ => x^p) t := continuousAt_id.rpow_const (Or.inl ht.ne')
  have hE : ContinuousAt (fun x : ℝ => Real.exp (-x^p)) t :=
    Real.continuous_exp.continuousAt.comp (f := fun x : ℝ => -x^p) (x := t) hP.neg
  exact (((continuousAt_const.mul hP).div (continuousAt_id.pow 2) (pow_ne_zero _ ht.ne')).mul
    ((continuousAt_const.mul hP).sub continuousAt_const |>.add continuousAt_const)).mul hE

theorem gumbelPartial_deriv {θ u v : ℝ} (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (gumbelPartial θ u) (gumbelDensityReal θ u v) v := by
  have hh := (((gumbelPsiDeriv_deriv (p := θ⁻¹) (add_pos (gumbelInv_pos (θ := θ) hu) (gumbelInv_pos (θ := θ) hv))).comp v
    ((gumbelInv_deriv (θ := θ) hv).const_add (gumbelInv θ u))).neg).mul_const (gumbelWeight θ u)
  convert hh using 1
  · rfl
  · simp only [gumbelDensityReal, ite_eq_left (And.intro hu hv)]
    ring

theorem gumbelRealCDF_deriv {θ u v : ℝ} (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (fun x => gumbelRealCDF θ x v) (gumbelPartial θ u v) u := by
  have hh := (gumbelPsi_deriv (p := θ⁻¹) (add_pos (gumbelInv_pos (θ := θ) hu) (gumbelInv_pos (θ := θ) hv))).comp u
    ((gumbelInv_deriv (θ := θ) hu).add_const (gumbelInv θ v))
  convert hh using 1
  · rfl
  · dsimp [gumbelPartial]; ring

theorem gumbelDensity_measurable (θ : ℝ) : Measurable (gumbelDensity θ) := by
  unfold gumbelDensity gumbelDensityReal gumbelSecond gumbelInv gumbelWeight
  apply Measurable.ite
  · exact (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 0))).inter
      (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 1)))
  · fun_prop
  · exact measurable_const

theorem gumbelDensityReal_nonneg {θ : ℝ} (hθ : 1 ≤ θ) (u v : ℝ) : 0 ≤ gumbelDensityReal θ u v := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  unfold gumbelDensityReal
  split_ifs with h
  · exact mul_nonneg (mul_nonneg
      (gumbelSecond_pos (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hθ)
        (add_pos (gumbelInv_pos (θ := θ) h.1) (gumbelInv_pos (θ := θ) h.2))).le
      (gumbelWeight_pos hp h.1).le) (gumbelWeight_pos hp h.2).le
  · exact le_rfl

theorem gumbelDensityReal_continuousAt {θ u v : ℝ}
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    ContinuousAt (Function.uncurry (gumbelDensityReal θ)) (u,v) := by
  have hiu := (gumbelInv_deriv (θ := θ) hu).continuousAt.comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hiv := (gumbelInv_deriv (θ := θ) hv).continuousAt.comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hwu := (gumbelWeight_continuousAt (θ := θ) hu).comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hwv := (gumbelWeight_continuousAt (θ := θ) hv).comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hh := (((gumbelSecond_continuousAt (p := θ⁻¹)
    (add_pos (gumbelInv_pos (θ := θ) hu) (gumbelInv_pos (θ := θ) hv))).comp
      (f := fun x : ℝ × ℝ => gumbelInv θ x.1+gumbelInv θ x.2) (x := (u,v)) (hiu.add hiv)).mul hwu).mul hwv
  apply hh.congr_of_eventuallyEq
  have he : ∀ᶠ x : ℝ × ℝ in nhds (u,v), x.1 ∈ Ioo 0 1 ∧ x.2 ∈ Ioo 0 1 :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hu,hv⟩
  filter_upwards [he] with x hx
  simp [Function.uncurry, gumbelDensityReal, hx]

theorem gumbelPartial_continuousAt {θ u v : ℝ}
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) : ContinuousAt (fun x => gumbelPartial θ x v) u := by
  exact (((gumbelPsiDeriv_deriv (p := θ⁻¹) (add_pos (gumbelInv_pos (θ := θ) hu) (gumbelInv_pos (θ := θ) hv))).continuousAt.comp
    (f := fun x => gumbelInv θ x+gumbelInv θ v) (x := u)
    ((gumbelInv_deriv (θ := θ) hu).continuousAt.add continuousAt_const)).neg).mul (gumbelWeight_continuousAt (θ := θ) hu)

theorem gumbel_toMeasure_density {θ : ℝ} (hθ : 1 ≤ θ) :
    (gumbel θ hθ).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (gumbelDensity θ x)) := by
  apply copula_density_of_interior_derivatives (gumbel θ hθ) (gumbelDensityReal θ) (gumbelRealCDF θ) (gumbelPartial θ)
  · intro u v; exact gumbelDensityReal_nonneg hθ u v
  · intro u v hu hv; exact gumbelDensityReal_continuousAt hu hv
  · intro u v hu hv; exact gumbelPartial_continuousAt hu hv
  · intro u v hu hv; exact gumbelRealCDF_deriv hu hv
  · intro u v hu hv; exact gumbelPartial_deriv hu hv
  · intro u v hu _ hv _
    have hu0 : u ≠ 0 := ne_of_gt (show (0:I) < u from hu)
    have hv0 : v ≠ 0 := ne_of_gt (show (0:I) < v from hv)
    rw [gumbel, BivariateGenerator.cdf_copula, BivariateGenerator.cdf]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hv0, false_or, ite_false]
    rfl

theorem gumbelDensity_mtp2 {θ : ℝ} (hθ : 1 ≤ θ) : IsMTP2 (gumbelDensity θ) := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  rw [Copula.isMTP2_fin_two_iff]
  intro a b c d hab hcd
  by_cases ha : (a:ℝ) ∈ Ioo 0 1
  swap
  · simp [gumbelDensity, gumbelDensityReal, ha]
  by_cases hb : (b:ℝ) ∈ Ioo 0 1
  swap
  · simp [gumbelDensity, gumbelDensityReal, hb]
  by_cases hc : (c:ℝ) ∈ Ioo 0 1
  swap
  · simp [gumbelDensity, gumbelDensityReal, hc]
  by_cases hd : (d:ℝ) ∈ Ioo 0 1
  swap
  · simp [gumbelDensity, gumbelDensityReal, hd]
  have ha0 : a ≠ 0 := ne_of_gt (show (0:I) < a from ha.1)
  have hc0 : c ≠ 0 := ne_of_gt (show (0:I) < c from hc.1)
  have hxy : gumbelInv θ b ≤ gumbelInv θ a := (gumbelGenerator θ hθ).inv_antitone a b ha0 hab
  have hzw : gumbelInv θ d ≤ gumbelInv θ c := (gumbelGenerator θ hθ).inv_antitone c d hc0 hcd
  have hi := convex_increment_pos (gumbelSecond_logconvex (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hθ))
    (gumbelInv_pos (θ := θ) hb) (gumbelInv_pos (θ := θ) hd).le hxy hzw
  have hlog : Real.log (gumbelSecond θ⁻¹ (gumbelInv θ a+gumbelInv θ d))+
      Real.log (gumbelSecond θ⁻¹ (gumbelInv θ b+gumbelInv θ c)) ≤
      Real.log (gumbelSecond θ⁻¹ (gumbelInv θ a+gumbelInv θ c))+
      Real.log (gumbelSecond θ⁻¹ (gumbelInv θ b+gumbelInv θ d)) := by linarith
  have hpos (u v : ℝ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :=
    gumbelSecond_pos (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hθ) (add_pos (gumbelInv_pos (θ := θ) hu) (gumbelInv_pos (θ := θ) hv))
  have he := Real.exp_le_exp.mpr hlog
  simp only [Real.exp_add, Real.exp_log (hpos a d ha hd), Real.exp_log (hpos b c hb hc),
    Real.exp_log (hpos a c ha hc), Real.exp_log (hpos b d hb hd)] at he
  have hw : 0 ≤ gumbelWeight θ a*gumbelWeight θ b*gumbelWeight θ c*gumbelWeight θ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (gumbelWeight_pos hp ha).le (gumbelWeight_pos hp hb).le)
      (gumbelWeight_pos hp hc).le) (gumbelWeight_pos hp hd).le
  have hh := mul_le_mul_of_nonneg_right he hw
  simp only [gumbelDensity, gumbelDensityReal, Matrix.cons_val_zero, Matrix.cons_val_one,
    ha, hb, hc, hd, and_self, ite_true]
  nlinarith only [hh]

theorem gumbel_hasMTP2Density {θ : ℝ} (hθ : 1 ≤ θ) : (gumbel θ hθ).HasMTP2Density :=
  ⟨gumbelDensity θ, gumbelDensity_measurable θ, fun x => gumbelDensityReal_nonneg hθ (x 0) (x 1),
    gumbelDensity_mtp2 hθ, gumbel_toMeasure_density hθ⟩

end Verification
