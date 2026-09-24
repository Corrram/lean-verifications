import Verification.BB1DensityShape
import Verification.InteriorDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def bbInv (θ δ u : ℝ) : ℝ := (u^(-θ)-1)^δ
noncomputable def bbWeight (θ δ u : ℝ) : ℝ := θ*δ*u^(-θ-1)*(u^(-θ)-1)^(δ-1)
noncomputable def bbDensityReal (θ δ u v : ℝ) : ℝ :=
  if u ∈ Ioo 0 1 ∧ v ∈ Ioo 0 1 then
    bbSecond δ⁻¹ θ⁻¹ (bbInv θ δ u+bbInv θ δ v)*bbWeight θ δ u*bbWeight θ δ v else 0
noncomputable def bbDensity (θ δ : ℝ) (x : Fin 2 → I) : ℝ := bbDensityReal θ δ (x 0) (x 1)
noncomputable def bbPartial (θ δ u v : ℝ) : ℝ :=
  -bbPsiDeriv δ⁻¹ θ⁻¹ (bbInv θ δ u+bbInv θ δ v)*bbWeight θ δ u
noncomputable def bbRealCDF (θ δ u v : ℝ) : ℝ :=
  (1+(bbInv θ δ u+bbInv θ δ v)^δ⁻¹)^(-θ⁻¹)

theorem bb_inv_base {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) : 0 < u^(-θ)-1 :=
  sub_pos.mpr (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hu.1 hu.2 (neg_neg_of_pos hθ))

theorem bbInv_pos {θ δ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) : 0 < bbInv θ δ u :=
  Real.rpow_pos_of_pos (bb_inv_base hθ hu) _

theorem bbWeight_pos {θ δ u : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hu : u ∈ Ioo 0 1) :
    0 < bbWeight θ δ u :=
  mul_pos (mul_pos (mul_pos hθ hδ) (Real.rpow_pos_of_pos hu.1 _))
    (Real.rpow_pos_of_pos (bb_inv_base hθ hu) _)

theorem bbInv_deriv {θ δ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) :
    HasDerivAt (bbInv θ δ) (-bbWeight θ δ u) u := by
  have hh := (((hasDerivAt_id u).rpow_const (p := -θ) (Or.inl hu.1.ne')).sub_const 1).rpow_const
    (p := δ) (Or.inl (bb_inv_base hθ hu).ne')
  convert hh using 1
  · rfl
  · dsimp [bbWeight]; ring

theorem bbWeight_continuousAt {θ δ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) :
    ContinuousAt (bbWeight θ δ) u := by
  have hP : ContinuousAt (fun x : ℝ => x^(-θ)) u := continuousAt_id.rpow_const (Or.inl hu.1.ne')
  exact (continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hu.1.ne'))).mul
    ((hP.sub continuousAt_const).rpow_const (Or.inl (bb_inv_base hθ hu).ne'))

theorem bbSecond_continuousAt {p q t : ℝ} (ht : 0 < t) : ContinuousAt (bbSecond p q) t := by
  have hP : ContinuousAt (fun x : ℝ => x^p) t := continuousAt_id.rpow_const (Or.inl ht.ne')
  have hB : 1+t^p ≠ 0 := ne_of_gt (by positivity)
  exact (((continuousAt_const.mul hP).div (continuousAt_id.pow 2) (pow_ne_zero _ ht.ne')).mul
    ((continuousAt_const.add hP).rpow_const (Or.inl hB))).mul
    (((continuousAt_const.mul hP).add continuousAt_const).sub continuousAt_const)

theorem bbPartial_deriv {θ δ u v : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (bbPartial θ δ u) (bbDensityReal θ δ u v) v := by
  have hh := (((bbPsiDeriv_deriv (p := δ⁻¹) (q := θ⁻¹) (add_pos (bbInv_pos (θ := θ) (δ := δ) hθ hu) (bbInv_pos (θ := θ) (δ := δ) hθ hv))).comp v
    ((bbInv_deriv (θ := θ) (δ := δ) hθ hv).const_add (bbInv θ δ u))).neg).mul_const (bbWeight θ δ u)
  convert hh using 1
  · rfl
  · simp only [bbDensityReal, ite_eq_left (And.intro hu hv)]
    ring

theorem bbRealCDF_deriv {θ δ u v : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (fun x => bbRealCDF θ δ x v) (bbPartial θ δ u v) u := by
  have hh := (bbPsi_deriv (p := δ⁻¹) (q := θ⁻¹) (add_pos (bbInv_pos (θ := θ) (δ := δ) hθ hu) (bbInv_pos (θ := θ) (δ := δ) hθ hv))).comp u
    ((bbInv_deriv (θ := θ) (δ := δ) hθ hu).add_const (bbInv θ δ v))
  convert hh using 1
  · rfl
  · dsimp [bbPartial]; ring

theorem bbDensity_measurable (θ δ : ℝ) : Measurable (bbDensity θ δ) := by
  unfold bbDensity bbDensityReal bbSecond bbInv bbWeight
  apply Measurable.ite
  · exact (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 0))).inter
      (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 1)))
  · fun_prop
  · exact measurable_const

theorem bbDensityReal_nonneg {θ δ : ℝ} (hθ : 0 < θ) (hδ : 1 ≤ δ) (u v : ℝ) : 0 ≤ bbDensityReal θ δ u v := by
  have hp : 0 < δ := lt_of_lt_of_le zero_lt_one hδ
  unfold bbDensityReal
  split_ifs with h
  · exact mul_nonneg (mul_nonneg
      (bbSecond_pos (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hδ) (inv_pos.mpr hθ)
        (add_pos (bbInv_pos (θ := θ) (δ := δ) hθ h.1) (bbInv_pos (θ := θ) (δ := δ) hθ h.2))).le
      (bbWeight_pos hθ hp h.1).le) (bbWeight_pos hθ hp h.2).le
  · exact le_rfl

theorem bbDensityReal_continuousAt {θ δ u v : ℝ} (hθ : 0 < θ)
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    ContinuousAt (Function.uncurry (bbDensityReal θ δ)) (u,v) := by
  have hiu := (bbInv_deriv (θ := θ) (δ := δ) hθ hu).continuousAt.comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hiv := (bbInv_deriv (θ := θ) (δ := δ) hθ hv).continuousAt.comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hwu := (bbWeight_continuousAt (θ := θ) (δ := δ) hθ hu).comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hwv := (bbWeight_continuousAt (θ := θ) (δ := δ) hθ hv).comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hh := (((bbSecond_continuousAt (p := δ⁻¹) (q := θ⁻¹)
    (add_pos (bbInv_pos (θ := θ) (δ := δ) hθ hu) (bbInv_pos (θ := θ) (δ := δ) hθ hv))).comp
      (f := fun x : ℝ × ℝ => bbInv θ δ x.1+bbInv θ δ x.2) (x := (u,v)) (hiu.add hiv)).mul hwu).mul hwv
  apply hh.congr_of_eventuallyEq
  have he : ∀ᶠ x : ℝ × ℝ in nhds (u,v), x.1 ∈ Ioo 0 1 ∧ x.2 ∈ Ioo 0 1 :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hu,hv⟩
  filter_upwards [he] with x hx
  simp [Function.uncurry, bbDensityReal, hx]

theorem bbPartial_continuousAt {θ δ u v : ℝ} (hθ : 0 < θ)
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) : ContinuousAt (fun x => bbPartial θ δ x v) u := by
  exact (((bbPsiDeriv_deriv (p := δ⁻¹) (q := θ⁻¹) (add_pos (bbInv_pos (θ := θ) (δ := δ) hθ hu) (bbInv_pos (θ := θ) (δ := δ) hθ hv))).continuousAt.comp
    (f := fun x => bbInv θ δ x+bbInv θ δ v) (x := u)
    ((bbInv_deriv (θ := θ) (δ := δ) hθ hu).continuousAt.add continuousAt_const)).neg).mul (bbWeight_continuousAt (θ := θ) (δ := δ) hθ hu)

theorem bb_toMeasure_density {θ δ : ℝ} (hθ : 0 < θ) (hδ : 1 ≤ δ) :
    (bb1 θ hθ δ hδ).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (bbDensity θ δ x)) := by
  apply copula_density_of_interior_derivatives (bb1 θ hθ δ hδ) (bbDensityReal θ δ) (bbRealCDF θ δ) (bbPartial θ δ)
  · intro u v; exact bbDensityReal_nonneg hθ hδ u v
  · intro u v hu hv; exact bbDensityReal_continuousAt hθ hu hv
  · intro u v hu hv; exact bbPartial_continuousAt hθ hu hv
  · intro u v hu hv; exact bbRealCDF_deriv hθ hu hv
  · intro u v hu hv; exact bbPartial_deriv hθ hu hv
  · intro u v hu _ hv _
    have hu0 : u ≠ 0 := ne_of_gt (show (0:I) < u from hu)
    have hv0 : v ≠ 0 := ne_of_gt (show (0:I) < v from hv)
    rw [bb1, BivariateGenerator.cdf_copula, BivariateGenerator.cdf]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hv0, false_or, ite_false]
    rfl

theorem bbDensity_mtp2 {θ δ : ℝ} (hθ : 0 < θ) (hδ : 1 ≤ δ) : IsMTP2 (bbDensity θ δ) := by
  have hp : 0 < δ := lt_of_lt_of_le zero_lt_one hδ
  rw [Copula.isMTP2_fin_two_iff]
  intro a b c d hab hcd
  by_cases ha : (a:ℝ) ∈ Ioo 0 1
  swap
  · simp [bbDensity, bbDensityReal, ha]
  by_cases hb : (b:ℝ) ∈ Ioo 0 1
  swap
  · simp [bbDensity, bbDensityReal, hb]
  by_cases hc : (c:ℝ) ∈ Ioo 0 1
  swap
  · simp [bbDensity, bbDensityReal, hc]
  by_cases hd : (d:ℝ) ∈ Ioo 0 1
  swap
  · simp [bbDensity, bbDensityReal, hd]
  have ha0 : a ≠ 0 := ne_of_gt (show (0:I) < a from ha.1)
  have hc0 : c ≠ 0 := ne_of_gt (show (0:I) < c from hc.1)
  have hxy : bbInv θ δ b ≤ bbInv θ δ a := ((claytonGenerator θ hθ).outerPower δ hδ).inv_antitone a b ha0 hab
  have hzw : bbInv θ δ d ≤ bbInv θ δ c := ((claytonGenerator θ hθ).outerPower δ hδ).inv_antitone c d hc0 hcd
  have hi := convex_increment_pos (bbSecond_logconvex (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hδ) (inv_pos.mpr hθ))
    (bbInv_pos (θ := θ) (δ := δ) hθ hb) (bbInv_pos (θ := θ) (δ := δ) hθ hd).le hxy hzw
  have hlog : Real.log (bbSecond δ⁻¹ θ⁻¹ (bbInv θ δ a+bbInv θ δ d))+
      Real.log (bbSecond δ⁻¹ θ⁻¹ (bbInv θ δ b+bbInv θ δ c)) ≤
      Real.log (bbSecond δ⁻¹ θ⁻¹ (bbInv θ δ a+bbInv θ δ c))+
      Real.log (bbSecond δ⁻¹ θ⁻¹ (bbInv θ δ b+bbInv θ δ d)) := by linarith
  have hpos (u v : ℝ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :=
    bbSecond_pos (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hδ) (inv_pos.mpr hθ) (add_pos (bbInv_pos (θ := θ) (δ := δ) hθ hu) (bbInv_pos (θ := θ) (δ := δ) hθ hv))
  have he := Real.exp_le_exp.mpr hlog
  simp only [Real.exp_add, Real.exp_log (hpos a d ha hd), Real.exp_log (hpos b c hb hc),
    Real.exp_log (hpos a c ha hc), Real.exp_log (hpos b d hb hd)] at he
  have hw : 0 ≤ bbWeight θ δ a*bbWeight θ δ b*bbWeight θ δ c*bbWeight θ δ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (bbWeight_pos hθ hp ha).le (bbWeight_pos hθ hp hb).le)
      (bbWeight_pos hθ hp hc).le) (bbWeight_pos hθ hp hd).le
  have hh := mul_le_mul_of_nonneg_right he hw
  simp only [bbDensity, bbDensityReal, Matrix.cons_val_zero, Matrix.cons_val_one,
    ha, hb, hc, hd, and_self, ite_true]
  nlinarith only [hh]

theorem bb_hasMTP2Density {θ δ : ℝ} (hθ : 0 < θ) (hδ : 1 ≤ δ) : (bb1 θ hθ δ hδ).HasMTP2Density :=
  ⟨bbDensity θ δ, bbDensity_measurable θ δ, fun x => bbDensityReal_nonneg hθ hδ (x 0) (x 1),
    bbDensity_mtp2 hθ hδ, bb_toMeasure_density hθ hδ⟩

end Verification
