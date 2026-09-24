import Verification.Nelsen20DensityShape
import Verification.InteriorDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n20Inv (θ u : ℝ) : ℝ := Real.exp (u^(-θ))-Real.exp 1
noncomputable def n20Weight (θ u : ℝ) : ℝ := θ*Real.exp (u^(-θ))*u^(-θ-1)
noncomputable def n20DensityReal (θ u v : ℝ) : ℝ :=
  if u ∈ Ioo 0 1 ∧ v ∈ Ioo 0 1 then
    n20Second θ⁻¹ (n20Inv θ u+n20Inv θ v)*n20Weight θ u*n20Weight θ v else 0
noncomputable def n20Density (θ : ℝ) (x : Fin 2 → I) : ℝ := n20DensityReal θ (x 0) (x 1)
noncomputable def n20Partial (θ u v : ℝ) : ℝ :=
  -n20PsiDeriv θ⁻¹ (n20Inv θ u+n20Inv θ v)*n20Weight θ u
noncomputable def n20RealCDF (θ u v : ℝ) : ℝ := n20Psi θ⁻¹ (n20Inv θ u+n20Inv θ v)

theorem n20Inv_pos {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) : 0 < n20Inv θ u := by
  apply sub_pos.mpr (Real.exp_lt_exp.mpr _)
  exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hu.1 hu.2 (neg_neg_of_pos hθ)

theorem n20Weight_nonneg {θ u : ℝ} (hθ : 0 < θ) (hu : 0 ≤ u) : 0 ≤ n20Weight θ u :=
  mul_nonneg (mul_nonneg hθ.le (Real.exp_pos _).le) (Real.rpow_nonneg hu _)

theorem n20Inv_deriv {θ u : ℝ} (hu : u ∈ Ioo 0 1) :
    HasDerivAt (n20Inv θ) (-n20Weight θ u) u := by
  have hd := (((hasDerivAt_id u).rpow_const (p := -θ) (Or.inl hu.1.ne')).exp).sub_const (Real.exp 1)
  convert hd using 1
  · rfl
  · dsimp [n20Weight]; ring

theorem n20Weight_continuousAt {θ u : ℝ} (hu : u ∈ Ioo 0 1) :
    ContinuousAt (n20Weight θ) u := by
  have h₁ := ((hasDerivAt_id u).rpow_const (p := -θ) (Or.inl hu.1.ne')).continuousAt
  have h₂ := ((hasDerivAt_id u).rpow_const (p := -θ-1) (Or.inl hu.1.ne')).continuousAt
  exact ((Real.continuous_exp.continuousAt.comp h₁).const_mul θ).mul h₂

theorem n20Second_continuousAt {θ t : ℝ} (_hθ : 0 < θ) (ht : 0 ≤ t) : ContinuousAt (n20Second θ⁻¹) t := by
  have hx : 0 < t+Real.exp 1 := add_pos_of_nonneg_of_pos ht (Real.exp_pos 1)
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht
  have hd := (hasDerivAt_id t).add_const (Real.exp 1)
  have hlog := hd.log hx.ne'
  have hpow := (hlog.rpow_const (p := -θ⁻¹-2) (Or.inl hl.ne')).continuousAt
  exact ((hpow.const_mul θ⁻¹).mul ((hlog.continuousAt.add_const θ⁻¹).add_const 1)).div
    (hd.continuousAt.pow 2) (pow_ne_zero 2 hx.ne')

theorem n20Partial_deriv {θ u v : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (n20Partial θ u) (n20DensityReal θ u v) v := by
  have hh := (((n20Psi_deriv2 (p := θ⁻¹) (t := n20Inv θ u+n20Inv θ v) (add_nonneg (n20Inv_pos hθ hu).le (n20Inv_pos hθ hv).le)).comp v
    ((n20Inv_deriv (θ := θ) hv).const_add (n20Inv θ u))).neg).mul_const (n20Weight θ u)
  convert hh using 1
  · rfl
  · simp only [n20DensityReal, ite_eq_left (And.intro hu hv), n20Second]
    ring

theorem n20RealCDF_deriv {θ u v : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (fun x => n20RealCDF θ x v) (n20Partial θ u v) u := by
  have hh := (n20Psi_deriv (p := θ⁻¹) (t := n20Inv θ u+n20Inv θ v) (add_nonneg (n20Inv_pos hθ hu).le (n20Inv_pos hθ hv).le)).comp u
    ((n20Inv_deriv (θ := θ) hu).add_const (n20Inv θ v))
  convert hh using 1
  · rfl
  · dsimp [n20Partial]; ring

theorem n20Density_measurable (θ : ℝ) : Measurable (n20Density θ) := by
  unfold n20Density n20DensityReal n20Second n20Inv n20Weight
  apply Measurable.ite
  · exact (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 0))).inter
      (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 1)))
  · fun_prop
  · exact measurable_const

theorem n20DensityReal_nonneg {θ : ℝ} (hθ : 0 < θ) (u v : ℝ) : 0 ≤ n20DensityReal θ u v := by
  unfold n20DensityReal
  split_ifs with h
  · exact mul_nonneg (mul_nonneg
      (n20Second_pos (inv_pos.mpr hθ) (add_nonneg (n20Inv_pos hθ h.1).le (n20Inv_pos hθ h.2).le)).le
      (n20Weight_nonneg hθ h.1.1.le)) (n20Weight_nonneg hθ h.2.1.le)
  · exact le_rfl

theorem n20DensityReal_continuousAt {θ u v : ℝ} (hθ : 0 < θ)
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    ContinuousAt (Function.uncurry (n20DensityReal θ)) (u,v) := by
  have hiu := (n20Inv_deriv (θ := θ) hu).continuousAt.comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hiv := (n20Inv_deriv (θ := θ) hv).continuousAt.comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hwu := (n20Weight_continuousAt (θ := θ) hu).comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hwv := (n20Weight_continuousAt (θ := θ) hv).comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hh := (((n20Second_continuousAt (t := n20Inv θ u+n20Inv θ v) hθ (add_nonneg (n20Inv_pos hθ hu).le (n20Inv_pos hθ hv).le)).comp
      (f := fun x : ℝ × ℝ => n20Inv θ x.1+n20Inv θ x.2) (x := (u,v)) (hiu.add hiv)).mul hwu).mul hwv
  apply hh.congr_of_eventuallyEq
  have he : ∀ᶠ x : ℝ × ℝ in nhds (u,v), x.1 ∈ Ioo 0 1 ∧ x.2 ∈ Ioo 0 1 :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hu,hv⟩
  filter_upwards [he] with x hx
  simp [Function.uncurry, n20DensityReal, hx]

theorem n20Partial_continuousAt {θ u v : ℝ} (hθ : 0 < θ)
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) : ContinuousAt (fun x => n20Partial θ x v) u := by
  exact (((n20Psi_deriv2 (p := θ⁻¹) (t := n20Inv θ u+n20Inv θ v) (add_nonneg (n20Inv_pos hθ hu).le (n20Inv_pos hθ hv).le)).continuousAt.comp
    (f := fun x => n20Inv θ x+n20Inv θ v) (x := u)
    ((n20Inv_deriv (θ := θ) hu).continuousAt.add continuousAt_const)).neg).mul (n20Weight_continuousAt (θ := θ) hu)

theorem n20_toMeasure_density {θ : ℝ} (hθ : 0 < θ) :
    (nelsen20 θ hθ.le).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (n20Density θ x)) := by
  apply copula_density_of_interior_derivatives (nelsen20 θ hθ.le) (n20DensityReal θ) (n20RealCDF θ) (n20Partial θ)
  · intro u v; exact n20DensityReal_nonneg hθ u v
  · intro u v hu hv; exact n20DensityReal_continuousAt hθ hu hv
  · intro u v hu hv; exact n20Partial_continuousAt hθ hu hv
  · intro u v hu hv; exact n20RealCDF_deriv hθ hu hv
  · intro u v hu hv; exact n20Partial_deriv hθ hu hv
  · intro u v hu _ hv _
    have hu0 : u ≠ 0 := ne_of_gt (show (0:I) < u from hu)
    have hv0 : v ≠ 0 := ne_of_gt (show (0:I) < v from hv)
    rw [nelsen20, dite_eq_right hθ.ne', BivariateGenerator.cdf_copula, BivariateGenerator.cdf]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hv0, false_or, ite_false]
    rfl

theorem n20Density_mtp2 {θ : ℝ} (hθ : 0 < θ) : IsMTP2 (n20Density θ) := by
  have hp : 0 < θ := hθ
  rw [Copula.isMTP2_fin_two_iff]
  intro a b c d hab hcd
  by_cases ha : (a:ℝ) ∈ Ioo 0 1
  swap
  · simp [n20Density, n20DensityReal, ha]
  by_cases hb : (b:ℝ) ∈ Ioo 0 1
  swap
  · simp [n20Density, n20DensityReal, hb]
  by_cases hc : (c:ℝ) ∈ Ioo 0 1
  swap
  · simp [n20Density, n20DensityReal, hc]
  by_cases hd : (d:ℝ) ∈ Ioo 0 1
  swap
  · simp [n20Density, n20DensityReal, hd]
  have ha0 : a ≠ 0 := ne_of_gt (show (0:I) < a from ha.1)
  have hc0 : c ≠ 0 := ne_of_gt (show (0:I) < c from hc.1)
  have hxy : n20Inv θ b ≤ n20Inv θ a := (nelsen20Generator θ hp).inv_antitone a b ha0 hab
  have hzw : n20Inv θ d ≤ n20Inv θ c := (nelsen20Generator θ hp).inv_antitone c d hc0 hcd
  have hi := convex_increment_pos (n20Second_logconvex (inv_pos.mpr hθ))
    (n20Inv_pos (θ := θ) hp hb) (n20Inv_pos (θ := θ) hp hd).le hxy hzw
  have hlog : Real.log (n20Second θ⁻¹ (n20Inv θ a+n20Inv θ d))+
      Real.log (n20Second θ⁻¹ (n20Inv θ b+n20Inv θ c)) ≤
      Real.log (n20Second θ⁻¹ (n20Inv θ a+n20Inv θ c))+
      Real.log (n20Second θ⁻¹ (n20Inv θ b+n20Inv θ d)) := by linarith
  have hpos (u v : ℝ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :=
    n20Second_pos (t := n20Inv θ u+n20Inv θ v) (inv_pos.mpr hp) (add_nonneg (n20Inv_pos hp hu).le (n20Inv_pos hp hv).le)
  have he := Real.exp_le_exp.mpr hlog
  simp only [Real.exp_add, Real.exp_log (hpos a d ha hd), Real.exp_log (hpos b c hb hc),
    Real.exp_log (hpos a c ha hc), Real.exp_log (hpos b d hb hd)] at he
  have hw : 0 ≤ n20Weight θ a*n20Weight θ b*n20Weight θ c*n20Weight θ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (n20Weight_nonneg (u := a) hp a.property.1) (n20Weight_nonneg (u := b) hp b.property.1))
      (n20Weight_nonneg (u := c) hp c.property.1)) (n20Weight_nonneg (u := d) hp d.property.1)
  have hh := mul_le_mul_of_nonneg_right he hw
  simp only [n20Density, n20DensityReal, Matrix.cons_val_zero, Matrix.cons_val_one,
    ha, hb, hc, hd, and_self, ite_true]
  nlinarith only [hh]

theorem n20_hasMTP2Density {θ : ℝ} (hθ : 0 < θ) :
    (nelsen20 θ hθ.le).HasMTP2Density := by
  have hp : 0 < θ := hθ
  exact ⟨n20Density θ, n20Density_measurable θ, fun x => n20DensityReal_nonneg hp (x 0) (x 1),
    n20Density_mtp2 hθ, n20_toMeasure_density hp⟩

theorem nelsen20_density_tp2 (θ : ℝ) (hθ : 0 ≤ θ) : (nelsen20 θ hθ).HasMTP2Density := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen20_zero]
    exact hasMTP2Density_independence 2
  · exact n20_hasMTP2Density (lt_of_le_of_ne hθ (Ne.symm hz))

end Verification
