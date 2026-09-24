import Verification.Nelsen16DensityShape
import Verification.InteriorDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n16Inv (θ u : ℝ) : ℝ := (1-u)*(1+θ/u)
noncomputable def n16Weight (θ u : ℝ) : ℝ := 1+θ/u^2
noncomputable def n16DensityReal (θ u v : ℝ) : ℝ :=
  if u ∈ Ioo 0 1 ∧ v ∈ Ioo 0 1 then
    n16Second θ (n16Inv θ u+n16Inv θ v)*n16Weight θ u*n16Weight θ v else 0
noncomputable def n16Density (θ : ℝ) (x : Fin 2 → I) : ℝ := n16DensityReal θ (x 0) (x 1)
noncomputable def n16Partial (θ u v : ℝ) : ℝ :=
  -n16PsiDeriv θ (n16Inv θ u+n16Inv θ v)*n16Weight θ u
noncomputable def n16RealCDF (θ u v : ℝ) : ℝ := n16Psi θ (n16Inv θ u+n16Inv θ v)

theorem n16Inv_pos {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) : 0 < n16Inv θ u :=
  mul_pos (sub_pos.mpr hu.2) (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hθ.le hu.1.le))

theorem n16Weight_pos {θ u : ℝ} (hθ : 0 < θ) : 0 < n16Weight θ u :=
  add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hθ.le (sq_nonneg u))

theorem n16Inv_deriv {θ u : ℝ} (hu : u ∈ Ioo 0 1) :
    HasDerivAt (n16Inv θ) (-n16Weight θ u) u := by
  have hd := ((hasDerivAt_id u).const_sub 1).mul
    (((hasDerivAt_const u θ).div (hasDerivAt_id u) hu.1.ne').const_add 1)
  convert hd using 1
  · rfl
  · dsimp [n16Weight]; field_simp [hu.1.ne']; ring

theorem n16Weight_continuousAt {θ u : ℝ} (hu : u ∈ Ioo 0 1) :
    ContinuousAt (n16Weight θ) u :=
  continuousAt_const.add (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero _ hu.1.ne'))

theorem n16Second_continuousAt {θ t : ℝ} (hθ : 0 < θ) : ContinuousAt (n16Second θ) t :=
  continuousAt_const.div ((n16Rad_deriv hθ).continuousAt.pow 3) (pow_ne_zero _ (n16Rad_pos hθ).ne')

theorem n16Partial_deriv {θ u v : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (n16Partial θ u) (n16DensityReal θ u v) v := by
  have hh := (((n16Psi_deriv2 (t := n16Inv θ u+n16Inv θ v) hθ).comp v
    ((n16Inv_deriv (θ := θ) hv).const_add (n16Inv θ u))).neg).mul_const (n16Weight θ u)
  convert hh using 1
  · rfl
  · simp only [n16DensityReal, ite_eq_left (And.intro hu hv), n16Second]
    ring

theorem n16RealCDF_deriv {θ u v : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) (_hv : v ∈ Ioo 0 1) :
    HasDerivAt (fun x => n16RealCDF θ x v) (n16Partial θ u v) u := by
  have hh := (n16Psi_deriv (t := n16Inv θ u+n16Inv θ v) hθ).comp u
    ((n16Inv_deriv (θ := θ) hu).add_const (n16Inv θ v))
  convert hh using 1
  · rfl
  · dsimp [n16Partial]; ring

theorem n16Density_measurable (θ : ℝ) : Measurable (n16Density θ) := by
  unfold n16Density n16DensityReal n16Second n16Rad n16Inv n16Weight
  apply Measurable.ite
  · exact (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 0))).inter
      (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 1)))
  · fun_prop
  · exact measurable_const

theorem n16DensityReal_nonneg {θ : ℝ} (hθ : 0 < θ) (u v : ℝ) : 0 ≤ n16DensityReal θ u v := by
  unfold n16DensityReal
  split_ifs with h
  · exact mul_nonneg (mul_nonneg
      (n16Second_pos hθ).le
      (n16Weight_pos hθ).le) (n16Weight_pos hθ).le
  · exact le_rfl

theorem n16DensityReal_continuousAt {θ u v : ℝ} (hθ : 0 < θ)
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    ContinuousAt (Function.uncurry (n16DensityReal θ)) (u,v) := by
  have hiu := (n16Inv_deriv (θ := θ) hu).continuousAt.comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hiv := (n16Inv_deriv (θ := θ) hv).continuousAt.comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hwu := (n16Weight_continuousAt (θ := θ) hu).comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hwv := (n16Weight_continuousAt (θ := θ) hv).comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hh := (((n16Second_continuousAt (t := n16Inv θ u+n16Inv θ v) hθ).comp
      (f := fun x : ℝ × ℝ => n16Inv θ x.1+n16Inv θ x.2) (x := (u,v)) (hiu.add hiv)).mul hwu).mul hwv
  apply hh.congr_of_eventuallyEq
  have he : ∀ᶠ x : ℝ × ℝ in nhds (u,v), x.1 ∈ Ioo 0 1 ∧ x.2 ∈ Ioo 0 1 :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hu,hv⟩
  filter_upwards [he] with x hx
  simp [Function.uncurry, n16DensityReal, hx]

theorem n16Partial_continuousAt {θ u v : ℝ} (hθ : 0 < θ)
    (hu : u ∈ Ioo 0 1) (_hv : v ∈ Ioo 0 1) : ContinuousAt (fun x => n16Partial θ x v) u := by
  exact (((n16Psi_deriv2 (t := n16Inv θ u+n16Inv θ v) hθ).continuousAt.comp
    (f := fun x => n16Inv θ x+n16Inv θ v) (x := u)
    ((n16Inv_deriv (θ := θ) hu).continuousAt.add continuousAt_const)).neg).mul (n16Weight_continuousAt (θ := θ) hu)

theorem n16_toMeasure_density {θ : ℝ} (hθ : 0 < θ) :
    (nelsen16 θ hθ.le).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (n16Density θ x)) := by
  apply copula_density_of_interior_derivatives (nelsen16 θ hθ.le) (n16DensityReal θ) (n16RealCDF θ) (n16Partial θ)
  · intro u v; exact n16DensityReal_nonneg hθ u v
  · intro u v hu hv; exact n16DensityReal_continuousAt hθ hu hv
  · intro u v hu hv; exact n16Partial_continuousAt hθ hu hv
  · intro u v hu hv; exact n16RealCDF_deriv hθ hu hv
  · intro u v hu hv; exact n16Partial_deriv hθ hu hv
  · intro u v hu _ hv _
    have hu0 : u ≠ 0 := ne_of_gt (show (0:I) < u from hu)
    have hv0 : v ≠ 0 := ne_of_gt (show (0:I) < v from hv)
    rw [nelsen16, dite_eq_right hθ.ne', BivariateGenerator.cdf_copula, BivariateGenerator.cdf]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hv0, false_or, ite_false]
    rfl

theorem n16Density_mtp2 {θ : ℝ} (hθ : 3+2*Real.sqrt 2 ≤ θ) : IsMTP2 (n16Density θ) := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one (n16_density_threshold hθ).1
  rw [Copula.isMTP2_fin_two_iff]
  intro a b c d hab hcd
  by_cases ha : (a:ℝ) ∈ Ioo 0 1
  swap
  · simp [n16Density, n16DensityReal, ha]
  by_cases hb : (b:ℝ) ∈ Ioo 0 1
  swap
  · simp [n16Density, n16DensityReal, hb]
  by_cases hc : (c:ℝ) ∈ Ioo 0 1
  swap
  · simp [n16Density, n16DensityReal, hc]
  by_cases hd : (d:ℝ) ∈ Ioo 0 1
  swap
  · simp [n16Density, n16DensityReal, hd]
  have ha0 : a ≠ 0 := ne_of_gt (show (0:I) < a from ha.1)
  have hc0 : c ≠ 0 := ne_of_gt (show (0:I) < c from hc.1)
  have hxy : n16Inv θ b ≤ n16Inv θ a := (nelsen16Generator θ hp).inv_antitone a b ha0 hab
  have hzw : n16Inv θ d ≤ n16Inv θ c := (nelsen16Generator θ hp).inv_antitone c d hc0 hcd
  have hi := convex_increment_pos (n16Second_logconvex hθ)
    (n16Inv_pos (θ := θ) hp hb) (n16Inv_pos (θ := θ) hp hd).le hxy hzw
  have hlog : Real.log (n16Second θ (n16Inv θ a+n16Inv θ d))+
      Real.log (n16Second θ (n16Inv θ b+n16Inv θ c)) ≤
      Real.log (n16Second θ (n16Inv θ a+n16Inv θ c))+
      Real.log (n16Second θ (n16Inv θ b+n16Inv θ d)) := by linarith
  have hpos (u v : ℝ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :=
    n16Second_pos (t := n16Inv θ u+n16Inv θ v) hp
  have he := Real.exp_le_exp.mpr hlog
  simp only [Real.exp_add, Real.exp_log (hpos a d ha hd), Real.exp_log (hpos b c hb hc),
    Real.exp_log (hpos a c ha hc), Real.exp_log (hpos b d hb hd)] at he
  have hw : 0 ≤ n16Weight θ a*n16Weight θ b*n16Weight θ c*n16Weight θ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (n16Weight_pos (u := a) hp).le (n16Weight_pos (u := b) hp).le)
      (n16Weight_pos (u := c) hp).le) (n16Weight_pos (u := d) hp).le
  have hh := mul_le_mul_of_nonneg_right he hw
  simp only [n16Density, n16DensityReal, Matrix.cons_val_zero, Matrix.cons_val_one,
    ha, hb, hc, hd, and_self, ite_true]
  nlinarith only [hh]

theorem n16_hasMTP2Density {θ : ℝ} (hθ : 3+2*Real.sqrt 2 ≤ θ) :
    (nelsen16 θ (le_trans zero_le_one (n16_density_threshold hθ).1)).HasMTP2Density := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one (n16_density_threshold hθ).1
  exact ⟨n16Density θ, n16Density_measurable θ, fun x => n16DensityReal_nonneg hp (x 0) (x 1),
    n16Density_mtp2 hθ, n16_toMeasure_density hp⟩

end Verification
