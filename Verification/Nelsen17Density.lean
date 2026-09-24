import Verification.Nelsen17DensityShape
import Verification.InteriorDensity
import Verification.Nelsen17Necessity
import Verification.MTP2ConditionalIncreasing
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n17DensityInv (a u : ℝ) : ℝ := -Real.log (n17Ratio a u)
noncomputable def n17Weight (a u : ℝ) : ℝ := a*(1+u)^(a-1)/((1+u)^a-1)
noncomputable def n17DensityReal (a u v : ℝ) : ℝ :=
  if u ∈ Ioo 0 1 ∧ v ∈ Ioo 0 1 then
    n17Second a (n17DensityInv a u+n17DensityInv a v)*n17Weight a u*n17Weight a v else 0
noncomputable def n17Density (a : ℝ) (x : Fin 2 → I) : ℝ := n17DensityReal a (x 0) (x 1)
noncomputable def n17Partial (a u v : ℝ) : ℝ :=
  -n17PsiDeriv a (n17DensityInv a u+n17DensityInv a v)*n17Weight a u
noncomputable def n17GeneratorCDF (a u v : ℝ) : ℝ := n17Psi a (n17DensityInv a u+n17DensityInv a v)

theorem n17DensityInv_pos {a u : ℝ} (ha : a ≠ 0) (hu : u ∈ Ioo 0 1) : 0 < n17DensityInv a u :=
  neg_pos.mpr (Real.log_neg (n17Ratio_pos ha hu.1) (n17Ratio_lt_one ha hu))

theorem n17Weight_nonneg {a u : ℝ} (ha : a ≠ 0) (hu : 0 < u) : 0 ≤ n17Weight a u := by
  have hr := n17Ratio_pos ha hu
  have hc := n17_coeff_pos ha
  have hn := n17A_ne ha
  have he : n17Weight a u = (a⁻¹*n17A a)⁻¹*(1+u)^(a-1)/n17Ratio a u := by
    dsimp [n17Weight, n17Ratio]
    field_simp
  rw [he]
  exact div_nonneg (mul_nonneg (inv_pos.mpr hc).le (Real.rpow_nonneg (by linarith) _)) hr.le

theorem n17DensityInv_deriv {a u : ℝ} (ha : a ≠ 0) (hu : u ∈ Ioo 0 1) :
    HasDerivAt (n17DensityInv a) (-n17Weight a u) u := by
  change HasDerivAt (fun x => -Real.log (n17Ratio a x)) (-n17Weight a u) u
  simpa only [n17Weight, neg_div, neg_mul] using n17Inv_deriv ha hu.1

theorem n17Weight_continuousAt {a u : ℝ} (ha : a ≠ 0) (hu : u ∈ Ioo 0 1) :
    ContinuousAt (n17Weight a) u := by
  have hb : 1+u ≠ 0 := by linarith [hu.1]
  have h₁ := (((hasDerivAt_id u).const_add 1).rpow_const (p := a-1) (Or.inl hb)).continuousAt
  have h₂ := (((hasDerivAt_id u).const_add 1).rpow_const (p := a) (Or.inl hb)).continuousAt
  have hn := (div_ne_zero_iff.mp (n17Ratio_pos ha hu.1).ne').1
  exact (h₁.const_mul a).div (h₂.sub_const 1) hn

theorem n17Second_continuousAt {a t : ℝ} (ht : 0 ≤ t) : ContinuousAt (n17Second a) t := by
  have hp := (((n17Base_deriv a t).rpow_const (p := a⁻¹-2) (Or.inl (n17Base_pos ht).ne')).continuousAt)
  have he := ((hasDerivAt_id t).neg.exp).continuousAt
  exact (((he.const_mul (a⁻¹*n17A a)).mul hp).mul ((he.const_mul (a⁻¹*n17A a)).const_add 1))

theorem n17Partial_deriv {a u v : ℝ} (ha : a ≠ 0) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (n17Partial a u) (n17DensityReal a u v) v := by
  have hh := (((n17Psi_deriv2 (a := a) (t := n17DensityInv a u+n17DensityInv a v) (add_nonneg (n17DensityInv_pos ha hu).le (n17DensityInv_pos ha hv).le)).comp v
    ((n17DensityInv_deriv ha hv).const_add (n17DensityInv a u))).neg).mul_const (n17Weight a u)
  convert hh using 1
  · rfl
  · simp only [n17DensityReal, ite_eq_left (And.intro hu hv), n17Second]
    ring

theorem n17GeneratorCDF_deriv {a u v : ℝ} (ha : a ≠ 0) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (fun x => n17GeneratorCDF a x v) (n17Partial a u v) u := by
  have hh := (n17Psi_deriv (a := a) (t := n17DensityInv a u+n17DensityInv a v) (add_nonneg (n17DensityInv_pos ha hu).le (n17DensityInv_pos ha hv).le)).comp u
    ((n17DensityInv_deriv ha hu).add_const (n17DensityInv a v))
  convert hh using 1
  · rfl
  · dsimp [n17Partial]; ring

theorem n17Density_measurable (a : ℝ) : Measurable (n17Density a) := by
  unfold n17Density n17DensityReal n17Second n17Base n17DensityInv n17Ratio n17Weight
  apply Measurable.ite
  · exact (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 0))).inter
      (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 1)))
  · fun_prop
  · exact measurable_const

theorem n17DensityReal_nonneg {a : ℝ} (ha : a ≠ 0) (u v : ℝ) : 0 ≤ n17DensityReal a u v := by
  unfold n17DensityReal
  split_ifs with h
  · exact mul_nonneg (mul_nonneg
      (n17Second_pos ha (add_nonneg (n17DensityInv_pos ha h.1).le (n17DensityInv_pos ha h.2).le)).le
      (n17Weight_nonneg ha h.1.1)) (n17Weight_nonneg ha h.2.1)
  · exact le_rfl

theorem n17DensityReal_continuousAt {a u v : ℝ} (ha : a ≠ 0)
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    ContinuousAt (Function.uncurry (n17DensityReal a)) (u,v) := by
  have hiu := (n17DensityInv_deriv ha hu).continuousAt.comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hiv := (n17DensityInv_deriv ha hv).continuousAt.comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hwu := (n17Weight_continuousAt ha hu).comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hwv := (n17Weight_continuousAt ha hv).comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hh := (((n17Second_continuousAt (a := a) (t := n17DensityInv a u+n17DensityInv a v) (add_nonneg (n17DensityInv_pos ha hu).le (n17DensityInv_pos ha hv).le)).comp
      (f := fun x : ℝ × ℝ => n17DensityInv a x.1+n17DensityInv a x.2) (x := (u,v)) (hiu.add hiv)).mul hwu).mul hwv
  apply hh.congr_of_eventuallyEq
  have he : ∀ᶠ x : ℝ × ℝ in nhds (u,v), x.1 ∈ Ioo 0 1 ∧ x.2 ∈ Ioo 0 1 :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hu,hv⟩
  filter_upwards [he] with x hx
  simp [Function.uncurry, n17DensityReal, hx]

theorem n17Partial_continuousAt {a u v : ℝ} (ha : a ≠ 0)
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) : ContinuousAt (fun x => n17Partial a x v) u := by
  exact (((n17Psi_deriv2 (a := a) (t := n17DensityInv a u+n17DensityInv a v) (add_nonneg (n17DensityInv_pos ha hu).le (n17DensityInv_pos ha hv).le)).continuousAt.comp
    (f := fun x => n17DensityInv a x+n17DensityInv a v) (x := u)
    ((n17DensityInv_deriv ha hu).continuousAt.add continuousAt_const)).neg).mul (n17Weight_continuousAt ha hu)

theorem n17_toMeasure_density {a : ℝ} (ha : a ≠ 0) :
    (nelsen17 (-a) (neg_ne_zero.mpr ha)).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (n17Density a x)) := by
  apply copula_density_of_interior_derivatives (nelsen17 (-a) (neg_ne_zero.mpr ha)) (n17DensityReal a) (n17GeneratorCDF a) (n17Partial a)
  · intro u v; exact n17DensityReal_nonneg ha u v
  · intro u v hu hv; exact n17DensityReal_continuousAt ha hu hv
  · intro u v hu hv; exact n17Partial_continuousAt ha hu hv
  · intro u v hu hv; exact n17GeneratorCDF_deriv ha hu hv
  · intro u v hu hv; exact n17Partial_deriv ha hu hv
  · intro u v hu _ hv _
    have hu0 : u ≠ 0 := ne_of_gt (show (0:I) < u from hu)
    have hv0 : v ≠ 0 := ne_of_gt (show (0:I) < v from hv)
    simp only [nelsen17, neg_neg]
    rw [BivariateGenerator.cdf_copula, BivariateGenerator.cdf]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hv0, false_or, ite_false]
    rfl

theorem n17Density_mtp2 {α : ℝ} (ha : α ≠ 0) (ha1 : α ≤ 1) : IsMTP2 (n17Density α) := by
  have hp : α ≠ 0 := ha
  rw [Copula.isMTP2_fin_two_iff]
  intro a b c d hab hcd
  by_cases ha : (a:ℝ) ∈ Ioo 0 1
  swap
  · simp [n17Density, n17DensityReal, ha]
  by_cases hb : (b:ℝ) ∈ Ioo 0 1
  swap
  · simp [n17Density, n17DensityReal, hb]
  by_cases hc : (c:ℝ) ∈ Ioo 0 1
  swap
  · simp [n17Density, n17DensityReal, hc]
  by_cases hd : (d:ℝ) ∈ Ioo 0 1
  swap
  · simp [n17Density, n17DensityReal, hd]
  have ha0 : a ≠ 0 := ne_of_gt (show (0:I) < a from ha.1)
  have hc0 : c ≠ 0 := ne_of_gt (show (0:I) < c from hc.1)
  have hxy : n17DensityInv α b ≤ n17DensityInv α a := (n17Generator α hp).inv_antitone a b ha0 hab
  have hzw : n17DensityInv α d ≤ n17DensityInv α c := (n17Generator α hp).inv_antitone c d hc0 hcd
  have hi := convex_increment_pos (n17Second_logconvex hp ha1)
    (n17DensityInv_pos (a := α) hp hb) (n17DensityInv_pos (a := α) hp hd).le hxy hzw
  have hlog : Real.log (n17Second α (n17DensityInv α a+n17DensityInv α d))+
      Real.log (n17Second α (n17DensityInv α b+n17DensityInv α c)) ≤
      Real.log (n17Second α (n17DensityInv α a+n17DensityInv α c))+
      Real.log (n17Second α (n17DensityInv α b+n17DensityInv α d)) := by linarith
  have hpos (u v : ℝ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :=
    n17Second_pos (t := n17DensityInv α u+n17DensityInv α v) hp (add_nonneg (n17DensityInv_pos hp hu).le (n17DensityInv_pos hp hv).le)
  have he := Real.exp_le_exp.mpr hlog
  simp only [Real.exp_add, Real.exp_log (hpos a d ha hd), Real.exp_log (hpos b c hb hc),
    Real.exp_log (hpos a c ha hc), Real.exp_log (hpos b d hb hd)] at he
  have hw : 0 ≤ n17Weight α a*n17Weight α b*n17Weight α c*n17Weight α d :=
    mul_nonneg (mul_nonneg (mul_nonneg (n17Weight_nonneg (u := a) hp ha.1) (n17Weight_nonneg (u := b) hp hb.1))
      (n17Weight_nonneg (u := c) hp hc.1)) (n17Weight_nonneg (u := d) hp hd.1)
  have hh := mul_le_mul_of_nonneg_right he hw
  simp only [n17Density, n17DensityReal, Matrix.cons_val_zero, Matrix.cons_val_one,
    ha, hb, hc, hd, and_self, ite_true]
  nlinarith only [hh]

theorem n17_hasMTP2Density {a : ℝ} (ha : a ≠ 0) (ha1 : a ≤ 1) :
    (nelsen17 (-a) (neg_ne_zero.mpr ha)).HasMTP2Density := by
  have hp : a ≠ 0 := ha
  exact ⟨n17Density a, n17Density_measurable a, fun x => n17DensityReal_nonneg hp (x 0) (x 1),
    n17Density_mtp2 ha ha1, n17_toMeasure_density hp⟩

theorem nelsen17_density_tp2 (θ : ℝ) (hθ : θ ≠ 0) (hθ1 : -1 ≤ θ) :
    (nelsen17 θ hθ).HasMTP2Density := by
  simpa only [neg_neg] using n17_hasMTP2Density (neg_ne_zero.mpr hθ) (by linarith : -θ ≤ 1)

theorem nelsen17_density_tp2_iff (θ : ℝ) (hθ : θ ≠ 0) :
    (nelsen17 θ hθ).HasMTP2Density ↔ -1 ≤ θ := by
  constructor
  · intro h; exact (nelsen17_isCI_iff θ hθ).mp (mtp2_isCI h)
  · exact nelsen17_density_tp2 θ hθ

end Verification
