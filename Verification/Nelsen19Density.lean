import Verification.Nelsen19DensityShape
import Verification.InteriorDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Copula.Dependence.ClaytonDensityMeasure

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n19Inv (θ u : ℝ) : ℝ := Real.exp (θ/u)-Real.exp θ
noncomputable def n19Weight (θ u : ℝ) : ℝ := θ*Real.exp (θ/u)/u^2
noncomputable def n19DensityReal (θ u v : ℝ) : ℝ :=
  if u ∈ Ioo 0 1 ∧ v ∈ Ioo 0 1 then
    n19Second θ (n19Inv θ u+n19Inv θ v)*n19Weight θ u*n19Weight θ v else 0
noncomputable def n19Density (θ : ℝ) (x : Fin 2 → I) : ℝ := n19DensityReal θ (x 0) (x 1)
noncomputable def n19Partial (θ u v : ℝ) : ℝ :=
  -n19PsiDeriv θ (n19Inv θ u+n19Inv θ v)*n19Weight θ u
noncomputable def n19RealCDF (θ u v : ℝ) : ℝ := n19Psi θ (n19Inv θ u+n19Inv θ v)

theorem n19Inv_pos {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) : 0 < n19Inv θ u := by
  apply sub_pos.mpr (Real.exp_lt_exp.mpr _)
  exact (lt_div_iff₀ hu.1).mpr (mul_lt_of_lt_one_right hθ hu.2)

theorem n19Weight_nonneg {θ u : ℝ} (hθ : 0 < θ) : 0 ≤ n19Weight θ u :=
  div_nonneg (mul_nonneg hθ.le (Real.exp_pos _).le) (sq_nonneg _)

theorem n19Inv_deriv {θ u : ℝ} (hu : u ∈ Ioo 0 1) :
    HasDerivAt (n19Inv θ) (-n19Weight θ u) u := by
  have hd := (((hasDerivAt_const u θ).div (hasDerivAt_id u) hu.1.ne').exp).sub_const (Real.exp θ)
  convert hd using 1
  · rfl
  · dsimp [n19Weight]; ring

theorem n19Weight_continuousAt {θ u : ℝ} (hu : u ∈ Ioo 0 1) :
    ContinuousAt (n19Weight θ) u := by
  unfold n19Weight
  have hu0 : 0 < u := hu.1
  fun_prop (disch := positivity)

theorem n19Second_continuousAt {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t) : ContinuousAt (n19Second θ) t := by
  have hx : 0 < t+Real.exp θ := add_pos_of_nonneg_of_pos ht (Real.exp_pos θ)
  have hl := n19_log_pos hθ ht
  unfold n19Second
  fun_prop (disch := positivity)

theorem n19Partial_deriv {θ u v : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (n19Partial θ u) (n19DensityReal θ u v) v := by
  have hh := (((n19Psi_deriv2 (t := n19Inv θ u+n19Inv θ v) hθ (add_nonneg (n19Inv_pos hθ hu).le (n19Inv_pos hθ hv).le)).comp v
    ((n19Inv_deriv (θ := θ) hv).const_add (n19Inv θ u))).neg).mul_const (n19Weight θ u)
  convert hh using 1
  · rfl
  · simp only [n19DensityReal, ite_eq_left (And.intro hu hv), n19Second]
    ring

theorem n19RealCDF_deriv {θ u v : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    HasDerivAt (fun x => n19RealCDF θ x v) (n19Partial θ u v) u := by
  have hh := (n19Psi_deriv (t := n19Inv θ u+n19Inv θ v) hθ (add_nonneg (n19Inv_pos hθ hu).le (n19Inv_pos hθ hv).le)).comp u
    ((n19Inv_deriv (θ := θ) hu).add_const (n19Inv θ v))
  convert hh using 1
  · rfl
  · dsimp [n19Partial]; ring

theorem n19Density_measurable (θ : ℝ) : Measurable (n19Density θ) := by
  unfold n19Density n19DensityReal n19Second n19Inv n19Weight
  apply Measurable.ite
  · exact (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 0))).inter
      (measurableSet_Ioo.preimage (measurable_subtype_coe.comp (measurable_pi_apply 1)))
  · fun_prop
  · exact measurable_const

theorem n19DensityReal_nonneg {θ : ℝ} (hθ : 0 < θ) (u v : ℝ) : 0 ≤ n19DensityReal θ u v := by
  unfold n19DensityReal
  split_ifs with h
  · exact mul_nonneg (mul_nonneg
      (n19Second_pos hθ (add_nonneg (n19Inv_pos hθ h.1).le (n19Inv_pos hθ h.2).le)).le
      (n19Weight_nonneg hθ)) (n19Weight_nonneg hθ)
  · exact le_rfl

theorem n19DensityReal_continuousAt {θ u v : ℝ} (hθ : 0 < θ)
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :
    ContinuousAt (Function.uncurry (n19DensityReal θ)) (u,v) := by
  have hiu := (n19Inv_deriv (θ := θ) hu).continuousAt.comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hiv := (n19Inv_deriv (θ := θ) hv).continuousAt.comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hwu := (n19Weight_continuousAt (θ := θ) hu).comp
    (f := Prod.fst) (x := (u,v)) continuousAt_fst
  have hwv := (n19Weight_continuousAt (θ := θ) hv).comp
    (f := Prod.snd) (x := (u,v)) continuousAt_snd
  have hh := (((n19Second_continuousAt (t := n19Inv θ u+n19Inv θ v) hθ (add_nonneg (n19Inv_pos hθ hu).le (n19Inv_pos hθ hv).le)).comp
      (f := fun x : ℝ × ℝ => n19Inv θ x.1+n19Inv θ x.2) (x := (u,v)) (hiu.add hiv)).mul hwu).mul hwv
  apply hh.congr_of_eventuallyEq
  have he : ∀ᶠ x : ℝ × ℝ in nhds (u,v), x.1 ∈ Ioo 0 1 ∧ x.2 ∈ Ioo 0 1 :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hu,hv⟩
  filter_upwards [he] with x hx
  simp [Function.uncurry, n19DensityReal, hx]

theorem n19Partial_continuousAt {θ u v : ℝ} (hθ : 0 < θ)
    (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) : ContinuousAt (fun x => n19Partial θ x v) u := by
  exact (((n19Psi_deriv2 (t := n19Inv θ u+n19Inv θ v) hθ (add_nonneg (n19Inv_pos hθ hu).le (n19Inv_pos hθ hv).le)).continuousAt.comp
    (f := fun x => n19Inv θ x+n19Inv θ v) (x := u)
    ((n19Inv_deriv (θ := θ) hu).continuousAt.add continuousAt_const)).neg).mul (n19Weight_continuousAt (θ := θ) hu)

theorem n19_toMeasure_density {θ : ℝ} (hθ : 0 < θ) :
    (nelsen19 θ hθ.le).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (n19Density θ x)) := by
  apply copula_density_of_interior_derivatives (nelsen19 θ hθ.le) (n19DensityReal θ) (n19RealCDF θ) (n19Partial θ)
  · intro u v; exact n19DensityReal_nonneg hθ u v
  · intro u v hu hv; exact n19DensityReal_continuousAt hθ hu hv
  · intro u v hu hv; exact n19Partial_continuousAt hθ hu hv
  · intro u v hu hv; exact n19RealCDF_deriv hθ hu hv
  · intro u v hu hv; exact n19Partial_deriv hθ hu hv
  · intro u v hu _ hv _
    have hu0 : u ≠ 0 := ne_of_gt (show (0:I) < u from hu)
    have hv0 : v ≠ 0 := ne_of_gt (show (0:I) < v from hv)
    rw [nelsen19, dite_eq_right hθ.ne', BivariateGenerator.cdf_copula, BivariateGenerator.cdf]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hv0, false_or, ite_false]
    rfl

theorem n19Density_mtp2 {θ : ℝ} (hθ : 0 < θ) : IsMTP2 (n19Density θ) := by
  have hp : 0 < θ := hθ
  rw [Copula.isMTP2_fin_two_iff]
  intro a b c d hab hcd
  by_cases ha : (a:ℝ) ∈ Ioo 0 1
  swap
  · simp [n19Density, n19DensityReal, ha]
  by_cases hb : (b:ℝ) ∈ Ioo 0 1
  swap
  · simp [n19Density, n19DensityReal, hb]
  by_cases hc : (c:ℝ) ∈ Ioo 0 1
  swap
  · simp [n19Density, n19DensityReal, hc]
  by_cases hd : (d:ℝ) ∈ Ioo 0 1
  swap
  · simp [n19Density, n19DensityReal, hd]
  have ha0 : a ≠ 0 := ne_of_gt (show (0:I) < a from ha.1)
  have hc0 : c ≠ 0 := ne_of_gt (show (0:I) < c from hc.1)
  have hxy : n19Inv θ b ≤ n19Inv θ a := (nelsen19Generator θ hp).inv_antitone a b ha0 hab
  have hzw : n19Inv θ d ≤ n19Inv θ c := (nelsen19Generator θ hp).inv_antitone c d hc0 hcd
  have hi := convex_increment_pos (n19Second_logconvex hθ)
    (n19Inv_pos (θ := θ) hp hb) (n19Inv_pos (θ := θ) hp hd).le hxy hzw
  have hlog : Real.log (n19Second θ (n19Inv θ a+n19Inv θ d))+
      Real.log (n19Second θ (n19Inv θ b+n19Inv θ c)) ≤
      Real.log (n19Second θ (n19Inv θ a+n19Inv θ c))+
      Real.log (n19Second θ (n19Inv θ b+n19Inv θ d)) := by linarith
  have hpos (u v : ℝ) (hu : u ∈ Ioo 0 1) (hv : v ∈ Ioo 0 1) :=
    n19Second_pos (t := n19Inv θ u+n19Inv θ v) hp (add_nonneg (n19Inv_pos hp hu).le (n19Inv_pos hp hv).le)
  have he := Real.exp_le_exp.mpr hlog
  simp only [Real.exp_add, Real.exp_log (hpos a d ha hd), Real.exp_log (hpos b c hb hc),
    Real.exp_log (hpos a c ha hc), Real.exp_log (hpos b d hb hd)] at he
  have hw : 0 ≤ n19Weight θ a*n19Weight θ b*n19Weight θ c*n19Weight θ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (n19Weight_nonneg (u := a) hp) (n19Weight_nonneg (u := b) hp))
      (n19Weight_nonneg (u := c) hp)) (n19Weight_nonneg (u := d) hp)
  have hh := mul_le_mul_of_nonneg_right he hw
  simp only [n19Density, n19DensityReal, Matrix.cons_val_zero, Matrix.cons_val_one,
    ha, hb, hc, hd, and_self, ite_true]
  nlinarith only [hh]

theorem n19_hasMTP2Density {θ : ℝ} (hθ : 0 < θ) :
    (nelsen19 θ hθ.le).HasMTP2Density := by
  have hp : 0 < θ := hθ
  exact ⟨n19Density θ, n19Density_measurable θ, fun x => n19DensityReal_nonneg hp (x 0) (x 1),
    n19Density_mtp2 hθ, n19_toMeasure_density hp⟩

theorem nelsen19_density_tp2 (θ : ℝ) (hθ : 0 ≤ θ) : (nelsen19 θ hθ).HasMTP2Density := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen19_zero]
    exact clayton_positive_density_tp2 1 (by norm_num)
  · exact n19_hasMTP2Density (lt_of_le_of_ne hθ (Ne.symm hz))

end Verification
