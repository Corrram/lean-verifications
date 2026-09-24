import Verification.BB1Conditional
import Mathlib.Analysis.SpecialFunctions.Sqrt

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n16Rad (θ t : ℝ) : ℝ := Real.sqrt ((1-t-θ)^2+4*θ)
noncomputable def n16Psi (θ t : ℝ) : ℝ := (1-t-θ+n16Rad θ t)/2
noncomputable def n16PsiDeriv (θ t : ℝ) : ℝ := -(1+(1-t-θ)/n16Rad θ t)/2

theorem n16Rad_pos {θ t : ℝ} (hθ : 0 < θ) : 0 < n16Rad θ t := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg (1-t-θ)]

theorem n16Rad_sq {θ t : ℝ} (hθ : 0 ≤ θ) : (n16Rad θ t)^2 = (1-t-θ)^2+4*θ :=
  Real.sq_sqrt (by nlinarith [sq_nonneg (1-t-θ)])

theorem n16Rad_deriv {θ t : ℝ} (hθ : 0 < θ) :
    HasDerivAt (n16Rad θ) (-(1-t-θ)/n16Rad θ t) t := by
  have hs := ((hasDerivAt_id t).const_sub 1).sub_const θ
  have hh := ((hs.pow 2).add_const (4*θ)).sqrt
    (ne_of_gt (by nlinarith [sq_nonneg (1-t-θ)] : 0 < (1-t-θ)^2+4*θ))
  convert hh using 1
  · rfl
  · dsimp [n16Rad]; ring

theorem n16Psi_deriv {θ t : ℝ} (hθ : 0 < θ) :
    HasDerivAt (n16Psi θ) (n16PsiDeriv θ t) t := by
  have hh := ((((hasDerivAt_id t).const_sub 1).sub_const θ).add (n16Rad_deriv hθ)).div_const 2
  convert hh using 1
  · rfl
  · dsimp [n16PsiDeriv]; ring

theorem n16Psi_deriv2 {θ t : ℝ} (hθ : 0 < θ) :
    HasDerivAt (n16PsiDeriv θ) (2*θ/(n16Rad θ t)^3) t := by
  have hs := ((hasDerivAt_id t).const_sub 1).sub_const θ
  have hh := ((((hs.div (n16Rad_deriv hθ) (n16Rad_pos hθ).ne').const_add 1).neg).div_const 2)
  convert hh using 1
  · rfl
  · dsimp
    have he := n16Rad_sq (t := t) hθ.le
    field_simp [(n16Rad_pos (t := t) hθ).ne']
    nlinarith

theorem n16Psi_convex {θ : ℝ} (hθ : 0 < θ) : ConvexOn ℝ (Ici 0) (n16Psi θ) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
  · intro t _; exact (n16Psi_deriv hθ).continuousAt.continuousWithinAt
  · intro t _; exact (n16Psi_deriv hθ).hasDerivWithinAt
  · intro t _; exact (n16Psi_deriv2 hθ).hasDerivWithinAt
  · intro t _; exact div_nonneg (by linarith) (pow_nonneg (n16Rad_pos hθ).le _)

theorem n16Psi_antitone {θ : ℝ} (hθ : 0 < θ) : AntitoneOn (n16Psi θ) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
  · intro t _; exact (n16Psi_deriv hθ).continuousAt.continuousWithinAt
  · intro t _; exact (n16Psi_deriv hθ).hasDerivWithinAt
  · intro t _
    have he := n16Rad_sq (t := t) hθ.le
    have hp := n16Rad_pos (t := t) hθ
    have hb : -(n16Rad θ t) ≤ 1-t-θ := by nlinarith
    have hd : -1 ≤ (1-t-θ)/n16Rad θ t := (le_div_iff₀ hp).mpr (by linarith)
    unfold n16PsiDeriv
    linarith

private theorem n16_u_pos (u : I) (hu : u ≠ 0) : 0 < (u:ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

noncomputable def nelsen16Generator (θ : ℝ) (hθ : 0 < θ) : BivariateGenerator where
  toFun := n16Psi θ
  invFun u := (1-(u:ℝ))*(1+θ/(u:ℝ))
  nonneg t _ := by
    have he := n16Rad_sq (t := t) hθ.le
    have hp := n16Rad_pos (t := t) hθ
    unfold n16Psi
    have hh : 0 ≤ 1-t-θ+n16Rad θ t := by nlinarith
    exact div_nonneg hh (by norm_num)
  antitone := n16Psi_antitone hθ
  convex := n16Psi_convex hθ
  inv_nonneg u _ := mul_nonneg (sub_nonneg.mpr u.property.2)
    (add_nonneg zero_le_one (div_nonneg hθ.le u.property.1))
  inv_antitone u v hu huv := by
    have hp := n16_u_pos u hu
    have hq : 0 < (v:ℝ) := hp.trans_le huv
    apply mul_le_mul (sub_le_sub_left (show (u:ℝ) ≤ v from huv) 1)
      (add_le_add (le_refl 1) (div_le_div_of_nonneg_left hθ.le hp huv))
      (by positivity) (sub_nonneg.mpr u.property.2)
  inv_one := by simp
  right_inv u hu := by
    have hp := n16_u_pos u hu
    have he : 1-(1-(u:ℝ))*(1+θ/(u:ℝ))-θ = (u:ℝ)-θ/(u:ℝ) := by field_simp; ring
    have hs : ((u:ℝ)-θ/(u:ℝ))^2+4*θ = ((u:ℝ)+θ/(u:ℝ))^2 := by field_simp; ring
    unfold n16Psi n16Rad
    rw [he, hs, Real.sqrt_sq (by positivity : 0 ≤ (u:ℝ)+θ/(u:ℝ))]
    ring

noncomputable def nelsen16 (θ : ℝ) (hθ : 0 ≤ θ) : Copula 2 :=
  if hz : θ = 0 then countermonotonic else
    (nelsen16Generator θ (lt_of_le_of_ne hθ (Ne.symm hz))).copula

theorem nelsen16_zero : nelsen16 0 le_rfl = countermonotonic := by simp [nelsen16]

theorem nelsen16_cdf (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (nelsen16 θ hθ.le).cdf ![u,v] =
      if u = 0 ∨ v = 0 then 0 else
        let s := (u:ℝ)+(v:ℝ)-1-θ*((u:ℝ)⁻¹+(v:ℝ)⁻¹-1)
        (s+Real.sqrt (s^2+4*θ))/2 := by
  by_cases hu : u = 0
  · subst u; simp
  by_cases hv : v = 0
  · subst v
    rw [Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)]
    simp
  simp only [nelsen16, hθ.ne', dite_false, BivariateGenerator.cdf_copula,
    Matrix.cons_val_zero, Matrix.cons_val_one, BivariateGenerator.cdf, hu, hv, or_self, ite_false]
  change n16Psi θ ((1-(u:ℝ))*(1+θ/(u:ℝ))+(1-(v:ℝ))*(1+θ/(v:ℝ))) = _
  have he : 1-((1-(u:ℝ))*(1+θ/(u:ℝ))+(1-(v:ℝ))*(1+θ/(v:ℝ)))-θ =
      (u:ℝ)+(v:ℝ)-1-θ*((u:ℝ)⁻¹+(v:ℝ)⁻¹-1) := by
    have hp := n16_u_pos u hu
    have hq := n16_u_pos v hv
    field_simp
    ring
  unfold n16Psi n16Rad
  rw [he]

theorem nelsen16_cdf_full (θ : ℝ) (hθ : 0 ≤ θ) (u v : I) :
    (nelsen16 θ hθ).cdf ![u,v] =
      if u = 0 ∨ v = 0 then 0 else
        let s := (u:ℝ)+(v:ℝ)-1-θ*((u:ℝ)⁻¹+(v:ℝ)⁻¹-1)
        (s+Real.sqrt (s^2+4*θ))/2 := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen16_zero]
    by_cases hu : u = 0
    · subst u; simp
    by_cases hv : v = 0
    · subst v
      rw [Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)]
      simp
    simp only [hu, hv, or_self, ite_false, zero_mul, mul_zero, sub_zero, add_zero,
      cdf_countermonotonic, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sqrt_sq_eq_abs]
    by_cases hs : 0 ≤ (u:ℝ)+(v:ℝ)-1
    · rw [abs_of_nonneg hs, max_eq_right hs]; ring
    · rw [abs_of_neg (lt_of_not_ge hs), max_eq_left (le_of_not_ge hs)]; ring
  · exact nelsen16_cdf θ (lt_of_le_of_ne hθ (Ne.symm hz)) u v

theorem nelsen16_cdf_continuous_parameter (u v : I) :
    Continuous (fun θ : Ici (0:ℝ) => (nelsen16 θ (Set.mem_Ici.mp θ.property)).cdf ![u,v]) := by
  simp only [nelsen16_cdf_full]
  by_cases hz : u = 0 ∨ v = 0
  · simp only [hz, ite_true]; exact continuous_const
  · simp only [hz, ite_false]
    fun_prop

theorem nelsen16_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 ≤ θ a) (ht : Filter.Tendsto θ l (nhds 0)) (u v : I) :
    Filter.Tendsto (fun a => (nelsen16 (θ a) (hθ a)).cdf ![u,v]) l
      (nhds (countermonotonic.cdf ![u,v])) := by
  have hh : Filter.Tendsto (fun a => (⟨θ a,Set.mem_Ici.mpr (hθ a)⟩ : Ici (0:ℝ))) l (nhds ⟨0,by simp⟩) :=
    tendsto_subtype_rng.mpr ht
  simpa only [Function.comp_def, nelsen16_zero] using
    ((nelsen16_cdf_continuous_parameter u v).continuousAt.tendsto.comp hh)

end Verification
