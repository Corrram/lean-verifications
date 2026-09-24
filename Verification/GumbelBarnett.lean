import Copula.Archimedean.Basic
import Copula.Archimedean.Symmetry
import Copula.Dependence.ConditionalMonotonicity
import Mathlib.Analysis.Convex.Deriv

open ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def gbPsi (θ t : ℝ) : ℝ := Real.exp ((1-Real.exp t)/θ)

theorem gbPsi_derivative (θ t : ℝ) :
    HasDerivAt (gbPsi θ) (-Real.exp t / θ * gbPsi θ t) t := by
  convert (((Real.hasDerivAt_exp t).const_sub 1).div_const θ).exp using 1
  · rfl
  · dsimp [gbPsi]
    ring

theorem gbPsi_second_derivative (θ t : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (fun x => -Real.exp x / θ * gbPsi θ x)
      (Real.exp t * (Real.exp t-θ) / θ^2 * gbPsi θ t) t := by
  convert (((Real.hasDerivAt_exp t).neg.div_const θ).mul (gbPsi_derivative θ t)) using 1
  dsimp
  field_simp [hθ]
  ring

theorem gbPsi_convex (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ConvexOn ℝ (Ici 0) (gbPsi θ) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
  · intro t _
    exact (gbPsi_derivative θ t).continuousAt.continuousWithinAt
  · intro t _
    exact (gbPsi_derivative θ t).hasDerivWithinAt
  · intro t _
    exact (gbPsi_second_derivative θ t hθ.ne').hasDerivWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := (show 0 < t by simpa only [interior_Ici, mem_Ioi] using ht).le
    have he := Real.add_one_le_exp t
    exact mul_nonneg (div_nonneg (mul_nonneg (Real.exp_pos t).le (by linarith))
      (sq_nonneg θ)) (Real.exp_pos _).le

private theorem gb_u_pos (u : I) (hu : u ≠ 0) : 0 < (u:ℝ) := by
  have hn : (u:ℝ) ≠ 0 := fun h => hu (Subtype.ext h)
  exact lt_of_le_of_ne u.property.1 hn.symm

private theorem gb_inv_base (θ : ℝ) (hθ : 0 ≤ θ) (u : I) :
    1 ≤ 1-θ*Real.log (u:ℝ) := by
  have hl := Real.log_nonpos u.property.1 u.property.2
  nlinarith

/-- An admissible bivariate Gumbel–Barnett generator. -/
noncomputable def gumbelBarnettGenerator (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    Copula.BivariateGenerator where
  toFun := gbPsi θ
  invFun u := Real.log (1-θ*Real.log (u:ℝ))
  nonneg t _ := (Real.exp_pos _).le
  antitone x _ y _ hxy := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (sub_le_sub_left (Real.exp_le_exp.mpr hxy) 1) hθ.le
  convex := gbPsi_convex θ hθ hθ1
  inv_nonneg u _ := Real.log_nonneg (gb_inv_base θ hθ.le u)
  inv_antitone u v hu huv := by
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (gb_inv_base θ hθ.le v))
    have hl := Real.log_le_log (gb_u_pos u hu) (show (u:ℝ) ≤ v from huv)
    nlinarith
  inv_one := by simp
  right_inv u hu := by
    dsimp [gbPsi]
    rw [Real.exp_log (lt_of_lt_of_le zero_lt_one (gb_inv_base θ hθ.le u))]
    have he : (1-(1-θ*Real.log (u:ℝ)))/θ = Real.log (u:ℝ) := by
      field_simp; ring
    rw [he, Real.exp_log (gb_u_pos u hu)]

/-- The family on its closed parameter interval, with independence at zero. -/
noncomputable def gumbelBarnett (θ : I) : Copula 2 :=
  if h : (θ:ℝ) = 0 then Copula.independence 2
  else (gumbelBarnettGenerator θ (lt_of_le_of_ne θ.property.1 (Ne.symm h)) θ.property.2).copula

theorem gumbelBarnett_zero : gumbelBarnett 0 = Copula.independence 2 := by
  simp [gumbelBarnett]

theorem gumbelBarnett_cdf (θ u v : I) :
    (gumbelBarnett θ).cdf ![u,v] =
      (u:ℝ)*v*Real.exp (-(θ:ℝ)*Real.log (u:ℝ)*Real.log (v:ℝ)) := by
  by_cases hθ : (θ:ℝ) = 0
  · simp [gumbelBarnett, hθ, Copula.cdf_independence, Fin.prod_univ_two]
  by_cases hu : u = 0
  · subst u
    simp
  by_cases hv : v = 0
  · subst v
    rw [Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)]
    simp
  simp only [gumbelBarnett, hθ, ↓reduceDIte, Copula.BivariateGenerator.cdf_copula,
    Matrix.cons_val_zero, Matrix.cons_val_one, Copula.BivariateGenerator.cdf,
    hu, hv, or_self, ↓reduceIte]
  change gbPsi θ (Real.log (1-(θ:ℝ)*Real.log (u:ℝ)) +
    Real.log (1-(θ:ℝ)*Real.log (v:ℝ))) = _
  unfold gbPsi
  rw [Real.exp_add,
    Real.exp_log (lt_of_lt_of_le zero_lt_one (gb_inv_base θ θ.property.1 u)),
    Real.exp_log (lt_of_lt_of_le zero_lt_one (gb_inv_base θ θ.property.1 v))]
  have he : (1-(1-(θ:ℝ)*Real.log (u:ℝ))*(1-(θ:ℝ)*Real.log (v:ℝ)))/(θ:ℝ) =
      Real.log (u:ℝ)+Real.log (v:ℝ)+(-(θ:ℝ)*Real.log (u:ℝ)*Real.log (v:ℝ)) := by
    field_simp
    ring
  rw [he, Real.exp_add, Real.exp_add, Real.exp_log (gb_u_pos u hu),
    Real.exp_log (gb_u_pos v hv)]

theorem gumbelBarnett_transpose (θ : I) : (gumbelBarnett θ).transpose = gumbelBarnett θ := by
  apply Copula.cdf_injective
  funext x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, Copula.cdf_transpose, gumbelBarnett_cdf, gumbelBarnett_cdf]
  congr 1 <;> ring

end Verification
