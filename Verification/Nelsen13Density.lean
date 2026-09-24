import Verification.Nelsen13LogDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open ProbabilityTheory Set
open MeasureTheory
open Copula
open scoped unitInterval

namespace Verification

noncomputable def n13Inv (θ u : ℝ) : ℝ := (1-Real.log u)^θ-1
noncomputable def n13Weight (θ u : ℝ) : ℝ := θ*(1-Real.log u)^θ/(1-Real.log u)/u
noncomputable def n13Density (θ : ℝ) (x : Fin 2 → I) : ℝ :=
  n13Second θ⁻¹ (n13Inv θ (x 0)+n13Inv θ (x 1))*n13Weight θ (x 0)*n13Weight θ (x 1)
noncomputable def n13Partial (θ u v : ℝ) : ℝ :=
  -n13PsiDeriv θ⁻¹ (n13Inv θ u+n13Inv θ v)*n13Weight θ u

theorem n13Density_measurable (θ : ℝ) : Measurable (n13Density θ) := by
  unfold n13Density n13Second n13Psi n13Inv n13Weight
  fun_prop

theorem n13Inv_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (u : I) : 0 ≤ n13Inv θ u :=
  sub_nonneg.mpr (Real.one_le_rpow (n13_inv_base u) hθ)

theorem n13Weight_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (u : I) : 0 ≤ n13Weight θ u := by
  have ha : 0 ≤ 1-Real.log (u:ℝ) := le_trans zero_le_one (n13_inv_base u)
  unfold n13Weight
  exact div_nonneg (div_nonneg (mul_nonneg hθ (Real.rpow_nonneg ha _)) ha) u.property.1

theorem n13Density_nonneg {θ : ℝ} (hθ : 1 ≤ θ) (x : Fin 2 → I) : 0 ≤ n13Density θ x := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  exact mul_nonneg (mul_nonneg
    (n13Second_pos (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hθ)
      (add_nonneg (n13Inv_nonneg hp.le _) (n13Inv_nonneg hp.le _))).le
    (n13Weight_nonneg hp.le _)) (n13Weight_nonneg hp.le _)

theorem n13Density_mtp2 {θ : ℝ} (hθ : 1 ≤ θ) : IsMTP2 (n13Density θ) := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  rw [Copula.isMTP2_fin_two_iff]
  intro a b c d hab hcd
  by_cases ha : a = 0
  · subst a; simp [n13Density, n13Weight]
  by_cases hc : c = 0
  · subst c; simp [n13Density, n13Weight]
  have hxy : n13Inv θ b ≤ n13Inv θ a := (nelsen13Generator θ hp).inv_antitone a b ha hab
  have hzw : n13Inv θ d ≤ n13Inv θ c := (nelsen13Generator θ hp).inv_antitone c d hc hcd
  have hi := BivariateGenerator.convex_increment (n13_logSecond_convex (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hθ))
    (n13Inv_nonneg hp.le b) (n13Inv_nonneg hp.le d) hxy hzw
  have hlog : Real.log (n13Second θ⁻¹ (n13Inv θ a+n13Inv θ d))+
      Real.log (n13Second θ⁻¹ (n13Inv θ b+n13Inv θ c)) ≤
      Real.log (n13Second θ⁻¹ (n13Inv θ a+n13Inv θ c))+
      Real.log (n13Second θ⁻¹ (n13Inv θ b+n13Inv θ d)) := by linarith
  have hpos (u v : I) := n13Second_pos (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hθ)
    (add_nonneg (n13Inv_nonneg hp.le u) (n13Inv_nonneg hp.le v))
  have he := Real.exp_le_exp.mpr hlog
  simp only [Real.exp_add, Real.exp_log (hpos a d), Real.exp_log (hpos b c),
    Real.exp_log (hpos a c), Real.exp_log (hpos b d)] at he
  have hw : 0 ≤ n13Weight θ a*n13Weight θ b*n13Weight θ c*n13Weight θ d := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (n13Weight_nonneg hp.le a)
      (n13Weight_nonneg hp.le b)) (n13Weight_nonneg hp.le c)) (n13Weight_nonneg hp.le d)
  have hh := mul_le_mul_of_nonneg_right he hw
  dsimp [n13Density]
  nlinarith only [hh]

theorem n13Inv_deriv {θ u : ℝ} (hu : 0 < u) (ha : 0 < 1-Real.log u) :
    HasDerivAt (n13Inv θ) (-n13Weight θ u) u := by
  have hh := (((Real.hasDerivAt_log hu.ne').const_sub 1).rpow_const
    (p := θ) (Or.inl ha.ne')).sub_const 1
  convert hh using 1
  · rfl
  · dsimp [n13Weight]
    rw [Real.rpow_sub_one ha.ne']
    ring

theorem n13Partial_deriv {θ u v : ℝ} (hv : 0 < v) (ha : 0 < 1-Real.log v)
    (hs : 0 < 1+(n13Inv θ u+n13Inv θ v)) :
    HasDerivAt (n13Partial θ u)
      (n13Second θ⁻¹ (n13Inv θ u+n13Inv θ v)*n13Weight θ u*n13Weight θ v) v := by
  have hi := (n13Inv_deriv (θ := θ) hv ha).const_add (n13Inv θ u)
  have hh := (((n13Psi_deriv2 θ⁻¹ _ hs).comp v hi).neg).mul_const (n13Weight θ u)
  convert hh using 1
  · rfl
  · change n13Second θ⁻¹ (n13Inv θ u+n13Inv θ v)*n13Weight θ u*n13Weight θ v =
      -(n13Second θ⁻¹ (n13Inv θ u+n13Inv θ v)*(-n13Weight θ v))*n13Weight θ u
    ring

theorem n13CDF_deriv {θ u v : ℝ} (hu : 0 < u) (ha : 0 < 1-Real.log u)
    (hs : 0 < 1+(n13Inv θ u+n13Inv θ v)) :
    HasDerivAt (fun x => n13Psi θ⁻¹ (n13Inv θ x+n13Inv θ v)) (n13Partial θ u v) u := by
  have hi := (n13Inv_deriv (θ := θ) hu ha).add_const (n13Inv θ v)
  have hh := (n13Psi_deriv θ⁻¹ _ hs).comp u hi
  convert hh using 1
  · rfl
  · dsimp [n13Partial]
    ring

end Verification
