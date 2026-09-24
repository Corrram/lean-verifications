import Verification.Nelsen13Section
import Verification.Nelsen13Order
import Copula.Rank.ConditionalDerivative
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur

open ProbabilityTheory Set Filter
open Copula
open scoped unitInterval Topology

namespace Verification

theorem nelsen13_section_concave (θ : ℝ) (hθ : 1 ≤ θ) (v : I) :
    ConcaveOn ℝ (Icc 0 1) (cdfSection (nelsen13 θ (by linarith)) v) := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  by_cases hv : v = 0
  · subst v
    have he : cdfSection (nelsen13 θ hp.le) 0 = fun _ => 0 := by
      funext u
      exact Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)
    rw [he]
    exact concaveOn_const _ (convex_Icc _ _)
  let k : ℝ := (1-Real.log (v:ℝ))^θ-1
  have hk : 0 ≤ k := sub_nonneg.mpr (Real.one_le_rpow (n13_inv_base v) hp.le)
  have ha (u : ℝ) (hu : u ∈ Ioo 0 1) : 0 < n13A u := by
    have hh := Real.log_nonpos hu.1.le hu.2.le
    dsimp [n13A]; linarith
  have hb (u : ℝ) (hu : u ∈ Ioo 0 1) : 0 < n13B θ k u := by
    have hh := ha u hu
    dsimp [n13B]; positivity
  have hd (u : ℝ) (hu : u ∈ Ioo 0 1) :
      HasDerivAt (cdfSection (nelsen13 θ hp.le) v) (n13SectionDeriv θ k u) u := by
    apply (n13Section_deriv hp.ne' hu.1 (ha u hu) (hb u hu)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
    rw [cdfSection, projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩, nelsen13_cdf θ hp]
    have hx0 : (⟨x,hx.1.le,hx.2.le⟩:I) ≠ 0 := fun he => hx.1.ne' (congrArg Subtype.val he)
    simp only [hx0, hv, or_self, ite_false]
    dsimp [n13Section, n13B, n13A, k]
    congr 3
    ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
  · exact ((nelsen13 θ hp.le).continuous_cdf.comp (by fun_prop)).continuousOn
  · intro u hu
    exact (hd u (by simpa only [interior_Icc] using hu)).hasDerivWithinAt
  · intro u hu
    have hu' : u ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using hu
    exact (n13Section_deriv2 hp.ne' hu'.1 (ha u hu') (hb u hu')).hasDerivWithinAt
  · intro u hu
    have hu' : u ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using hu
    exact n13Section_deriv2_nonpos hθ hk hu'.1 (ha u hu')

theorem nelsen13_isCI (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen13 θ (by linarith)).IsCI := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  have ha : (nelsen13 θ hp.le).IsArchimedean := by
    simp only [nelsen13, hp.ne', dite_false]
    exact BivariateGenerator.isArchimedean _
  apply ha.isCI_iff.mpr
  intro a b c v hab hbc
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  rcases eq_or_lt_of_le hbc with rfl | hbc
  · simp
  have hs := (nelsen13_section_concave θ hθ v).neg.secant_mono_aux1 a.property c.property
    (show (a:ℝ) < b from hab) (show (b:ℝ) < c from hbc)
  simp only [Pi.neg_apply, cdfSection, projIcc_of_mem zero_le_one a.property,
    projIcc_of_mem zero_le_one b.property, projIcc_of_mem zero_le_one c.property] at hs
  nlinarith

theorem nelsen13_schur_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (hθη : θ ≤ η) :
    (nelsen13 θ (by linarith)).SchurBothLE (nelsen13 η (by linarith)) := by
  have ho := nelsen13_lowerOrthant_monotone (by linarith : 0 ≤ θ) (by linarith : 0 ≤ η) hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen13_isCI θ hθ).1
      (nelsen13_isCI η hη).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen13_isCI θ hθ).2
      (nelsen13_isCI η hη).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, cdf_transpose, cdf_transpose]
    exact ho ![x 1,x 0]

theorem n13_power_comparison_strict (r : ℝ) (hr : 1 < r) {a b : ℝ}
    (ha : 1 < a) (hb : 1 < b) : a^r+b^r-1 < (a+b-1)^r := by
  have hc := strictConvexOn_rpow hr
  have h1 : (1:ℝ) ∈ Ici 0 := by norm_num
  have hab : a+b-1 ∈ Ici 0 := by change 0 ≤ a+b-1; linarith
  have hA := hc.secant_strict_mono_aux1 h1 hab ha (by linarith : a < a+b-1)
  have hB := hc.secant_strict_mono_aux1 h1 hab hb (by linarith : b < a+b-1)
  simp only [Real.one_rpow] at hA hB
  nlinarith

theorem nelsen13_not_pqd_below_one (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ¬ (nelsen13 θ hθ).IsPQD := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen13_zero, gumbelBarnett_isPQD_iff]
    norm_num
  have hp : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hz)
  let q : I := ⟨Real.exp (-1), (Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by norm_num)⟩
  have hq : q ≠ 0 := fun h => (Real.exp_pos (-1)).ne' (congrArg Subtype.val h)
  have ha : 1 < (2:ℝ)^θ := Real.one_lt_rpow (by norm_num) hp
  have hr : 1 < θ⁻¹ := (one_lt_inv₀ hp).mpr hθ1
  have hh := n13_power_comparison_strict θ⁻¹ hr ha ha
  rw [Real.rpow_rpow_inv (by norm_num : (0:ℝ) ≤ 2) hp.ne'] at hh
  intro h
  have hc := h q q
  rw [nelsen13_cdf θ hp] at hc
  simp only [hq, or_self, ite_false] at hc
  change Real.exp (-1)*Real.exp (-1) ≤
    Real.exp (1-((1-Real.log (Real.exp (-1)))^θ+(1-Real.log (Real.exp (-1)))^θ-1)^θ⁻¹) at hc
  rw [← Real.exp_add, Real.log_exp] at hc
  norm_num only [sub_neg_eq_add, show (1:ℝ)+1=2 by norm_num] at hc
  have he := Real.exp_le_exp.mp hc
  linarith

theorem nelsen13_isCI_iff (θ : ℝ) (hθ : 0 ≤ θ) :
    (nelsen13 θ hθ).IsCI ↔ 1 ≤ θ := by
  constructor
  · intro h
    by_contra hn
    exact nelsen13_not_pqd_below_one θ hθ (lt_of_not_ge hn) h.isPQD
  · exact nelsen13_isCI θ

theorem nelsen13_density_tp2_requires_one (θ : ℝ) (hθ : 0 ≤ θ)
    (hd : (nelsen13 θ hθ).HasMTP2Density) : 1 ≤ θ := by
  by_contra hn
  exact nelsen13_not_pqd_below_one θ hθ (lt_of_not_ge hn)
    (Copula.hasMTP2Density_isPQD _ hd)

end Verification
