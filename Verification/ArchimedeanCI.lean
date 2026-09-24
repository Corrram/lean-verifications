import Copula.Dependence.ConditionalMonotonicity
import Copula.Rank.ConditionalDerivative
import Mathlib.Analysis.Convex.Deriv

open ProbabilityTheory Set Filter
open Copula
open scoped unitInterval Topology

namespace Verification

theorem convex_increment_pos {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {a b c e : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hab : a ≤ b) (hce : c ≤ e) :
    0 ≤ f (b + e) - f (a + e) - f (b + c) + f (a + c) := by
  by_cases hz : b - a + (e - c) = 0
  · have hb : b = a := by linarith
    have he : e = c := by linarith
    simp [hb, he]
  have ht : 0 < b - a + (e - c) := by positivity
  have hp : 0 ≤ (b - a) / (b - a + (e - c)) := div_nonneg (sub_nonneg.mpr hab) ht.le
  have hq : 0 ≤ (e - c) / (b - a + (e - c)) := div_nonneg (sub_nonneg.mpr hce) ht.le
  have hpq : (b - a) / (b - a + (e - c)) + (e - c) / (b - a + (e - c)) = 1 := by
    rw [← add_div, div_self hz]
  have h₁ := hf.2 (show a + c ∈ Ioi 0 by simp only [mem_Ioi]; linarith)
    (show b + e ∈ Ioi 0 by simp only [mem_Ioi]; linarith) hp hq hpq
  have h₂ := hf.2 (show a + c ∈ Ioi 0 by simp only [mem_Ioi]; linarith)
    (show b + e ∈ Ioi 0 by simp only [mem_Ioi]; linarith) hq hp (by linarith)
  have he₁ : (b - a) / (b - a + (e - c)) * (a + c) +
      (e - c) / (b - a + (e - c)) * (b + e) = a + e := by field_simp; ring
  have he₂ : (e - c) / (b - a + (e - c)) * (a + c) +
      (b - a) / (b - a + (e - c)) * (b + e) = b + c := by field_simp; ring
  simp only [smul_eq_mul, he₁] at h₁
  simp only [smul_eq_mul, he₂] at h₂
  have hs := add_le_add h₁ h₂
  have he : (b - a) / (b - a + (e - c)) * f (a + c) +
      (e - c) / (b - a + (e - c)) * f (b + e) +
      ((e - c) / (b - a + (e - c)) * f (a + c) +
      (b - a) / (b - a + (e - c)) * f (b + e)) = f (a + c) + f (b + e) := by
    calc
      _ = ((b - a) / (b - a + (e - c)) + (e - c) / (b - a + (e - c))) *
        (f (a + c) + f (b + e)) := by ring
      _ = _ := by rw [hpq, one_mul]
  rw [he] at hs
  linarith


/-- A smooth strict inverse generator with log-convex negative derivative gives CI.
Only interior differentiability is used; the actual copula supplies boundary continuity. -/
theorem generator_isCI_of_logconvex_neg_deriv (g : BivariateGenerator)
    (φ φ' ψ' : ℝ → ℝ)
    (hφ : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → φ u = g.invFun u)
    (hφpos : ∀ u ∈ Ioo (0:ℝ) 1, 0 < φ u)
    (hφderiv : ∀ u ∈ Ioo (0:ℝ) 1, HasDerivAt φ (φ' u) u)
    (hψderiv : ∀ t, 0 < t → HasDerivAt g.toFun (ψ' t) t)
    (hψneg : ∀ t, 0 < t → ψ' t < 0)
    (hlog : ConvexOn ℝ (Ioi 0) (fun t => Real.log (-ψ' t))) : g.copula.IsCI := by
  have hprod (u : ℝ) (hu : u ∈ Ioo 0 1) : ψ' (φ u)*φ' u = 1 := by
    have hh := (hψderiv (φ u) (hφpos u hu)).comp u (hφderiv u hu)
    have hid : HasDerivAt (fun x => g.toFun (φ x)) 1 u := by
      apply (hasDerivAt_id u).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
      have hx0 : (⟨x,hx.1.le,hx.2.le⟩:I) ≠ 0 := fun he => hx.1.ne' (congrArg Subtype.val he)
      rw [hφ ⟨x,hx.1.le,hx.2.le⟩ hx.1 hx.2]
      exact g.right_inv _ hx0
    exact hh.unique hid
  have hconc (v : I) : ConcaveOn ℝ (Icc 0 1) (cdfSection g.copula v) := by
    by_cases hv : v = 0
    · subst v
      have he : cdfSection g.copula 0 = fun _ => 0 := by
        funext u; exact Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)
      rw [he]
      exact concaveOn_const _ (convex_Icc _ _)
    let k := g.invFun v
    have hk : 0 ≤ k := g.inv_nonneg v hv
    have hd (u : ℝ) (hu : u ∈ Ioo 0 1) : HasDerivAt (cdfSection g.copula v)
        (ψ' (φ u+k)/ψ' (φ u)) u := by
      have hh := (hψderiv (φ u+k) (by linarith [hφpos u hu])).comp u
        ((hφderiv u hu).add_const k)
      have hn := (hψneg (φ u) (hφpos u hu)).ne
      have he : ψ' (φ u+k)*φ' u = ψ' (φ u+k)/ψ' (φ u) := by
        field_simp
        calc
          _ = ψ' (φ u+k)*(ψ' (φ u)*φ' u) := by ring
          _ = _ := by rw [hprod u hu, mul_one]
      rw [he] at hh
      apply hh.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
      rw [cdfSection, projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩,
        BivariateGenerator.cdf_copula]
      have hx0 : (⟨x,hx.1.le,hx.2.le⟩:I) ≠ 0 := fun he => hx.1.ne' (congrArg Subtype.val he)
      simp only [BivariateGenerator.cdf, Matrix.cons_val_zero, Matrix.cons_val_one,
        hx0, hv, or_self, ite_false]
      dsimp only [Function.comp_def]
      rw [hφ ⟨x,hx.1.le,hx.2.le⟩ hx.1 hx.2]
    apply AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1)
    · exact (g.copula.continuous_cdf.comp (by fun_prop)).continuousOn
    · intro u hu
      exact (hd u (by simpa only [interior_Icc] using hu)).differentiableAt.differentiableWithinAt
    · intro x hx y hy hxy
      have hx' : x ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using hx
      have hy' : y ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using hy
      rw [(hd x hx').deriv, (hd y hy').deriv]
      have hxy' : φ y ≤ φ x := by
        rw [hφ ⟨x,hx'.1.le,hx'.2.le⟩ hx'.1 hx'.2, hφ ⟨y,hy'.1.le,hy'.2.le⟩ hy'.1 hy'.2]
        exact g.inv_antitone _ _ (fun he => hx'.1.ne' (congrArg Subtype.val he)) hxy
      have hi := convex_increment_pos hlog (hφpos y hy') (show (0:ℝ) ≤ 0 from le_rfl) hxy' hk
      simp only [add_zero] at hi
      have hl : Real.log (-ψ' (φ y+k))-Real.log (-ψ' (φ y)) ≤
          Real.log (-ψ' (φ x+k))-Real.log (-ψ' (φ x)) := by linarith
      have he := Real.exp_le_exp.mpr hl
      have hpx := neg_pos.mpr (hψneg (φ x) (hφpos x hx'))
      have hpy := neg_pos.mpr (hψneg (φ y) (hφpos y hy'))
      have hpxk := neg_pos.mpr (hψneg (φ x+k) (by linarith [hφpos x hx']))
      have hpyk := neg_pos.mpr (hψneg (φ y+k) (by linarith [hφpos y hy']))
      simpa only [Real.exp_sub, Real.exp_log hpx, Real.exp_log hpy,
        Real.exp_log hpxk, Real.exp_log hpyk, neg_div_neg_eq] using he
  apply g.isArchimedean.isCI_iff.mpr
  intro a b c v hab hbc
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  rcases eq_or_lt_of_le hbc with rfl | hbc
  · simp
  have hs := (hconc v).neg.secant_mono_aux1 a.property c.property
    (show (a:ℝ) < b from hab) (show (b:ℝ) < c from hbc)
  simp only [Pi.neg_apply, cdfSection, projIcc_of_mem zero_le_one a.property,
    projIcc_of_mem zero_le_one b.property, projIcc_of_mem zero_le_one c.property] at hs
  nlinarith

end Verification
