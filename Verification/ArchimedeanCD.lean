import Verification.ArchimedeanCI

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

/-- A smooth strict inverse generator with log-concave negative derivative gives CD.
Only interior differentiability is used; the actual copula supplies boundary continuity. -/
theorem generator_isCD_of_logconcave_neg_deriv (g : BivariateGenerator)
    (φ φ' ψ' : ℝ → ℝ)
    (hφ : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → φ u = g.invFun u)
    (hφpos : ∀ u ∈ Ioo (0:ℝ) 1, 0 < φ u)
    (hφderiv : ∀ u ∈ Ioo (0:ℝ) 1, HasDerivAt φ (φ' u) u)
    (hψderiv : ∀ t, 0 < t → HasDerivAt g.toFun (ψ' t) t)
    (hψneg : ∀ t, 0 < t → ψ' t < 0)
    (hlog : ConcaveOn ℝ (Ioi 0) (fun t => Real.log (-ψ' t))) : g.copula.IsCD := by
  have hprod (u : ℝ) (hu : u ∈ Ioo 0 1) : ψ' (φ u)*φ' u = 1 := by
    have hh := (hψderiv (φ u) (hφpos u hu)).comp u (hφderiv u hu)
    have hid : HasDerivAt (fun x => g.toFun (φ x)) 1 u := by
      apply (hasDerivAt_id u).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
      have hx0 : (⟨x,hx.1.le,hx.2.le⟩:I) ≠ 0 := fun he => hx.1.ne' (congrArg Subtype.val he)
      rw [hφ ⟨x,hx.1.le,hx.2.le⟩ hx.1 hx.2]
      exact g.right_inv _ hx0
    exact hh.unique hid
  have hconv (v : I) : ConvexOn ℝ (Icc 0 1) (cdfSection g.copula v) := by
    by_cases hv : v = 0
    · subst v
      have he : cdfSection g.copula 0 = fun _ => 0 := by
        funext u; exact Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)
      rw [he]
      exact convexOn_const _ (convex_Icc _ _)
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
    apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1)
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
      have hi := convex_increment_pos hlog.neg (hφpos y hy') (show (0:ℝ) ≤ 0 from le_rfl) hxy' hk
      simp only [add_zero, Pi.neg_apply] at hi
      have hl : Real.log (-ψ' (φ x+k))-Real.log (-ψ' (φ x)) ≤
          Real.log (-ψ' (φ y+k))-Real.log (-ψ' (φ y)) := by linarith
      have he := Real.exp_le_exp.mpr hl
      have hpx := neg_pos.mpr (hψneg (φ x) (hφpos x hx'))
      have hpy := neg_pos.mpr (hψneg (φ y) (hφpos y hy'))
      have hpxk := neg_pos.mpr (hψneg (φ x+k) (by linarith [hφpos x hx']))
      have hpyk := neg_pos.mpr (hψneg (φ y+k) (by linarith [hφpos y hy']))
      simpa only [Real.exp_sub, Real.exp_log hpx, Real.exp_log hpy,
        Real.exp_log hpxk, Real.exp_log hpyk, neg_div_neg_eq] using he
  apply g.isArchimedean.isCD_iff.mpr
  intro a b c v hab hbc
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  rcases eq_or_lt_of_le hbc with rfl | hbc
  · simp
  have hs := (hconv v).secant_mono_aux1 a.property c.property
    (show (a:ℝ) < b from hab) (show (b:ℝ) < c from hbc)
  simp only [cdfSection, projIcc_of_mem zero_le_one a.property,
    projIcc_of_mem zero_le_one b.property, projIcc_of_mem zero_le_one c.property] at hs
  nlinarith


end Verification
