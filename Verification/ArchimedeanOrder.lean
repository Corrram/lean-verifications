import Copula.Archimedean.Symmetry
import Copula.Order.SymmetricSchur
import Copula.Order.Orthant
import Mathlib.Order.Filter.Basic

/-! # Lower-orthant comparison of bivariate Archimedean copulas

For strict bivariate generators `ψ₁, ψ₂` (inverse generators, `ψ(0)=1`, positive on
`[0,∞)`), `C_{ψ₁} ≤_lo C_{ψ₂}` holds iff `φ₁ ∘ ψ₂` is subadditive on `[0,∞)`,
where `φ₁=ψ₁⁻¹`. This is Proposition 3.3(i) of Ansari–Rockel (Nelsen, Theorem 4.4.2).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.BivariateGenerator

theorem toFun_zero (g : BivariateGenerator) : g.toFun 0=1 := by
  have h := g.right_inv 1 one_ne_zero
  rwa [g.inv_one] at h

theorem toFun_le_one (g : BivariateGenerator) {x : ℝ} (hx : 0≤x) : g.toFun x≤1 := by
  rw [← g.toFun_zero]
  exact g.antitone (le_refl (0:ℝ)) hx hx

/-- A strict generator is strictly decreasing on `[0,∞)`: a flat piece would force a
positive lower bound, contradicting surjectivity onto `(0,1]`. -/
theorem strictAntiOn_of_pos (g : BivariateGenerator) (hpos : ∀ x, 0≤x → 0<g.toFun x) :
    StrictAntiOn g.toFun (Ici 0) := by
  intro a ha b hb hab
  rcases (g.antitone ha hb hab.le).lt_or_eq with h|h
  · exact h
  exfalso
  -- `g` is constant from `a` on
  have hconst : ∀ c, b≤c → g.toFun c=g.toFun b := by
    intro c hc
    rcases hc.eq_or_lt with h'|h'
    · rw [h']
    apply le_antisymm (g.antitone hb (le_trans hb hc) hc)
    have hl : 0<c-a := by linarith
    set l : ℝ := (c-b)/(c-a)
    have hl0 : 0≤l := div_nonneg (by linarith) hl.le
    have hl1 : 0<1-l := by
      have : l<1 := (div_lt_one hl).mpr (by linarith)
      linarith
    have hcomb : l*a+(1-l)*c=b := by
      simp only [l]
      field_simp
      ring
    have hc := g.convex.2 ha (show c∈Ici (0:ℝ) from le_trans hb hc) hl0 hl1.le (by ring)
    simp only [smul_eq_mul,hcomb] at hc
    rw [← h] at hc
    by_contra hcon
    push Not at hcon
    nlinarith [mul_pos hl1 (sub_pos.mpr hcon)]
  set w := g.toFun b
  have hw : 0<w := hpos b hb
  have hw1 : w≤1 := g.toFun_le_one hb
  let u : I := ⟨w/2,by positivity,by linarith⟩
  have hu : u≠0 := fun e => by
    have := congrArg Subtype.val e
    simp [u] at this
    linarith
  have hv := g.right_inv u hu
  have hn := g.inv_nonneg u hu
  rcases le_or_gt b (g.invFun u) with k|k
  · rw [hconst _ k] at hv
    change w=w/2 at hv
    linarith
  · have := g.antitone hn hb k.le
    rw [hv] at this
    change w/2≥w at this
    linarith

theorem invFun_toFun (g : BivariateGenerator) (hpos : ∀ x, 0≤x → 0<g.toFun x) {x : ℝ}
    (hx : 0≤x) : g.invFun (projIcc 0 1 zero_le_one (g.toFun x))=x := by
  have hmem : g.toFun x∈Icc (0:ℝ) 1 := ⟨(hpos x hx).le,g.toFun_le_one hx⟩
  have hne : projIcc 0 1 zero_le_one (g.toFun x)≠0 := by
    intro e
    have := congrArg Subtype.val e
    rw [projIcc_of_mem _ hmem] at this
    exact (hpos x hx).ne' this
  have hr := g.right_inv _ hne
  have e : ((projIcc 0 1 zero_le_one (g.toFun x) : I) : ℝ)=g.toFun x :=
    congrArg Subtype.val (projIcc_of_mem _ hmem)
  rw [e] at hr
  exact (g.strictAntiOn_of_pos hpos).injOn (g.inv_nonneg _ hne) hx hr

/-- The composition `φ₁ ∘ ψ₂` of Proposition 3.3. -/
noncomputable def compose (g₁ g₂ : BivariateGenerator) (x : ℝ) : ℝ :=
  g₁.invFun (projIcc 0 1 zero_le_one (g₂.toFun x))

theorem lowerOrthantLE_iff_cdf (g₁ g₂ : BivariateGenerator) :
    g₁.copula.LowerOrthantLE g₂.copula ↔ ∀ u v : I, g₁.cdf u v≤g₂.cdf u v := by
  constructor
  · intro h u v
    simpa using h ![u,v]
  · intro h u
    simpa using h (u 0) (u 1)

/-- Proposition 3.3(i), strict generators: lower-orthant order iff subadditivity of
`φ₁ ∘ ψ₂` on `[0,∞)`. -/
theorem lowerOrthantLE_iff_subadditive (g₁ g₂ : BivariateGenerator)
    (h₁ : ∀ x, 0≤x → 0<g₁.toFun x) (h₂ : ∀ x, 0≤x → 0<g₂.toFun x) :
    g₁.copula.LowerOrthantLE g₂.copula ↔
      ∀ x y, 0≤x → 0≤y → compose g₁ g₂ (x+y)≤compose g₁ g₂ x+compose g₁ g₂ y := by
  rw [lowerOrthantLE_iff_cdf]
  have hmem (x : ℝ) (hx : 0≤x) : g₂.toFun x∈Icc (0:ℝ) 1 := ⟨(h₂ x hx).le,g₂.toFun_le_one hx⟩
  have hne (x : ℝ) (hx : 0≤x) : projIcc 0 1 zero_le_one (g₂.toFun x)≠0 := by
    intro e
    have := congrArg Subtype.val e
    rw [projIcc_of_mem _ (hmem x hx)] at this
    exact (h₂ x hx).ne' this
  constructor
  · intro h x y hx hy
    set u := projIcc 0 1 zero_le_one (g₂.toFun x)
    set v := projIcc 0 1 zero_le_one (g₂.toFun y)
    have hu0 : u≠0 := hne x hx
    have hv0 : v≠0 := hne y hy
    have hc := h u v
    simp only [cdf,hu0,hv0,or_self,ite_false] at hc
    rw [invFun_toFun g₂ h₂ hx,invFun_toFun g₂ h₂ hy] at hc
    -- `ψ₁(a) ≤ ψ₁(φ₁ w)` with `w=ψ₂(x+y)`
    set w := projIcc 0 1 zero_le_one (g₂.toFun (x+y))
    have hw := g₁.right_inv w (hne (x+y) (add_nonneg hx hy))
    have ew : (w : ℝ)=g₂.toFun (x+y) :=
      congrArg Subtype.val (projIcc_of_mem _ (hmem (x+y) (add_nonneg hx hy)))
    rw [ew] at hw
    rw [← hw] at hc
    have ha : 0≤g₁.invFun u+g₁.invFun v :=
      add_nonneg (g₁.inv_nonneg u (hne x hx)) (g₁.inv_nonneg v (hne y hy))
    have hb : 0≤g₁.invFun w := g₁.inv_nonneg w (hne (x+y) (add_nonneg hx hy))
    by_contra hlt
    push Not at hlt
    have := (g₁.strictAntiOn_of_pos h₁) ha hb hlt
    exact absurd hc (not_le.mpr this)
  · intro h u v
    by_cases hz : u=0 ∨ v=0
    · rcases hz with hz|hz <;> simp [hz]
    push Not at hz
    simp only [cdf,hz.1,hz.2,or_self,ite_false]
    set x := g₂.invFun u
    set y := g₂.invFun v
    have hx : 0≤x := g₂.inv_nonneg u hz.1
    have hy : 0≤y := g₂.inv_nonneg v hz.2
    have hu : projIcc 0 1 zero_le_one (g₂.toFun x)=u := by
      rw [g₂.right_inv u hz.1]
      exact projIcc_val zero_le_one u
    have hv : projIcc 0 1 zero_le_one (g₂.toFun y)=v := by
      rw [g₂.right_inv v hz.2]
      exact projIcc_val zero_le_one v
    have hs := h x y hx hy
    simp only [compose,hu,hv] at hs
    set w := projIcc 0 1 zero_le_one (g₂.toFun (x+y))
    have hw := g₁.right_inv w (hne (x+y) (add_nonneg hx hy))
    have ew : (w : ℝ)=g₂.toFun (x+y) :=
      congrArg Subtype.val (projIcc_of_mem _ (hmem (x+y) (add_nonneg hx hy)))
    rw [ew] at hw
    rw [← hw]
    exact g₁.antitone (g₁.inv_nonneg w (hne (x+y) (add_nonneg hx hy)))
      (add_nonneg (g₁.inv_nonneg u hz.1) (g₁.inv_nonneg v hz.2)) hs

/-- Proposition 3.3(i), general form: lower-orthant order in generator coordinates. -/
theorem lowerOrthantLE_iff_generator (g₁ g₂ : BivariateGenerator) :
    g₁.copula.LowerOrthantLE g₂.copula ↔
      ∀ u v : I, u≠0 → v≠0 → g₁.toFun (g₁.invFun u+g₁.invFun v)≤g₂.toFun (g₂.invFun u+g₂.invFun v) := by
  rw [lowerOrthantLE_iff_cdf]
  constructor
  · intro h u v hu hv
    simpa [cdf,hu,hv] using h u v
  · intro h u v
    by_cases hz : u=0 ∨ v=0
    · rcases hz with hz|hz <;> simp [hz]
    push Not at hz
    simpa [cdf,hz.1,hz.2] using h u v hz.1 hz.2

end ProbabilityTheory.Copula.BivariateGenerator
