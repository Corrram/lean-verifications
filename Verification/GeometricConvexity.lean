import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! # Convexity from comparisons at geometrically spaced points -/

open Set

namespace Verification

theorem geometric_jensen_chord {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    (hj : ∀ x r : ℝ, 0<x → 1<r → (r+1)*f x≤r*f (x/r)+f (r*x))
    {a b c : ℝ} (ha : 0<a) (hab : a<b) (hbc : b<c) :
    f b≤f a+(b-a)/(c-a)*(f c-f a) := by
  let line : ℝ → ℝ := fun x => f a+(x-a)/(c-a)*(f c-f a)
  by_contra h
  have hgap : 0<f b-line b := sub_pos.mpr (lt_of_not_ge h)
  let ε := (f b-line b)/(2*(b-a)*(c-b))
  have hε : 0<ε := div_pos hgap (by positivity)
  let g : ℝ → ℝ := fun x => f x-line x+ε*(x-a)*(x-c)
  have hc : a<c := hab.trans hbc
  have hga : g a=0 := by simp [g,line]
  have hgc : g c=0 := by simp [g,line,sub_ne_zero.mpr hc.ne']
  have hgb : 0<g b := by
    have he : g b=(f b-line b)/2 := by
      dsimp only [g,ε]
      field_simp [sub_ne_zero.mpr hab.ne',sub_ne_zero.mpr hbc.ne']
      ring
    rw [he]
    positivity
  have hg : ContinuousOn g (Icc a c) := by
    have hf' := hf.mono (show Icc a c⊆Ioi 0 from fun x hx => ha.trans_le hx.1)
    exact (hf'.sub (by dsimp [line]; fun_prop)).add (by fun_prop)
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hc.le) hg
  have hxpos : 0<g x := hgb.trans_le (hmax ⟨hab.le,hbc.le⟩)
  have hax : a<x := lt_of_le_of_ne hx.1 (by intro he; subst x; simp [hga] at hxpos)
  have hxc : x<c := lt_of_le_of_ne hx.2 (by intro he; subst x; simp [hgc] at hxpos)
  have hx0 : 0<x := ha.trans hax
  let r := (1+min (x/a) (c/x))/2
  have hmin : 1<min (x/a) (c/x) := lt_min ((one_lt_div ha).mpr hax) ((one_lt_div hx0).mpr hxc)
  have hr : 1<r := by dsimp [r]; linarith
  have hr0 : 0<r := by linarith
  have hra : r<x/a := by dsimp [r]; linarith [min_le_left (x/a) (c/x)]
  have hrc : r<c/x := by dsimp [r]; linarith [min_le_right (x/a) (c/x)]
  have hleft : x/r∈Icc a c := by
    constructor
    · apply (le_div_iff₀ hr0).mpr
      have hh := (lt_div_iff₀ ha).mp hra
      nlinarith
    · have hh : x/r<x := (div_lt_self hx0 hr)
      exact hh.le.trans hx.2
  have hright : r*x∈Icc a c := by
    constructor
    · have hh : x<r*x := by nlinarith
      exact hx.1.trans hh.le
    · exact ((lt_div_iff₀ hx0).mp hrc).le
  have hline : r*line (x/r)+line (r*x)-(r+1)*line x=0 := by
    dsimp [line]
    field_simp [hr0.ne']
    ring
  have hquad : r*((x/r-a)*(x/r-c))+(r*x-a)*(r*x-c)-(r+1)*((x-a)*(x-c))=
      x^2*(r-1)^2*(r+1)/r := by
    field_simp [hr0.ne']
    ring
  have hqpos : 0<x^2*(r-1)^2*(r+1)/r := by positivity
  have hstrict : (r+1)*g x<r*g (x/r)+g (r*x) := by
    have hh := hj x r hx0 hr
    dsimp only [g]
    nlinarith [mul_pos hε hqpos]
  have hle1 := mul_le_mul_of_nonneg_left (hmax hleft) hr0.le
  have hle2 : g (r*x)≤g x := hmax hright
  nlinarith only [hstrict,hle1,hle2]

theorem convexOn_Ioi_of_geometric_jensen {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    (hj : ∀ x r : ℝ, 0<x → 1<r → (r+1)*f x≤r*f (x/r)+f (r*x)) :
    ConvexOn ℝ (Ioi 0) f := by
  apply LinearOrder.convexOn_of_lt (convex_Ioi 0)
  intro x hx y _ hxy a b ha hb hab
  have hxb : x<a*x+b*y := by
    nlinarith [mul_pos hb (sub_pos.mpr hxy),congrArg (fun t : ℝ => t*x) hab]
  have hby : a*x+b*y<y := by
    nlinarith [mul_pos ha (sub_pos.mpr hxy),congrArg (fun t : ℝ => t*y) hab]
  have hh := geometric_jensen_chord hf hj hx hxb hby
  have he : f x+(a*x+b*y-x)/(y-x)*(f y-f x)=a*f x+b*f y := by
    have hd : y-x≠0 := sub_ne_zero.mpr hxy.ne'
    rw [show a=1-b by linarith]
    field_simp
    ring
  simpa only [smul_eq_mul,he] using hh

end Verification
