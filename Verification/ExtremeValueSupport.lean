import Verification.ExtremeValueConvexity
import Mathlib.Analysis.Convex.Deriv

/-! # Supporting lines for extreme-value logarithmic sections -/

open ProbabilityTheory Set Copula Filter
open scoped unitInterval Topology

namespace Verification

theorem extremeValueLogSection_support (C : Copula 2) (hC : C.IsExtremeValue)
    (y : ℝ) (hy : 0≤y) (x : ℝ) (hx : 0<x) :
    ∃ p ∈ Icc (0:ℝ) 1, ∀ z : ℝ, 0≤z →
      extremeValueLogSection C y hy x+p*(z-x)≤extremeValueLogSection C y hy z := by
  let f := extremeValueLogSection C y hy
  have hc : ConvexOn ℝ (Ioi 0) f := extremeValueLogSection_convex C hC y hy
  have hxi : x∈interior (Ioi (0:ℝ)) := by simpa using hx
  let p := derivWithin f (Ioi x) x
  have hinc {a b : ℝ} (ha : 0≤a) (hab : a≤b) :
      0≤f b-f a ∧ f b-f a≤b-a := by
    dsimp only [f]
    rw [extremeValueLogSection_of_nonneg C y hy b (ha.trans hab),
      extremeValueLogSection_of_nonneg C y hy a ha]
    exact extremeValueLog_increment_first C hC ha hy hab
  have hleft := hc.slope_le_leftDeriv_of_mem_interior
    (show x/2∈Ioi (0:ℝ) by change 0<x/2; positivity) hxi (show x/2<x by linarith)
  have hmiddle := hc.leftDeriv_le_rightDeriv_of_mem_interior hxi
  have hright := hc.rightDeriv_le_slope_of_mem_interior hxi
    (show x+1∈Ioi (0:ℝ) by change 0<x+1; linarith) (show x<x+1 by linarith)
  have hp0 : 0≤p := by
    have hs : 0≤slope f (x/2) x := by
      rw [slope_def_field]
      exact div_nonneg (hinc (by positivity) (by linarith)).1 (by linarith)
    exact hs.trans (hleft.trans hmiddle)
  have hp1 : p≤1 := by
    have hs : slope f x (x+1)≤1 := by
      rw [slope_def_field,div_le_one (by linarith)]
      exact (hinc hx.le (by linarith)).2
    exact hright.trans hs
  have hs (z : ℝ) (hz : 0<z) : f x+p*(z-x)≤f z := by
    rcases lt_trichotomy x z with h | h | h
    · have hh := hc.rightDeriv_le_slope_of_mem_interior hxi hz h
      rw [slope_def_field] at hh
      have he := (le_div_iff₀ (sub_pos.mpr h)).mp hh
      change p*(z-x)≤f z-f x at he
      linarith
    · subst z; simp
    · have hh := (hc.slope_le_leftDeriv_of_mem_interior hz hxi h).trans hmiddle
      rw [slope_def_field] at hh
      have he := (div_le_iff₀ (sub_pos.mpr h)).mp hh
      change f x-f z≤p*(x-z) at he
      nlinarith
  refine ⟨p,⟨hp0,hp1⟩,fun z hz => ?_⟩
  rcases hz.eq_or_lt with hz0 | hzp
  · subst z
    have hf : Continuous f := extremeValueLogSection_continuous C hC y hy
    have hlim1 : Tendsto (fun z : ℝ => f x+p*(z-x)) (𝓝[>] 0) (𝓝 (f x+p*(0-x))) :=
      (by fun_prop : Continuous (fun z : ℝ => f x+p*(z-x))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hlim2 := hf.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
    exact le_of_tendsto_of_tendsto hlim1 hlim2 (by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hs z hz)
  · exact hs z hzp

end Verification
