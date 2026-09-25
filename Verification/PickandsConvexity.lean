import Verification.ExtremeValueSupport

/-! # Convexity of the canonical Pickands function on the closed interval -/

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem copulaPickands_eq_log (C : Copula 2) (hC : C.IsExtremeValue) (t : I) :
    copulaPickands C t=extremeValueLog C (1-(t:ℝ)) (t:ℝ)
      (sub_nonneg.mpr t.property.2) t.property.1 := by
  have hx : 0≤(1-(t:ℝ))/2 := by linarith [t.property.2]
  have hy : 0≤(t:ℝ)/2 := by linarith [t.property.1]
  have hh := extremeValueLog_homogeneous C hC ((1-(t:ℝ))/2) ((t:ℝ)/2) 2 hx hy (by norm_num)
  simp only [show 2*((1-(t:ℝ))/2)=1-(t:ℝ) by ring,show 2*((t:ℝ)/2)=(t:ℝ) by ring] at hh
  rw [hh]
  unfold copulaPickands pickandsRay extremeValueLog
  ring

theorem copulaPickands_perspective (C : Copula 2) (hC : C.IsExtremeValue)
    (t : I) (ht : 0<(t:ℝ)) :
    copulaPickands C t=(t:ℝ)*extremeValueLogSection C 1 (by norm_num) ((1-(t:ℝ))/(t:ℝ)) := by
  have hq : 0≤(1-(t:ℝ))/(t:ℝ) := div_nonneg (sub_nonneg.mpr t.property.2) ht.le
  have hh := extremeValueLog_homogeneous C hC ((1-(t:ℝ))/(t:ℝ)) 1 (t:ℝ) hq (by norm_num) ht.le
  have he : (t:ℝ)*((1-(t:ℝ))/(t:ℝ))=1-(t:ℝ) := by field_simp
  simp only [he,mul_one] at hh
  rw [copulaPickands_eq_log C hC t,hh,extremeValueLogSection_of_nonneg C 1 (by norm_num) _ hq]

/-- Every interior Pickands point admits a linear support valid also at both endpoints. -/
theorem copulaPickands_support (C : Copula 2) (hC : C.IsExtremeValue)
    (t : I) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) :
    ∃ p q : ℝ, copulaPickands C t=p*(1-(t:ℝ))+q*(t:ℝ) ∧
      ∀ s : I, p*(1-(s:ℝ))+q*(s:ℝ)≤copulaPickands C s := by
  let f := extremeValueLogSection C 1 (by norm_num)
  let x := (1-(t:ℝ))/(t:ℝ)
  have hx : 0<x := div_pos (sub_pos.mpr ht1) ht0
  obtain ⟨p,hp,hs⟩ := extremeValueLogSection_support C hC 1 (by norm_num) x hx
  refine ⟨p,f x-p*x,?_,fun s => ?_⟩
  · rw [copulaPickands_perspective C hC t ht0]
    change (t:ℝ)*f x=p*(1-(t:ℝ))+(f x-p*x)*(t:ℝ)
    dsimp only [x]
    field_simp
    ring
  · by_cases hs0 : s=0
    · subst s
      simpa only [Set.Icc.coe_zero,sub_zero,mul_one,mul_zero,add_zero,copulaPickands_zero] using hp.2
    have hsp : 0<(s:ℝ) := lt_of_le_of_ne s.property.1 (Ne.symm (fun h => hs0 (Subtype.ext h)))
    have hq : 0≤(1-(s:ℝ))/(s:ℝ) := div_nonneg (sub_nonneg.mpr s.property.2) hsp.le
    have hh := mul_le_mul_of_nonneg_left (hs _ hq) hsp.le
    change (s:ℝ)*(f x+p*((1-(s:ℝ))/(s:ℝ)-x))≤(s:ℝ)*f ((1-(s:ℝ))/(s:ℝ)) at hh
    rw [copulaPickands_perspective C hC s hsp]
    change p*(1-(s:ℝ))+(f x-p*x)*(s:ℝ)≤(s:ℝ)*f ((1-(s:ℝ))/(s:ℝ))
    have he : (s:ℝ)*(f x+p*((1-(s:ℝ))/(s:ℝ)-x))=p*(1-(s:ℝ))+(f x-p*x)*(s:ℝ) := by
      field_simp
      ring
    rwa [he] at hh

/-- Real-coordinate extension used only to state ordinary `ConvexOn` on `[0,1]`. -/
noncomputable def copulaPickandsReal (C : Copula 2) (t : ℝ) : ℝ :=
  extremeValueLog C (max (1-t) 0) (max t 0) (le_max_right _ _) (le_max_right _ _)

theorem copulaPickandsReal_coe (C : Copula 2) (hC : C.IsExtremeValue) (t : I) :
    copulaPickandsReal C t=copulaPickands C t := by
  simp only [copulaPickandsReal,max_eq_left (sub_nonneg.mpr t.property.2),max_eq_left t.property.1]
  exact (copulaPickands_eq_log C hC t).symm

theorem copulaPickandsReal_convex (C : Copula 2) (hC : C.IsExtremeValue) :
    ConvexOn ℝ (Icc 0 1) (copulaPickandsReal C) := by
  apply LinearOrder.convexOn_of_lt (convex_Icc 0 1)
  intro x hx y hy hxy a b ha hb hab
  have ht0 : 0<a*x+b*y := by
    have hby : 0<b*y := mul_pos hb (lt_of_le_of_lt hx.1 hxy)
    have hax : 0≤a*x := mul_nonneg ha.le hx.1
    linarith
  have ht1 : a*x+b*y<1 := by
    have hh := mul_pos ha (sub_pos.mpr (lt_of_lt_of_le hxy hy.2))
    have hh' := mul_nonneg hb.le (sub_nonneg.mpr hy.2)
    nlinarith
  let t : I := ⟨a*x+b*y,ht0.le,ht1.le⟩
  obtain ⟨p,q,he,hs⟩ := copulaPickands_support C hC t ht0 ht1
  have hA := mul_le_mul_of_nonneg_left (hs ⟨x,hx⟩) ha.le
  have hB := mul_le_mul_of_nonneg_left (hs ⟨y,hy⟩) hb.le
  have hlin : a*(p*(1-x)+q*x)+b*(p*(1-y)+q*y)=p*(1-(a*x+b*y))+q*(a*x+b*y) := by
    linear_combination p*hab
  change copulaPickandsReal C (a*x+b*y)≤a*copulaPickandsReal C x+b*copulaPickandsReal C y
  rw [show copulaPickandsReal C (a*x+b*y)=copulaPickands C t from copulaPickandsReal_coe C hC t,
    show copulaPickandsReal C x=copulaPickands C ⟨x,hx⟩ from copulaPickandsReal_coe C hC ⟨x,hx⟩,
    show copulaPickandsReal C y=copulaPickands C ⟨y,hy⟩ from copulaPickandsReal_coe C hC ⟨y,hy⟩,he]
  change p*(1-(a*x+b*y))+q*(a*x+b*y)≤_
  rw [← hlin]
  exact add_le_add hA hB

end Verification
