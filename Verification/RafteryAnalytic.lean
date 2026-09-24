import Verification.Raftery
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open ProbabilityTheory Set Copula Filter
open scoped unitInterval Topology

namespace Verification

noncomputable def rafteryL (a u v : ℝ) : ℝ := u+u^a*(v^a-v^(1-a))/(2*a-1)
noncomputable def rafteryPL (a u v : ℝ) : ℝ := 1+a*u^(a-1)*(v^a-v^(1-a))/(2*a-1)
noncomputable def rafteryPR (a u v : ℝ) : ℝ := v^a*(a*u^(a-1)+(a-1)*u^(-a))/(2*a-1)
noncomputable def rafteryF (a u v : ℝ) : ℝ := if u≤v then rafteryL a u v else rafteryL a v u
noncomputable def rafteryP (a u v : ℝ) : ℝ := if u≤v then rafteryPL a u v else rafteryPR a u v
noncomputable def rafteryDensity (a u v : ℝ) : ℝ :=
  a/(2*a-1)*(min u v)^(a-1)*(a*(max u v)^(a-1)+(a-1)*(max u v)^(-a))

private theorem hasDerivAt_ite_same {f g : ℝ → ℝ} {x d : ℝ} (p : ℝ → Prop) [DecidablePred p]
    (hf : HasDerivAt f d x) (hg : HasDerivAt g d x) (he : f x=g x) :
    HasDerivAt (fun y => if p y then f y else g y) d x := by
  have hs : HasDerivWithinAt (fun y => if p y then f y else g y) d {y | p y} x :=
    hf.hasDerivWithinAt.congr (fun y hy => by simp only [show p y from hy,ite_true])
      (by split_ifs; rfl; exact he.symm)
  have ht : HasDerivWithinAt (fun y => if p y then f y else g y) d {y | ¬p y} x :=
    hg.hasDerivWithinAt.congr (fun y hy => by simp only [show ¬p y from hy,ite_false])
      (by split_ifs; exact he; rfl)
  have hh := hs.union ht
  have hu : {y | p y} ∪ {y | ¬p y} = univ := by
    ext y
    simp only [mem_union,mem_ofPred_eq,mem_univ,iff_true]
    exact em (p y)
  rw [hu,hasDerivWithinAt_univ] at hh
  exact hh

theorem rafteryL_deriv_first {a u v : ℝ} (hu : 0<u) :
    HasDerivAt (fun x => rafteryL a x v) (rafteryPL a u v) u := by
  exact (hasDerivAt_id u).add
    (((Real.hasDerivAt_rpow_const (p:=a) (Or.inl hu.ne')).mul_const _).div_const _)

theorem rafteryL_deriv_second {a u v : ℝ} (hv : 0<v) :
    HasDerivAt (rafteryL a u) (rafteryPR a v u) v := by
  have hh := ((((Real.hasDerivAt_rpow_const (p:=a) (Or.inl hv.ne')).sub
    (Real.hasDerivAt_rpow_const (p:=1-a) (Or.inl hv.ne'))).const_mul (u^a)).div_const (2*a-1)).const_add u
  convert hh using 1
  · rfl
  · dsimp only [rafteryPR]
    rw [show 1-a-1=-a by ring]
    ring

theorem rafteryP_diagonal {a t : ℝ} (ha : 1<a) (ht : 0<t) :
    rafteryPL a t t = rafteryPR a t t := by
  have h₁ : t^(a-1)*t^(1-a)=1 := by rw [← Real.rpow_add ht]; norm_num
  have h₂ : t^a*t^(-a)=1 := by rw [← Real.rpow_add ht]; norm_num
  unfold rafteryPL rafteryPR
  field_simp [show 2*a-1≠0 by linarith]
  field_simp [show a*2-1≠0 by linarith]
  linear_combination -a*h₁-(a-1)*h₂

theorem rafteryPL_deriv_second {a u v : ℝ} (hv : 0<v) :
    HasDerivAt (rafteryPL a u)
      (a/(2*a-1)*u^(a-1)*(a*v^(a-1)+(a-1)*v^(-a))) v := by
  have hh := ((((Real.hasDerivAt_rpow_const (p:=a) (Or.inl hv.ne')).sub
    (Real.hasDerivAt_rpow_const (p:=1-a) (Or.inl hv.ne'))).const_mul (a*u^(a-1))).div_const (2*a-1)).const_add 1
  convert hh using 1
  · rfl
  · rw [show 1-a-1=-a by ring]
    ring

theorem rafteryPR_deriv_second {a u v : ℝ} (hv : 0<v) :
    HasDerivAt (rafteryPR a u)
      (a/(2*a-1)*v^(a-1)*(a*u^(a-1)+(a-1)*u^(-a))) v := by
  have hh := ((Real.hasDerivAt_rpow_const (p:=a) (Or.inl hv.ne')).mul_const
    (a*u^(a-1)+(a-1)*u^(-a))).div_const (2*a-1)
  convert hh using 1
  · rfl
  · ring

theorem rafteryF_deriv_first {a u v : ℝ} (ha : 1<a) (hu : 0<u) :
    HasDerivAt (fun x => rafteryF a x v) (rafteryP a u v) u := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · simp only [rafteryP,huv.le,ite_true]
    apply (rafteryL_deriv_first hu).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds huv] with x hx
    simp only [rafteryF,hx.le,ite_true]
  · simp only [rafteryP,le_refl,ite_true]
    have hr := rafteryL_deriv_second (a:=a) (u:=u) hu
    rw [← rafteryP_diagonal ha hu] at hr
    exact hasDerivAt_ite_same (fun x => x≤u) (rafteryL_deriv_first hu) hr rfl
  · simp only [rafteryP,not_le.mpr hvu,ite_false]
    apply (rafteryL_deriv_second hu).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hvu] with x hx
    simp only [rafteryF,not_le.mpr hx,ite_false]

theorem rafteryP_deriv_second {a u v : ℝ} (ha : 1<a) (hu : 0<u) (hv : 0<v) :
    HasDerivAt (rafteryP a u) (rafteryDensity a u v) v := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · simp only [rafteryDensity,min_eq_left huv.le,max_eq_right huv.le]
    apply (rafteryPL_deriv_second hv).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds huv] with x hx
    simp only [rafteryP,hx.le,ite_true]
  · simp only [rafteryDensity,min_self,max_self]
    exact hasDerivAt_ite_same (fun x => u≤x) (rafteryPL_deriv_second hu)
      (rafteryPR_deriv_second hu) (rafteryP_diagonal ha hu)
  · simp only [rafteryDensity,min_eq_right hvu.le,max_eq_left hvu.le]
    apply (rafteryPR_deriv_second hv).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hvu] with x hx
    simp only [rafteryP,not_le.mpr hx,ite_false]

theorem rafteryP_continuous_first {a u v : ℝ} (ha : 1<a) (hu : 0<u) :
    ContinuousAt (fun x => rafteryP a x v) u := by
  have hl : ContinuousAt (fun x => rafteryPL a x v) u := by
    unfold rafteryPL
    exact continuousAt_const.add (((continuousAt_id.rpow_const (Or.inl hu.ne')).const_mul a).mul_const _ |>.div_const _)
  have hr : ContinuousAt (fun x => rafteryPR a x v) u := by
    unfold rafteryPR
    exact (((continuousAt_id.rpow_const (Or.inl hu.ne')).const_mul a).add
      ((continuousAt_id.rpow_const (Or.inl hu.ne')).const_mul (a-1))).const_mul (v^a) |>.div_const _
  rcases lt_trichotomy u v with huv | rfl | hvu
  · apply hl.congr
    filter_upwards [gt_mem_nhds huv] with x hx
    simp only [rafteryP,hx.le,ite_true]
  · change Tendsto (fun x => if x≤u then rafteryPL a x u else rafteryPR a x u) (𝓝 u)
      (𝓝 (if u≤u then rafteryPL a u u else rafteryPR a u u))
    simp only [le_refl,ite_true]
    have hrt : Tendsto (fun x => rafteryPR a x u) (𝓝 u) (𝓝 (rafteryPL a u u)) := by
      rw [rafteryP_diagonal ha hu]
      exact hr.tendsto
    exact hl.tendsto.if' hrt (p:=fun x => x≤u)
  · apply hr.congr
    filter_upwards [lt_mem_nhds hvu] with x hx
    simp only [rafteryP,not_le.mpr hx,ite_false]

end Verification
