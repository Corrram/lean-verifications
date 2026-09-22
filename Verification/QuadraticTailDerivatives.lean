import Verification.QuadraticBandTailCoefficients
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Differentiation of the exact tail corrections, including the joining point -/

open MeasureTheory Set Filter
open scoped unitInterval Topology

namespace Verification

theorem hasDerivAt_positivePart_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => (max 0 y)^2) (2*max 0 x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := hasDerivAt_const x (0 : ℝ)
    rw [max_eq_left hx.le,mul_zero]
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    simp [max_eq_left hy.le]
  · have hl : HasDerivWithinAt (fun y : ℝ => (max 0 y)^2) 0 (Iic 0) 0 := by
      apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr_of_mem
      · intro y hy
        simp [max_eq_left (show y ≤ 0 from hy)]
      · exact self_mem_Iic
    have hr : HasDerivWithinAt (fun y : ℝ => (max 0 y)^2) 0 (Ici 0) 0 := by
      have h : HasDerivAt (fun y : ℝ => y^2) 0 0 := by
        convert! (hasDerivAt_id (0 : ℝ)).pow 2 using 1; norm_num
      apply h.hasDerivWithinAt.congr_of_mem
      · intro y hy
        rw [max_eq_right hy]
      · exact self_mem_Ici
    simpa only [Iic_union_Ici,hasDerivWithinAt_univ,max_self,mul_zero] using hl.union hr
  · have h := (hasDerivAt_id x).pow 2
    simp only [Nat.cast_ofNat,Nat.add_one_sub_one,pow_one,mul_one,id_eq] at h
    rw [max_eq_right hx.le]
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp only [max_eq_right hy.le,Pi.pow_apply,id_eq]

theorem hasDerivAt_nuTail (b t : ℝ) :
    HasDerivAt (fun a => nuTail a t) (6*t^2*max 0 (b*t-1)) b := by
  have h := ((hasDerivAt_positivePart_sq (b*t-1)).comp b
    (((hasDerivAt_id b).mul_const t).sub_const 1)).const_mul (3*t)
  convert! h using 1; ring

theorem hasDerivAt_xiTail (b t : ℝ) :
    HasDerivAt (fun a => xiTail a t) (b*(6*t^2*max 0 (b*t-1))) b := by
  have h := ((hasDerivAt_positivePart_sq (b*t-1)).comp b
    (((hasDerivAt_id b).mul_const t).sub_const 1)).mul
      ((((hasDerivAt_id b).const_mul 2).mul_const t).add_const 1)
  convert! h using 1
  dsimp only [Function.comp_def,id_eq]
  by_cases hp : 0 ≤ b*t-1
  · rw [max_eq_right hp]; ring
  · rw [max_eq_left (le_of_not_ge hp)]; ring

/-- A continuously varying derivative on a compact integration domain can be integrated. -/
theorem hasDerivAt_integral_compact {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f g : ℝ → α → ℝ) (hf : Continuous (Function.uncurry f))
    (hg : Continuous (Function.uncurry g)) (hd : ∀ x a, HasDerivAt (fun y => f y a) (g x a) x)
    (x : ℝ) : HasDerivAt (fun y => ∫ a, f y a ∂μ) (∫ a, g x a ∂μ) x := by
  have hk : IsCompact ((Icc (x-1) (x+1)) ×ˢ (univ : Set α)) := isCompact_Icc.prod isCompact_univ
  obtain ⟨B,hB⟩ := hk.bddAbove_image hg.norm.continuousOn
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds (by linarith : x-1<x) (by linarith : x<x+1))
    (Filter.Eventually.of_forall (fun y => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    ((hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (hg.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a y hy => hB (show ‖g y a‖ ∈ (fun p : ℝ × α => ‖g p.1 p.2‖) '' ((Icc (x-1) (x+1)) ×ˢ (univ : Set α)) from ⟨(y,a),⟨hy,mem_univ a⟩,rfl⟩)))
    (integrable_const B)
    (Filter.Eventually.of_forall (fun a y _ => hd y a))).2

theorem hasDerivAt_integral_nuTail (b : ℝ) :
    HasDerivAt (fun a => ∫ p : I × I, nuTail a |squareDelta p|)
      (∫ p : I × I, 6*|squareDelta p|^2*max 0 (b*|squareDelta p|-1)) b := by
  refine hasDerivAt_integral_compact volume (fun a p => nuTail a |squareDelta p|)
    (fun a p => 6*|squareDelta p|^2*max 0 (a*|squareDelta p|-1)) ?_ ?_ ?_ b
  · dsimp only [Function.uncurry,nuTail]; fun_prop
  · fun_prop
  · intro x p; exact hasDerivAt_nuTail x _

theorem hasDerivAt_integral_xiTail (b : ℝ) :
    HasDerivAt (fun a => ∫ p : I × I, xiTail a |squareDelta p|)
      (b*(∫ p : I × I, 6*|squareDelta p|^2*max 0 (b*|squareDelta p|-1))) b := by
  rw [← integral_const_mul]
  refine hasDerivAt_integral_compact volume (fun a p => xiTail a |squareDelta p|)
    (fun a p => a*(6*|squareDelta p|^2*max 0 (a*|squareDelta p|-1))) ?_ ?_ ?_ b
  · dsimp only [Function.uncurry,xiTail]; fun_prop
  · fun_prop
  · intro x p; exact hasDerivAt_xiTail x _

end Verification
