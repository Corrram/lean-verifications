import Verification.Nelsen16
import Copula.TailDependence.Derivative
import Copula.TailDependence.Examples

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n16DiagBase (θ t : ℝ) : ℝ := 2*t^2+(θ-1)*t-2*θ
noncomputable def n16Diagonal (θ t : ℝ) : ℝ :=
  t*(2*θ/(Real.sqrt ((n16DiagBase θ t)^2+4*θ*t^2)-n16DiagBase θ t))

theorem n16Diagonal_eq {θ : ℝ} (hθ : 0 < θ) (t : I) :
    n16Diagonal θ t = (nelsen16 θ hθ.le).diagonal t := by
  rw [Copula.diagonal, nelsen16_cdf_full]
  by_cases ht : t = 0
  · subst t; simp [n16Diagonal]
  have hp : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm (fun h => ht (Subtype.ext h)))
  simp only [ht, or_self, ite_false]
  let s : ℝ := (t:ℝ)+(t:ℝ)-1-θ*((t:ℝ)⁻¹+(t:ℝ)⁻¹-1)
  have hb : n16DiagBase θ t = (t:ℝ)*s := by dsimp [n16DiagBase, s]; field_simp; ring
  have hsq : (n16DiagBase θ t)^2+4*θ*(t:ℝ)^2 = (t:ℝ)^2*(s^2+4*θ) := by rw [hb]; ring
  have hr : Real.sqrt ((n16DiagBase θ t)^2+4*θ*(t:ℝ)^2) = (t:ℝ)*Real.sqrt (s^2+4*θ) := by
    rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hp.le]
  have hs := Real.sq_sqrt (show 0 ≤ s^2+4*θ by nlinarith [sq_nonneg s])
  have hn := Real.sqrt_nonneg (s^2+4*θ)
  have hd : Real.sqrt (s^2+4*θ)-s ≠ 0 := by nlinarith
  unfold n16Diagonal
  rw [hr, hb]
  change (t:ℝ)*(2*θ/((t:ℝ)*Real.sqrt (s^2+4*θ)-(t:ℝ)*s)) = (s+Real.sqrt (s^2+4*θ))/2
  rw [← mul_sub]
  have he : (t:ℝ)*(2*θ/((t:ℝ)*(Real.sqrt (s^2+4*θ)-s))) =
      2*θ/(Real.sqrt (s^2+4*θ)-s) := by field_simp
  rw [he]
  apply (div_eq_iff hd).mpr
  nlinarith

theorem n16Diagonal_deriv_zero {θ : ℝ} (hθ : 0 < θ) : HasDerivAt (n16Diagonal θ) (1/2) 0 := by
  have hb : HasDerivAt (n16DiagBase θ) (θ-1) 0 := by
    convert (((hasDerivAt_id (0:ℝ)).pow 2).const_mul 2).add
      ((hasDerivAt_id (0:ℝ)).const_mul (θ-1)) |>.sub_const (2*θ) using 1
    · rfl
    · simp
  have hs : Real.sqrt ((n16DiagBase θ 0)^2+4*θ*0^2) = 2*θ := by
    have he : (n16DiagBase θ 0)^2+4*θ*0^2 = (2*θ)^2 := by simp [n16DiagBase]
    rw [he, Real.sqrt_sq (by linarith)]
  have hr := ((hb.pow 2).add (((hasDerivAt_id (0:ℝ)).pow 2).const_mul (4*θ))).sqrt
    (by dsimp [n16DiagBase]; nlinarith [sq_pos_of_pos hθ])
  have hd : Real.sqrt ((n16DiagBase θ 0)^2+4*θ*0^2)-n16DiagBase θ 0 ≠ 0 := by
    rw [hs]; dsimp [n16DiagBase]; nlinarith
  have hh := (hasDerivAt_id (0:ℝ)).mul ((hasDerivAt_const 0 (2*θ)).div (hr.sub hb) hd)
  convert hh using 1
  · rfl
  · simp only [Pi.div_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]
    rw [hs]
    simp only [n16DiagBase, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, add_zero, zero_sub,
      zero_mul, one_mul]
    field_simp
    ring

theorem nelsen16_lowerTail_pos {θ : ℝ} (hθ : 0 < θ) :
    (nelsen16 θ hθ.le).HasLowerTailDependence (1/2) :=
  hasLowerTailDependence_of_hasDerivWithinAt (n16Diagonal_eq hθ) (n16Diagonal_deriv_zero hθ).hasDerivWithinAt

theorem n16Diagonal_deriv_one {θ : ℝ} (hθ : 0 < θ) : HasDerivAt (n16Diagonal θ) 2 1 := by
  have hb : HasDerivAt (n16DiagBase θ) (θ+3) 1 := by
    convert (((hasDerivAt_id (1:ℝ)).pow 2).const_mul 2).add
      ((hasDerivAt_id (1:ℝ)).const_mul (θ-1)) |>.sub_const (2*θ) using 1
    · rfl
    · norm_num; ring
  have hs : Real.sqrt ((n16DiagBase θ 1)^2+4*θ*1^2) = 1+θ := by
    have he : (n16DiagBase θ 1)^2+4*θ*1^2 = (1+θ)^2 := by dsimp [n16DiagBase]; ring
    rw [he, Real.sqrt_sq (by linarith)]
  have hr := ((hb.pow 2).add (((hasDerivAt_id (1:ℝ)).pow 2).const_mul (4*θ))).sqrt
    (by dsimp [n16DiagBase]; nlinarith [sq_nonneg (1-θ)])
  have hd : Real.sqrt ((n16DiagBase θ 1)^2+4*θ*1^2)-n16DiagBase θ 1 ≠ 0 := by
    rw [hs]; dsimp [n16DiagBase]; nlinarith
  have hh := (hasDerivAt_id (1:ℝ)).mul ((hasDerivAt_const 1 (2*θ)).div (hr.sub hb) hd)
  convert hh using 1
  · rfl
  · simp only [Pi.div_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]
    rw [hs]
    norm_num only [n16DiagBase, one_pow, mul_one, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, one_mul, zero_mul, sub_zero, zero_sub]
    have hp : 1+θ ≠ 0 := ne_of_gt (by linarith)
    field_simp [hθ.ne', hp]
    ring_nf
    field_simp

theorem nelsen16_upperTail (θ : ℝ) (hθ : 0 ≤ θ) : (nelsen16 θ hθ).HasUpperTailDependence 0 := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen16_zero]
    exact hasUpperTailDependence_countermonotonic
  · have hp : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hz)
    simpa using hasUpperTailDependence_of_hasDerivWithinAt (n16Diagonal_eq hp)
      (n16Diagonal_deriv_one hp).hasDerivWithinAt

theorem nelsen16_tails (θ : ℝ) (hθ : 0 ≤ θ) :
    (nelsen16 θ hθ).HasLowerTailDependence (if θ = 0 then 0 else 1/2) ∧
      (nelsen16 θ hθ).HasUpperTailDependence 0 := by
  refine ⟨?_, nelsen16_upperTail θ hθ⟩
  by_cases hz : θ = 0
  · subst θ; simpa only [nelsen16_zero, ite_true] using hasLowerTailDependence_countermonotonic
  · simpa only [hz, ite_false] using nelsen16_lowerTail_pos (lt_of_le_of_ne hθ (Ne.symm hz))

end Verification
