import Papers.AnsariRockelSteinmassl2026RhoGamma.ElementaryArc

/-! # The support of the five-piece shuffle on the elementary arc -/

open MeasureTheory ProbabilityTheory Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

private theorem ae_of_lifts (A : RhoGamma.AuxiliaryCertificate) {P : (Fin 2 → I) → Prop}
    (hP : MeasurableSet {x | P x})
    (hL : ∀ (e : Bool) (u : I), P (RhoGamma.signedLift e false
      (Copula.OrdinalSum.lowerEmbed A.a u) (Copula.OrdinalSum.lowerEmbed A.a u)))
    (hU : ∀ᵐ x ∂A.D.toMeasure, ∀ e : Bool, P (RhoGamma.signedLift e true
      (Copula.OrdinalSum.upperEmbed A.a (x 0)) (Copula.OrdinalSum.upperEmbed A.a (x 1)))) :
    ∀ᵐ x ∂A.copula.toMeasure, P x := by
  have he (e : Bool) : ∀ᵐ x ∂A.magnitudes.toMeasure,
      P (RhoGamma.signedLift e (RhoGamma.thresholdSign A.t x) (x 0) (x 1)) := by
    have hm : Measurable (fun x : Fin 2 → I =>
        RhoGamma.signedLift e (RhoGamma.thresholdSign A.t x) (x 0) (x 1)) :=
      RhoGamma.measurable_signedLift (by fun_prop) (by fun_prop) (RhoGamma.measurable_thresholdSign A.t) e
    rw [RhoGamma.AuxiliaryCertificate.magnitudes, Copula.toMeasure_ordinalSum, ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      apply (ae_map_iff (show Measurable _ by fun_prop).aemeasurable (hP.preimage hm)).2
      rw [Copula.toMeasure_comonotonic]
      apply (ae_map_iff (show Measurable _ by fun_prop).aemeasurable ((hP.preimage hm).preimage (by fun_prop))).2
      filter_upwards [] with u
      change P (RhoGamma.signedLift e
        (RhoGamma.thresholdSign A.t (fun i => Copula.OrdinalSum.lowerEmbed A.a ((fun _ : Fin 2 => u) i)))
        (Copula.OrdinalSum.lowerEmbed A.a u) (Copula.OrdinalSum.lowerEmbed A.a u))
      rw [A.lower_threshold]
      exact hL e u
    · apply Measure.ae_smul_measure
      apply (ae_map_iff (show Measurable _ by fun_prop).aemeasurable (hP.preimage hm)).2
      filter_upwards [hU, A.upper_threshold_ae] with x hx ht
      simpa only [ht] using hx e
  change ∀ᵐ x ∂fairMeasure A.magnitudes.toMeasure
    (fun x => RhoGamma.signedLift true (RhoGamma.thresholdSign A.t x) (x 0) (x 1))
    (fun x => RhoGamma.signedLift false (RhoGamma.thresholdSign A.t x) (x 0) (x 1)), P x
  rw [fairMeasure, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_map_iff (RhoGamma.measurable_signedLift (by fun_prop) (by fun_prop)
      (RhoGamma.measurable_thresholdSign A.t) true).aemeasurable hP).2 (he true)
  · apply Measure.ae_smul_measure
    exact (ae_map_iff (RhoGamma.measurable_signedLift (by fun_prop) (by fun_prop)
      (RhoGamma.measurable_thresholdSign A.t) false).aemeasurable hP).2 (he false)

/-- The middle antidiagonal and the two pairs of parallel corner segments. -/
def FivePieceSupport (d : ℝ) (x : Fin 2 → I) : Prop :=
  (d ≤ (x 0 : ℝ) ∧ (x 0 : ℝ) ≤ 1 - d ∧ (x 1 : ℝ) = 1 - x 0) ∨
  ((x 0 : ℝ) ≤ d ∧ (x 1 : ℝ) ≤ d ∧ |(x 0 : ℝ) - x 1| = d / 2) ∨
  (1 - d ≤ (x 0 : ℝ) ∧ 1 - d ≤ (x 1 : ℝ) ∧ |(x 0 : ℝ) - x 1| = d / 2)

private theorem measurable_fivePieceSupport (d : ℝ) : MeasurableSet {x | FivePieceSupport d x} := by
  unfold FivePieceSupport
  measurability

private theorem lower_lift_support (A : RhoGamma.AuxiliaryCertificate) (e : Bool) (u : I) :
    FivePieceSupport (A.z / 2) (RhoGamma.signedLift e false
      (Copula.OrdinalSum.lowerEmbed A.a u) (Copula.OrdinalSum.lowerEmbed A.a u)) := by
  have hu := u.property
  have ha := A.a_pos
  have haz := A.a_add_z
  have hlo : 0 ≤ (A.a : ℝ) * u := mul_nonneg ha.le u.property.1
  have hhi : (A.a : ℝ) * u ≤ A.a := by nlinarith [u.property.2]
  apply Or.inl
  cases e <;>
    simp only [RhoGamma.signedLift, signedRank, Bool.false_eq_true, ite_false, ite_true,
      Bool.not_false, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      coe_positiveRank, coe_negativeRank, Copula.OrdinalSum.lowerEmbed]
  all_goals exact ⟨by linarith, by linarith, by ring⟩

private theorem upper_lift_support (A : RhoGamma.AuxiliaryCertificate) (e : Bool) (u v : I)
    (h : |(u : ℝ) - v| = 1 / 2) :
    FivePieceSupport (A.z / 2) (RhoGamma.signedLift e true
      (Copula.OrdinalSum.upperEmbed A.a u) (Copula.OrdinalSum.upperEmbed A.a v)) := by
  have ha := A.a_pos
  have haz := A.a_add_z
  have hz := A.z_pos
  have hu0 := mul_nonneg hz.le u.property.1
  have hv0 := mul_nonneg hz.le v.property.1
  have huz := mul_le_mul_of_nonneg_left u.property.2 hz.le
  have hvz := mul_le_mul_of_nonneg_left v.property.2 hz.le
  have hab : 1 - (A.a : ℝ) = A.z := by linarith
  have he : |A.z * ((u : ℝ) - v) / 2| = A.z / 2 / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hz, h]
    norm_num
    ring
  cases e
  · apply Or.inr (Or.inl ?_)
    simp only [RhoGamma.signedLift, signedRank, Bool.false_eq_true, ite_false,
      Bool.not_true, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      coe_negativeRank, Copula.OrdinalSum.upperEmbed, hab]
    refine ⟨by linarith, by linarith, ?_⟩
    rw [show (1 - ((A.a : ℝ) + A.z * u)) / 2 - (1 - ((A.a : ℝ) + A.z * v)) / 2 =
      -(A.z * ((u : ℝ) - v) / 2) by ring, abs_neg, he]
  · apply Or.inr (Or.inr ?_)
    simp only [RhoGamma.signedLift, signedRank, ite_true,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      coe_positiveRank, Copula.OrdinalSum.upperEmbed, hab]
    refine ⟨by linarith, by linarith, ?_⟩
    rw [show (1 + ((A.a : ℝ) + A.z * u)) / 2 - (1 + ((A.a : ℝ) + A.z * v)) / 2 =
      A.z * ((u : ℝ) - v) / 2 by ring, he]

/-- Example 3.10: the constructed optimizer is carried by exactly the stated five segments. -/
theorem elementary_shuffle_support {s : ℝ} (hs : 1 ≤ s) :
    let A := RhoGamma.AuxiliaryCertificate.halfShift s hs
    ∀ᵐ x ∂A.copula.toMeasure, FivePieceSupport (A.z / 2) x := by
  dsimp only
  apply ae_of_lifts _ (measurable_fivePieceSupport _) (lower_lift_support _)
  have h : ∀ᵐ x ∂RhoFootrule.halfTurn.toMeasure, |(x 0 : ℝ) - x 1| = 1 / 2 := by
    have hh := (RhoFootrule.quadratic_equality_iff RhoFootrule.halfTurn).mp (by
      rw [RhoFootrule.halfTurn_rho, RhoFootrule.halfTurn_footrule]
      norm_num)
    norm_num only [RhoFootrule.halfTurn_footrule] at hh
    exact hh
  filter_upwards [h] with x hx
  exact fun e => upper_lift_support _ e (x 0) (x 1) hx

end Papers.AnsariRockelSteinmassl2026RhoGamma
