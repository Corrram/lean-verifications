import Papers.AnsariRockelSteinmassl2026RhoGamma.ThetaBoundary

/-! # Definition 3.8 as an equality of probability measures -/

open MeasureTheory ProbabilityTheory Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

private theorem signed_block_law (A : RhoGamma.AuxiliaryCertificate) (e : Bool) :
    A.magnitudes.toMeasure.map (fun x => RhoGamma.signedLift e (RhoGamma.thresholdSign A.t x) (x 0) (x 1)) =
      ENNReal.ofReal (A.a : ℝ) • volume.map (fun u : I => RhoGamma.signedLift e false
        (Copula.OrdinalSum.lowerEmbed A.a u) (Copula.OrdinalSum.lowerEmbed A.a u)) +
      ENNReal.ofReal A.z • A.D.toMeasure.map (fun x => RhoGamma.signedLift e true
        (Copula.OrdinalSum.upperEmbed A.a (x 0)) (Copula.OrdinalSum.upperEmbed A.a (x 1))) := by
  have hm : Measurable (fun x : Fin 2 → I => RhoGamma.signedLift e (RhoGamma.thresholdSign A.t x) (x 0) (x 1)) :=
    RhoGamma.measurable_signedLift (by fun_prop) (by fun_prop) (RhoGamma.measurable_thresholdSign A.t) e
  have hz : 1 - (A.a : ℝ) = A.z := by linarith [A.a_add_z]
  rw [RhoGamma.AuxiliaryCertificate.magnitudes, Copula.toMeasure_ordinalSum,
    Measure.map_add _ _ hm, Measure.map_smul _ hm.aemeasurable, Measure.map_smul _ hm.aemeasurable, hz,
    Measure.map_map hm (by fun_prop), Measure.map_map hm (by fun_prop)]
  congr 1
  · congr 1
    rw [Copula.toMeasure_comonotonic, Measure.map_map (hm.comp (by fun_prop)) (by fun_prop)]
    apply Measure.map_congr
    filter_upwards [] with u
    change RhoGamma.signedLift e
      (RhoGamma.thresholdSign A.t (fun i => Copula.OrdinalSum.lowerEmbed A.a ((fun _ : Fin 2 => u) i))) _ _ = _
    rw [A.lower_threshold]
  · congr 1
    apply Measure.map_congr
    filter_upwards [A.upper_threshold_ae] with x hx
    simp only [Function.comp_apply, hx]

/-- The source construction: a diagonal lower-magnitude block with opposite signs,
then the upper auxiliary block with equal signs, followed by an independent fair sign. -/
theorem glued_copula_probability_law (A : RhoGamma.AuxiliaryCertificate) :
    A.copula.toMeasure =
      ENNReal.ofReal (A.a : ℝ) • fairMeasure volume
        (fun u : I => RhoGamma.signedLift true false
          (Copula.OrdinalSum.lowerEmbed A.a u) (Copula.OrdinalSum.lowerEmbed A.a u))
        (fun u : I => RhoGamma.signedLift false false
          (Copula.OrdinalSum.lowerEmbed A.a u) (Copula.OrdinalSum.lowerEmbed A.a u)) +
      ENNReal.ofReal A.z • fairMeasure A.D.toMeasure
        (fun x => RhoGamma.signedLift true true
          (Copula.OrdinalSum.upperEmbed A.a (x 0)) (Copula.OrdinalSum.upperEmbed A.a (x 1)))
        (fun x => RhoGamma.signedLift false true
          (Copula.OrdinalSum.upperEmbed A.a (x 0)) (Copula.OrdinalSum.upperEmbed A.a (x 1))) := by
  change fairMeasure A.magnitudes.toMeasure
    (fun x => RhoGamma.signedLift true (RhoGamma.thresholdSign A.t x) (x 0) (x 1))
    (fun x => RhoGamma.signedLift false (RhoGamma.thresholdSign A.t x) (x 0) (x 1)) = _
  rw [fairMeasure, signed_block_law A true, signed_block_law A false]
  simp only [fairMeasure, smul_add, smul_smul]
  ac_rfl

end Papers.AnsariRockelSteinmassl2026RhoGamma
