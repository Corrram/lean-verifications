import Verification.CheckerboardMajorization
import Verification.CheckerboardEnergy

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Verification

/-- Uniform predictor bins and arbitrary response bins preserve the xi upper bound
for every conditionally increasing copula, including singular copulas. -/
theorem checkerboard_xi_le_of_isCI {n : ℕ} (C : Copula 2) (hC : C.IsCI)
    (m : ℕ) (hm : 0<m) (Q : IntervalPartition n) :
    (C.cellMass (IntervalPartition.uniform m hm) Q).checkerboard.chatterjeeXi ≤ C.chatterjeeXi := by
  let D := (C.cellMass (IntervalPartition.uniform m hm) Q).checkerboard
  have he : (∫ v : I, conditionalEnergy D v) ≤ ∫ v : I, conditionalEnergy C v := by
    rw [integral_partition Q _ (conditionalEnergy_measurable D)
      (fun j => conditionalEnergy_integrable_comp D (partitionEmbed_continuous Q j).measurable),
      integral_partition Q _ (conditionalEnergy_measurable C)
      (fun j => conditionalEnergy_integrable_comp C (partitionEmbed_continuous Q j).measurable)]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (Q.width_pos j).le
    apply integral_mono
      (conditionalEnergy_integrable_comp D (partitionEmbed_continuous Q j).measurable)
      (conditionalEnergy_integrable_comp C (partitionEmbed_continuous Q j).measurable)
    intro v
    change (∫ u : I, D.conditionalCDF u (partitionEmbed Q j v)^2) ≤ _
    rw [checkerboard_conditional_energy]
    exact checkerboardRow_energy_le C hC m hm Q j v
  change 6*(∫ v : I, conditionalEnergy D v)-2 ≤ 6*(∫ v : I, conditionalEnergy C v)-2
  linarith

/-- Theorem 4.2: the actual checkerboard matrix extracted from an MTP2 density. -/
theorem checkerboard_xi_le_of_mtp2 {n : ℕ} (C : Copula 2) (hC : C.HasMTP2Density)
    (m : ℕ) (hm : 0<m) (Q : IntervalPartition n) :
    (C.cellMass (IntervalPartition.uniform m hm) Q).checkerboard.chatterjeeXi ≤ C.chatterjeeXi :=
  checkerboard_xi_le_of_isCI C (mtp2_isCI hC) m hm Q

end Verification
