import Verification.SampleRankCopula
import Verification.PowerGrid

open MeasureTheory ProbabilityTheory Filter
open Copula
open scoped unitInterval Topology

namespace Verification

/-- The sample size is n+1; the grid order is exactly floor((n+1)^κ). -/
noncomputable def sampleCheckerboardEstimator {Ω : Type*} (X : ℕ → Ω → (Fin 2 → I))
    (κ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  checkerboardEstimator ((sampleRankCopula X n ω).cellMass
    (IntervalPartition.uniform (powerGridIndex κ n+1) (by omega))
    (IntervalPartition.uniform (powerGridIndex κ n+1) (by omega)))

/-- Almost-sure consistency of the rank-based checkerboard estimator, proved
from independence and the actual sampling law. -/
theorem sampleCheckerboardEstimator_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : Copula 2) (X : ℕ → Ω → (Fin 2 → I))
    (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i)=C.toMeasure)
    (κ : ℝ) (hκ : 0<κ) (hκ' : κ≤1/3) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => sampleCheckerboardEstimator X κ n ω) atTop (𝓝 C.chatterjeeXi) := by
  filter_upwards [sampleRankCopula_ae_rate μ C X hX hI hlaw] with ω hω
  exact checkerboardEstimator_tendsto_of_cdf_error C (fun n => sampleRankCopula X n ω)
    (powerGridIndex κ) (powerGridIndex_tendsto κ hκ)
    (fun n => 3*empiricalCDFRadius n+8/((n : ℝ)+1)) hω
    (powerGridIndex_rate_tendsto κ hκ.le hκ')

end Verification
