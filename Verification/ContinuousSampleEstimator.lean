import Verification.SampleEstimatorConsistency
import Copula.Sklar.Continuous

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def realSampleRankCopula {Ω : Type*} (X : ℕ → Ω → (Fin 2 → ℝ)) (n : ℕ) (ω : Ω) : Copula 2 := by
  classical
  let x : Fin (n+1) → (Fin 2 → ℝ) := fun i => X i.val ω
  exact if h : Function.Injective (fun i => x i 0) ∧ Function.Injective (fun i => x i 1) then
    rankCopula (n+1) (by omega) (finiteRanks _ h.1) (finiteRanks _ h.2)
  else Copula.independence 2

noncomputable def realSampleCheckerboardEstimator {Ω : Type*} (X : ℕ → Ω → (Fin 2 → ℝ))
    (κ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  checkerboardEstimator ((realSampleRankCopula X n ω).cellMass
    (IntervalPartition.uniform (powerGridIndex κ n+1) (by omega))
    (IntervalPartition.uniform (powerGridIndex κ n+1) (by omega)))

/-- The probability integral transform leaves sample ranks unchanged, including
continuous marginal CDFs with flat intervals. -/
theorem realSampleRankCopula_transform {Ω : Type*} (ν : ProbabilityMeasure (Fin 2 → ℝ))
    (X : ℕ → Ω → (Fin 2 → ℝ)) (n : ℕ) (ω : Ω)
    (hi : ∀ d : Fin 2, Function.Injective (fun i : Fin (n+1) => marginalTransform ν (X i.val ω) d)) :
    realSampleRankCopula X n ω=sampleRankCopula (fun i ω => marginalTransform ν (X i ω)) n ω := by
  have hx (d : Fin 2) : Function.Injective (fun i : Fin (n+1) => X i.val ω d) := by
    intro i j hij
    apply hi d
    exact congrArg (cdfUnit (marginal ν d)) hij
  rw [realSampleRankCopula,dite_eq_left ⟨hx 0,hx 1⟩,sampleRankCopula,dite_eq_left ⟨hi 0,hi 1⟩]
  have he (d : Fin 2) : finiteRanks (fun i : Fin (n+1) => X i.val ω d) (hx d) =
      finiteRanks (fun i : Fin (n+1) => marginalTransform ν (X i.val ω) d) (hi d) :=
    finiteRanks_comp_mono _ (cdfUnit (marginal ν d)) (ProbabilityTheory.monotone_cdf (marginal ν d)) (hx d) (hi d)
  rw [he 0,he 1]

/-- Theorem 4.5 statistical conclusion for real observations with continuous
marginal CDFs. The estimator uses the original data ranks. -/
theorem realSampleCheckerboardEstimator_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ d, Continuous (ProbabilityTheory.cdf (marginal ν d)))
    (X : ℕ → Ω → (Fin 2 → ℝ)) (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i)=ν.toMeasure) (κ : ℝ) (hκ : 0<κ) (hκ' : κ≤1/3) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => realSampleCheckerboardEstimator X κ n ω) atTop
      (𝓝 (ofContinuousMarginals ν hc).chatterjeeXi) := by
  let C := ofContinuousMarginals ν hc
  let Y : ℕ → Ω → (Fin 2 → I) := fun i ω => marginalTransform ν (X i ω)
  have hY (i : ℕ) : Measurable (Y i) := (measurable_marginalTransform ν).comp (hX i)
  have hYI : iIndepFun Y μ := hI.comp (fun _ => marginalTransform ν) (fun _ => measurable_marginalTransform ν)
  have hYlaw (i : ℕ) : μ.map (Y i)=C.toMeasure := by
    change μ.map (marginalTransform ν ∘ X i)=C.toMeasure
    rw [← Measure.map_map (measurable_marginalTransform ν) (hX i),hlaw]
    rfl
  filter_upwards [sampleCheckerboardEstimator_ae_tendsto μ C Y hY hYI hYlaw κ hκ hκ',
    copulaSample_ae_injective μ C Y hY hYI hYlaw] with ω hω hi
  have he (n : ℕ) : realSampleCheckerboardEstimator X κ n ω=sampleCheckerboardEstimator Y κ n ω := by
    unfold realSampleCheckerboardEstimator sampleCheckerboardEstimator
    rw [realSampleRankCopula_transform ν X n ω (fun d => (hi d).comp Fin.val_injective)]
  simpa only [he] using hω

end Verification
