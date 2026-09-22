import Verification.ContinuousSampleEstimator
import Verification.EstimatorCost
import Verification.Karamata

/-! # Statistical consistency, exact rank binning, and unit-cost work -/

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open Copula Verification
open scoped unitInterval BigOperators Topology

namespace Papers.Rockel2025Approximation

theorem majorization_sum_convex (a b : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f)
    (hb : ∀ i, i<n-1 → b (i+1)≤b i)
    (hp : ∀ k, k≤n → (∑ i ∈ Finset.range k, b i) ≤ ∑ i ∈ Finset.range k, a i)
    (ht : (∑ i ∈ Finset.range n, a i)=∑ i ∈ Finset.range n, b i) :
    (∑ i ∈ Finset.range n, f (b i)) ≤ ∑ i ∈ Finset.range n, f (a i) :=
  Verification.majorization_sum_convex a b n f hf hb hp ht

theorem rankCopula_cellMass {m r n : ℕ} (hn : 0<n) (rx ry : Equiv.Perm (Fin n))
    (P : IntervalPartition m) (Q : IntervalPartition r) (i : Fin m) (j : Fin r) :
    ((rankCopula n hn rx ry).cellMass P Q).mass i j = (n : ℝ)*∑ k,
      cellOverlap P (IntervalPartition.uniform n hn) i (rx k)*
      cellOverlap Q (IntervalPartition.uniform n hn) j (ry k) :=
  Verification.rankCopula_cellMass hn rx ry P Q i j

theorem sampleRankCopula_ae_rate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : Copula 2) (X : ℕ → Ω → (Fin 2 → I))
    (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i)=C.toMeasure) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ u v : I,
      |(sampleRankCopula X n ω).cdf ![u,v]-C.cdf ![u,v]| ≤ 3*empiricalCDFRadius n+8/((n : ℝ)+1) :=
  Verification.sampleRankCopula_ae_rate μ C X hX hI hlaw

theorem sampleCheckerboardEstimator_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : Copula 2) (X : ℕ → Ω → (Fin 2 → I))
    (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i)=C.toMeasure)
    (κ : ℝ) (hκ : 0<κ) (hκ' : κ≤1/3) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => sampleCheckerboardEstimator X κ n ω) atTop (𝓝 C.chatterjeeXi) :=
  Verification.sampleCheckerboardEstimator_ae_tendsto μ C X hX hI hlaw κ hκ hκ'

theorem realSampleCheckerboardEstimator_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ d, Continuous (ProbabilityTheory.cdf (marginal ν d)))
    (X : ℕ → Ω → (Fin 2 → ℝ)) (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i)=ν.toMeasure) (κ : ℝ) (hκ : 0<κ) (hκ' : κ≤1/3) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => realSampleCheckerboardEstimator X κ n ω) atTop
      (𝓝 (ofContinuousMarginals ν hc).chatterjeeXi) :=
  Verification.realSampleCheckerboardEstimator_ae_tendsto μ ν hc X hX hI hlaw κ hκ hκ'

theorem rankCopula_cellMass_four_slots (K n : ℕ) (hK : 0<K) (hn : 0<n) (hKn : K≤n)
    (rx ry : Equiv.Perm (Fin n)) (i j : Fin K) :
    ((rankCopula n hn rx ry).cellMass (IntervalPartition.uniform K hK) (IntervalPartition.uniform K hK)).mass i j =
    (n : ℝ)*∑ k : Fin n, ∑ a : Fin 2, ∑ b : Fin 2,
      (if i.val=(rx k).val*K/n+a.val then cellOverlap (IntervalPartition.uniform K hK) (IntervalPartition.uniform n hn) i (rx k) else 0)*
      (if j.val=(ry k).val*K/n+b.val then cellOverlap (IntervalPartition.uniform K hK) (IntervalPartition.uniform n hn) j (ry k) else 0) :=
  Verification.rankCopula_cellMass_four_slots K n hK hn hKn rx ry i j

theorem checkerboardEstimatorWork_isBigO {α β : Type*} (leX : α → α → Bool) (leY : β → β → Bool)
    (xs : ℕ → List α) (ys : ℕ → List β) (hx : ∀ n, (xs n).length=n+1) (hy : ∀ n, (ys n).length=n+1)
    (κ : ℝ) (hκ : 0≤κ) (hκ' : κ≤1/3) :
    (fun n => (checkerboardEstimatorWork leX leY (xs n) (ys n) (powerGridIndex κ n+1) : ℝ)) =O[atTop]
      (fun n => ((n : ℝ)+1)*Real.log ((n : ℝ)+1)) :=
  Verification.checkerboardEstimatorWork_isBigO leX leY xs ys hx hy κ hκ hκ'

end Papers.Rockel2025Approximation
