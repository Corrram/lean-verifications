import Verification.ConditionalBlocks
import Verification.ConditionalMeanMoments

/-! # The correlation ratio under diagonal localization -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

theorem conditionalBlocks_correlationRatio (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    correlationRatio (conditionalBlocks C D a ha0 ha1) =
      1-(a : ℝ)^3*(1-correlationRatio C)-(1-(a : ℝ))^3*(1-correlationRatio D) := by
  let f := fun u => ((a : ℝ)*(conditionalMean C u-1/2)+(-(1-(a : ℝ))/2))^2
  let g := fun u => ((1-(a : ℝ))*(conditionalMean D u-1/2)+(a : ℝ)/2)^2
  have he : (fun u => (conditionalMean (conditionalBlocks C D a ha0 ha1) u-1/2)^2) =ᵐ[volume]
      unitJoin a f g := by
    filter_upwards [conditionalMean_conditionalBlocks C D a ha0 ha1] with u hu
    rw [hu]
    unfold unitJoin
    split_ifs <;> dsimp [f,g] <;> ring
  have hf : Measurable f := by
    exact ((measurable_const.mul ((conditionalMean_measurable C).sub measurable_const)).add measurable_const).pow_const 2
  have hg : Measurable g := by
    exact ((measurable_const.mul ((conditionalMean_measurable D).sub measurable_const)).add measurable_const).pow_const 2
  rw [correlationRatio,integral_congr_ae he,integral_unitJoin a ha0 ha1 f g hf hg
    (conditionalMean_affine_square_integrable C (a : ℝ) (-(1-(a : ℝ))/2))
    (conditionalMean_affine_square_integrable D (1-(a : ℝ)) ((a : ℝ)/2))]
  dsimp [f,g]
  rw [conditionalMean_affine_square_integral,conditionalMean_affine_square_integral]
  unfold correlationRatio
  ring

end Verification
