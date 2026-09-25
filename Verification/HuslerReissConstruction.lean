import Verification.StableTailExtremeValue
import Mathlib.Probability.Distributions.Gaussian.Real

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Verification

noncomputable def lognormalSpectralWeight (s z : ℝ) : ℝ := Real.exp (s*z-s^2/2)

theorem lognormalSpectralWeight_integrable (s : ℝ) :
    Integrable (lognormalSpectralWeight s) (gaussianReal 0 1) := by
  change Integrable (fun z => Real.exp (s*z-s^2/2)) (gaussianReal 0 1)
  simp only [sub_eq_add_neg,Real.exp_add]
  exact (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) s).mul_const (Real.exp (-(s^2/2)))

theorem lognormalSpectralWeight_mean (s : ℝ) :
    ∫ z,lognormalSpectralWeight s z ∂gaussianReal 0 1=1 := by
  have h : (∫ z,Real.exp (s*z) ∂gaussianReal 0 1)=Real.exp (s^2/2) := by
    have he := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) s
    simpa [mgf] using he
  simp only [lognormalSpectralWeight,Real.exp_sub]
  rw [integral_div,h,div_self (Real.exp_ne_zero _)]

noncomputable def huslerReissStableTail (δ : ℝ) : StableTail :=
  spectralStableTail (gaussianReal 0 1) (lognormalSpectralWeight (2/δ)) (fun _ => 1)
    (lognormalSpectralWeight_integrable _) (integrable_const 1)
    (fun _ => (Real.exp_pos _).le) (fun _ => zero_le_one)
    (lognormalSpectralWeight_mean _) (by simp)

/-- The positive-parameter Hüsler–Reiss spectral construction.
The paper's explicit Gaussian-CDF formula is identified in `HuslerReissFormula.lean`. -/
noncomputable def huslerReissPositive (δ : ℝ) (_hδ : 0<δ) : Copula 2 :=
  stableTailCopula (huslerReissStableTail δ)

theorem huslerReissPositive_isExtremeValue (δ : ℝ) (hδ : 0<δ) :
    (huslerReissPositive δ hδ).IsExtremeValue :=
  stableTailCopula_isExtremeValue _

theorem huslerReissPositive_isCI (δ : ℝ) (hδ : 0<δ) :
    (huslerReissPositive δ hδ).IsCI := stableTailCopula_isCI _

theorem huslerReissPositive_pickands_spectral (δ : ℝ) (hδ : 0<δ) (t : I) :
    copulaPickands (huslerReissPositive δ hδ) t=
      ∫ z,max ((1-(t:ℝ))*Real.exp ((2/δ)*z-(2/δ)^2/2)) (t:ℝ) ∂gaussianReal 0 1 := by
  rw [huslerReissPositive,stableTailCopula_pickands]
  simp only [huslerReissStableTail,spectralStableTail,spectralTail,lognormalSpectralWeight,mul_one]

end Verification
