import Verification.ConditionalCopula
import Copula.Rank.ConditionalCDF
import Copula.Dependence.ConditionalMonotonicity

/-! # Constructing a copula from a family of conditional CDFs -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

/-- Integral construction, with uniform mean and monotonicity in the response threshold. -/
theorem conditional_integral_classical_ae (h : I → I → ℝ)
    (hi : ∀ v, Integrable (h v))
    (hm : ∀ u, Monotone (fun v => h v u))
    (hz : h 0 =ᵐ[volume] fun _ => 0) (ho : h 1 =ᵐ[volume] fun _ => 1)
    (hmean : ∀ v, (∫ u : I, h v u) = (v : ℝ)) :
    Copula.IsClassical (fun z : Fin 2 → I => ∫ u in Iic (z 0), h (z 1) u) := by
  apply Copula.IsClassical.ofBivariate (fun u v => ∫ t in Iic u, h v t)
  · intro v
    have he : Iic (0 : I) = {0} := by ext u; simp
    simp [he]
  · intro u
    rw [integral_congr_ae (ae_restrict_of_ae hz)]
    simp
  · intro v
    have he : Iic (1 : I) = univ := by ext u; simp [unitInterval.le_one']
    simpa only [he, Measure.restrict_univ] using hmean v
  · intro u
    rw [integral_congr_ae (ae_restrict_of_ae ho)]
    simp [integral_const, Measure.real, unitInterval.volume_Iic,
      ENNReal.toReal_ofReal u.property.1]
  · intro a b c d hab hcd
    have hc := Copula.integral_Iic_add_Ioc_unit (hi c) hab
    have hd := Copula.integral_Iic_add_Ioc_unit (hi d) hab
    have he := setIntegral_mono_on (hi c).integrableOn (hi d).integrableOn
      measurableSet_Ioc (fun u (_ : u ∈ Ioc a b) => hm u hcd)
    linarith

noncomputable def copulaOfConditionalAE (h : I → I → ℝ)
    (hi : ∀ v, Integrable (h v))
    (hm : ∀ u, Monotone (fun v => h v u))
    (hz : h 0 =ᵐ[volume] fun _ => 0) (ho : h 1 =ᵐ[volume] fun _ => 1)
    (hmean : ∀ v, (∫ u : I, h v u) = (v : ℝ)) : Copula 2 :=
  Copula.ofClassical _ (conditional_integral_classical_ae h hi hm hz ho hmean)

theorem copulaOfConditionalAE_cdf (h : I → I → ℝ)
    (hi : ∀ v, Integrable (h v))
    (hm : ∀ u, Monotone (fun v => h v u))
    (hz : h 0 =ᵐ[volume] fun _ => 0) (ho : h 1 =ᵐ[volume] fun _ => 1)
    (hmean : ∀ v, (∫ u : I, h v u) = (v : ℝ)) (u v : I) :
    (copulaOfConditionalAE h hi hm hz ho hmean).cdf ![u, v] = ∫ t in Iic u, h v t := by
  simp [copulaOfConditionalAE]

theorem copulaOfConditionalAE_kernel (h : I → I → ℝ)
    (hi : ∀ v, Integrable (h v))
    (hm : ∀ u, Monotone (fun v => h v u))
    (hz : h 0 =ᵐ[volume] fun _ => 0) (ho : h 1 =ᵐ[volume] fun _ => 1)
    (hmean : ∀ v, (∫ u : I, h v u) = (v : ℝ)) (hn : ∀ v u, 0 ≤ h v u) (v : I) :
    (fun u => (copulaOfConditionalAE h hi hm hz ho hmean).conditionalCDF u v) =ᵐ[volume]
      h v := by
  apply Copula.conditionalCDF_ae_eq_of_integral _ v (hi v)
  · intro u
    exact hn v u
  · intro u
    exact (copulaOfConditionalAE_cdf h hi hm hz ho hmean u v).symm

end Verification
