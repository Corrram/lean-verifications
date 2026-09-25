import Copula.Distribution.GammaLaplace
import Mathlib.MeasureTheory.Measure.OpenPos

open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal

namespace Verification

theorem volume_positive_absolutelyContinuous_gamma {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    (volume : Measure ℝ).restrict (Ioi 0) ≪ gammaMeasure a b := by
  have hm : Measurable (gammaPDF a b) := (measurable_gammaPDFReal a b).ennreal_ofReal
  have hp : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Ioi 0),gammaPDF a b x≠0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (ENNReal.ofReal_pos.mpr (gammaPDFReal_pos ha hb hx)).ne'
  have he := withDensity_absolutelyContinuous' (μ := (volume : Measure ℝ).restrict (Ioi 0)) hm.aemeasurable hp
  rw [← restrict_withDensity measurableSet_Ioi] at he
  exact he.trans Measure.restrict_le_self.absolutelyContinuous

theorem gamma_ae_eq_constant_of_continuousOn {a b : ℝ} (ha : 0<a) (hb : 0<b)
    {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousOn f (Ioi 0)) (he : f=ᵐ[gammaMeasure a b] fun _ => c) :
    ∀ x∈Ioi (0:ℝ),f x=c := by
  have h := (volume_positive_absolutelyContinuous_gamma ha hb).ae_eq he
  exact volume.eqOn_open_of_ae_eq h isOpen_Ioi hf continuousOn_const

end Verification
