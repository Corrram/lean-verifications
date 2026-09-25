import Copula.Distribution.GammaLaplace

open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal

namespace Verification

theorem gammaPDF_power_exp {a b k d x : ℝ} (ha : 0<a) (hb : 0<b)
    (hak : 0<a+k) (hbd : 0<b+d) (hx : 0<x) :
    gammaPDF a b x*ENNReal.ofReal (x^k*exp (-(d*x)))=
      ENNReal.ofReal (b^a/Gamma a*Gamma (a+k)/(b+d)^(a+k))*gammaPDF (a+k) (b+d) x := by
  rw [gammaPDF_of_nonneg hx.le,gammaPDF_of_nonneg hx.le,
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hp : x^(a+k-1)=x^(a-1)*x^k := by
    rw [show a+k-1=(a-1)+k by ring,Real.rpow_add hx]
  have he : exp (-((b+d)*x))=exp (-(b*x))*exp (-(d*x)) := by
    rw [show -((b+d)*x)=-(b*x)+-(d*x) by ring,Real.exp_add]
  rw [hp,he]
  have hG := (Real.Gamma_pos_of_pos hak).ne'
  have hB := (Real.rpow_pos_of_pos hbd (a+k)).ne'
  field_simp

theorem lintegral_power_exp_gammaMeasure {a b k d : ℝ} (ha : 0<a) (hb : 0<b)
    (hak : 0<a+k) (hbd : 0<b+d) :
    (∫⁻ x, ENNReal.ofReal (x^k*exp (-(d*x))) ∂gammaMeasure a b)=
      ENNReal.ofReal (b^a/Gamma a*Gamma (a+k)/(b+d)^(a+k)) := by
  have hpdf (a b : ℝ) : Measurable (gammaPDF a b) := (measurable_gammaPDFReal a b).ennreal_ofReal
  rw [gammaMeasure,lintegral_withDensity_eq_lintegral_mul _ (hpdf a b) (by fun_prop)]
  have he : (fun x => gammaPDF a b x*ENNReal.ofReal (x^k*exp (-(d*x))))=ᵐ[volume]
      fun x => ENNReal.ofReal (b^a/Gamma a*Gamma (a+k)/(b+d)^(a+k))*gammaPDF (a+k) (b+d) x := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with x hx
    rcases lt_or_gt_of_ne hx with hn|hp
    · simp only [gammaPDF_of_neg hn,zero_mul,mul_zero]
    · exact gammaPDF_power_exp ha hb hak hbd hp
  simp only [Pi.mul_apply]
  rw [lintegral_congr_ae he,lintegral_const_mul _ (hpdf (a+k) (b+d)),
    lintegral_gammaPDF_eq_one hak hbd,mul_one]

end Verification
