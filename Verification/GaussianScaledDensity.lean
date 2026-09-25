import Verification.GaussianNormalDensity
import Verification.GaussianRhoIntegral

open ProbabilityTheory MeasureTheory Set
open scoped ENNReal

namespace Verification

theorem standardNormal_scaled_joint_density (r a b : ℝ) (ha : a≠0) (hb : b≠0) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ×ℝ => (a*p.1,r*(a*p.1)+b*p.2))=
      (volume : Measure (ℝ×ℝ)).withDensity
        (fun p => gaussianPDF 0 (NNReal.mk (a^2) (sq_nonneg a)) p.1*
          gaussianPDF (r*p.1) (NNReal.mk (b^2) (sq_nonneg b)) p.2) := by
  let v := NNReal.mk (b^2) (sq_nonneg b)
  let w := NNReal.mk (a^2) (sq_nonneg a)
  have hv : v≠0 := by
    intro h
    have h' : b^2=0 := congrArg (fun t : NNReal => (t:ℝ)) h
    exact hb (sq_eq_zero_iff.mp h')
  have hw : w≠0 := by
    intro h
    have h' : a^2=0 := congrArg (fun t : NNReal => (t:ℝ)) h
    exact ha (sq_eq_zero_iff.mp h')
  have hd : Measurable (fun p : ℝ×ℝ => gaussianPDF 0 w p.1*gaussianPDF (r*p.1) v p.2) := by
    unfold gaussianPDF gaussianPDFReal
    fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  have hfm : Measurable (fun p : ℝ×ℝ => f (a*p.1,r*(a*p.1)+b*p.2)) := hf.comp (by fun_prop)
  have hfx (x : ℝ) : Measurable (fun y : ℝ => f (x,y)) := hf.comp measurable_prodMk_left
  rw [lintegral_map hf (by fun_prop),lintegral_prod _ hfm.aemeasurable]
  have he (x : ℝ) : (∫⁻ y, f (a*x,r*(a*x)+b*y) ∂gaussianReal 0 1)=
      ∫⁻ y, gaussianPDF (r*(a*x)) v y*f (a*x,y) := by
    rw [← lintegral_map (hfx (a*x)) (by fun_prop),standardNormal_affine_map,
      gaussianReal_of_var_ne_zero _ hv]
    exact lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) (hfx (a*x))
  simp_rw [he]
  let F := fun x : ℝ => ∫⁻ y, gaussianPDF (r*x) v y*f (x,y)
  have hF : Measurable F := by
    apply Measurable.lintegral_prod_right
    have hg : Measurable (fun p : ℝ×ℝ => gaussianPDF (r*p.1) v p.2) := by
      unfold gaussianPDF gaussianPDFReal
      fun_prop
    exact hg.mul hf
  change (∫⁻ x, F (a*x) ∂gaussianReal 0 1)=_
  have hm := standardNormal_affine_map 0 a
  simp only [zero_add] at hm
  rw [← lintegral_map hF (by fun_prop),hm,gaussianReal_of_var_ne_zero _ hw,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hF,
    lintegral_withDensity_eq_lintegral_mul _ hd hf]
  rw [Measure.volume_eq_prod,lintegral_prod _ (hd.mul hf).aemeasurable]
  apply lintegral_congr
  intro x
  dsimp only [Pi.mul_apply,F]
  rw [← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr
  intro y
  exact (mul_assoc _ _ _).symm

theorem gaussian_scaled_pair_density {r : ℝ} (hr : r∈Ioo (-1) 1) (a : ℝ) (ha : a≠0) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).map
      (fun x => (a*x 0,a*x 1))=
      (volume : Measure (ℝ×ℝ)).withDensity
        (fun p => gaussianPDF 0 (NNReal.mk (a^2) (sq_nonneg a)) p.1*
          gaussianPDF (r*p.1) (NNReal.mk ((a*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.2) := by
  rw [← map_gaussianRealPair ⟨hr.1.le,hr.2.le⟩,Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : EuclideanSpace ℝ (Fin 2) => (a*x 0,a*x 1)) ∘ gaussianRealPair r=
      fun p : ℝ×ℝ => (a*p.1,r*(a*p.1)+(a*Real.sqrt (1-r^2))*p.2) := by
    funext p
    change (a*p.1,a*(r*p.1+Real.sqrt (1-r^2)*p.2))=_
    congr 1
    ring
  rw [he]
  exact standardNormal_scaled_joint_density r a (a*Real.sqrt (1-r^2)) ha
    (mul_ne_zero ha (Real.sqrt_ne_zero'.mpr (by nlinarith [hr.1,hr.2])))

end Verification
