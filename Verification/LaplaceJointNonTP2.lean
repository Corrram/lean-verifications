import Verification.LaplaceTP2Witness
import Verification.RealDensityMinors

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped ENNReal

namespace Verification

theorem laplace_joint_density_ne_top {r : ℝ} (hr : r∈Ioo (-1) 1)
    {p : ℝ×ℝ} (hp : p≠(0,0)) :
    gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt p≠∞ := by
  rw [laplace_joint_density_evaluation hr]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (laplaceRadialDensity_ne_top (studentQuadratic_pos hr hp))

theorem laplace_joint_real_density_continuousAt {r : ℝ} (hr : r∈Ioo (-1) 1)
    {p : ℝ×ℝ} (hp : p≠(0,0)) :
    ContinuousAt (fun z => (gaussianScaleMixtureJointDensity r
      (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt z).toReal) p := by
  apply (ENNReal.continuousAt_toReal (laplace_joint_density_ne_top hr hp)).comp
  have he : gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt=
      fun z => ENNReal.ofReal ((2*Real.pi*Real.sqrt (1-r^2))⁻¹)*laplaceRadialDensity (studentQuadratic r z) :=
    funext (laplace_joint_density_evaluation hr)
  rw [he]
  apply (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).continuousAt.comp
  exact (laplaceRadialDensity_continuousAt (studentQuadratic_pos hr hp)).comp
    (show Continuous (studentQuadratic r) by unfold studentQuadratic; fun_prop).continuousAt

/-- No nonnegative measurable TP2 density represents the actual Laplace joint law. -/
theorem laplace_joint_no_tp2_density {r : ℝ} (hr : r∈Ioo (-1) 1) :
    ¬∃ g : ℝ×ℝ→ℝ, Measurable g ∧ (∀ p,0≤g p) ∧
      (∀ a b c d : ℝ, a≤b → c≤d → g (a,d)*g (b,c)≤g (a,c)*g (b,d)) ∧
      (gaussianScaleMixtureLaw (bivariateCorrelation r)
        (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt).toMeasure.map
          MeasurableEquiv.finTwoArrow=volume.withDensity (fun p => ENNReal.ofReal (g p)) := by
  rintro ⟨g,hg,hn,htp,hd⟩
  let D := gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt
  have hD : Measurable D := measurable_gaussianScaleMixtureJointDensity _ _ _ (by fun_prop)
  have he : D=ᵐ[volume] fun p => ENNReal.ofReal (g p) := by
    apply (withDensity_eq_iff_of_sigmaFinite hD.aemeasurable hg.ennreal_ofReal.aemeasurable).mp
    rw [← hd]
    exact (gaussianScaleMixtureLaw_joint_withDensity hr _ _ (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure 1 1] with t ht
      exact Real.sqrt_pos.mpr ht)).symm
  have her : (fun p => (D p).toReal)=ᵐ[volume] g := by
    filter_upwards [he] with p hp
    rw [hp,ENNReal.toReal_ofReal (hn p)]
  obtain ⟨t,ht,_,hlt⟩ := laplace_joint_density_tp2_witness hr
  have hpoint {x : ℝ} (hx : x≠0) (y : ℝ) : (x,y)≠(0,0) := by
    intro h
    exact hx (congrArg Prod.fst h)
  have hfin {x : ℝ} (hx : x≠0) (y : ℝ) : D (x,y)≠∞ :=
    laplace_joint_density_ne_top hr (hpoint hx y)
  have hcont {x : ℝ} (hx : x≠0) (y : ℝ) : ContinuousAt (fun p => (D p).toReal) (x,y) :=
    laplace_joint_real_density_continuousAt hr (hpoint hx y)
  have hminor := real_density_minor_of_tp2_ae (fun p => (D p).toReal) g
    hD.ennreal_toReal hg her htp (-1) t 0 1 (by linarith) (by norm_num)
    (hcont (by norm_num) 0) (hcont (by norm_num) 1) (hcont ht.ne' 0) (hcont ht.ne' 1)
  have hstrict := (ENNReal.toReal_lt_toReal
    (ENNReal.mul_ne_top (hfin (by norm_num) 0) (hfin ht.ne' 1))
    (ENNReal.mul_ne_top (hfin (by norm_num) 1) (hfin ht.ne' 0))).mpr hlt
  simp only [ENNReal.toReal_mul] at hstrict
  exact (not_lt.mpr hminor) hstrict

end Verification
