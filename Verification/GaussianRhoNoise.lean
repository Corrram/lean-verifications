import Verification.GaussianTau
import Verification.GaussianXiProbability

open ProbabilityTheory MeasureTheory Set

namespace Verification

noncomputable def gaussianRhoNoise (r a b c d : ℝ) :
    ((ℝ×ℝ)×(ℝ×ℝ)) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  let x := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) (ℝ×ℝ))
  let y := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ×ℝ) (ℝ×ℝ))
  let z := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ×ℝ) (ℝ×ℝ))
  let w := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ×ℝ) (ℝ×ℝ))
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![a • x+b • y,c • (r • x+Real.sqrt (1-r^2) • z)+d • w])

theorem map_gaussianRhoNoise {r a b c d : ℝ} (hr : r∈Icc (-1) 1)
    (hab : a^2+b^2=1) (hcd : c^2+d^2=1) :
    (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
      ((gaussianReal 0 1).prod (gaussianReal 0 1))).map (gaussianRhoNoise r a b c d)=
      multivariateGaussian 0 (bivariateCorrelation (r*a*c)) := by
  have hs : 0≤1-r^2 := by nlinarith [hr.1,hr.2]
  have ha : |a|≤1 := (abs_le).mpr ⟨by nlinarith [sq_nonneg b],by nlinarith [sq_nonneg b]⟩
  have hc : |c|≤1 := (abs_le).mpr ⟨by nlinarith [sq_nonneg d],by nlinarith [sq_nonneg d]⟩
  have hq : r*a*c∈Icc (-1) 1 := by
    apply abs_le.mp
    rw [abs_mul,abs_mul]
    have h := mul_le_mul (mul_le_mul (abs_le.mpr hr) ha (abs_nonneg a) (by norm_num))
      hc (abs_nonneg c) (by norm_num)
    simpa using h
  have hs' : ((Real.sqrt (1-r^2):ℝ):ℂ)^2=1-(r:ℂ)^2 := by
    exact_mod_cast Real.sq_sqrt hs
  have hab' : (a:ℂ)^2+(b:ℂ)^2=1 := by exact_mod_cast hab
  have hcd' : (c:ℂ)^2+(d:ℂ)^2=1 := by exact_mod_cast hcd
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_eq_charFunDual_toDualMap,charFunDual_map,charFunDual_prod,
    charFunDual_prod,charFunDual_prod,
    charFunDual_standardNormal,charFunDual_standardNormal,
    charFunDual_standardNormal,charFunDual_standardNormal,
    charFun_bivariateGaussian hq]
  simp [gaussianRhoNoise,PiLp.inner_apply,Fin.sum_univ_two]
  simp only [← Complex.exp_add]
  congr 1
  have hb : (b:ℂ)^2=1-(a:ℂ)^2 := by linear_combination hab'
  have hd : (d:ℂ)^2=1-(c:ℂ)^2 := by linear_combination hcd'
  ring_nf
  rw [hs',hb,hd]
  ring

noncomputable def gaussianRhoScaledNoise (r a b c : ℝ) :
    ((ℝ×ℝ)×(ℝ×ℝ)) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  gaussianRhoNoise r (-a/Real.sqrt (a^2+b^2)) (b/Real.sqrt (a^2+b^2))
    (-a/Real.sqrt (a^2+c^2)) (c/Real.sqrt (a^2+c^2))

theorem map_gaussianRhoScaledNoise {r : ℝ} (hr : r∈Icc (-1) 1) (a b c : ℝ)
    (hab : 0<a^2+b^2) (hac : 0<a^2+c^2) :
    (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
      ((gaussianReal 0 1).prod (gaussianReal 0 1))).map (gaussianRhoScaledNoise r a b c)=
      multivariateGaussian 0
        (bivariateCorrelation (r*a^2/(Real.sqrt (a^2+b^2)*Real.sqrt (a^2+c^2)))) := by
  have hn (v : ℝ) (hv : 0<a^2+v^2) :
      (-a/Real.sqrt (a^2+v^2))^2+(v/Real.sqrt (a^2+v^2))^2=1 := by
    rw [div_pow,div_pow,neg_sq,Real.sq_sqrt hv.le,← add_div,div_self hv.ne']
  have h := map_gaussianRhoNoise hr (hn b hab) (hn c hac)
  have he : r*(-a/Real.sqrt (a^2+b^2))*(-a/Real.sqrt (a^2+c^2))=
      r*a^2/(Real.sqrt (a^2+b^2)*Real.sqrt (a^2+c^2)) := by ring
  simpa only [gaussianRhoScaledNoise,he] using h

theorem gaussian_scaled_independent_comparison {r : ℝ} (hr : r∈Icc (-1) 1) (a b c : ℝ)
    (hab : 0<a^2+b^2) (hac : 0<a^2+c^2) :
    (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
      ((gaussianReal 0 1).prod (gaussianReal 0 1))).real
        {p | b*p.1.2≤a*p.1.1 ∧ c*p.2.2≤a*(r*p.1.1+Real.sqrt (1-r^2)*p.2.1)}=
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        (bivariateCorrelation (r*a^2/(Real.sqrt (a^2+b^2)*Real.sqrt (a^2+c^2))))).real
          {x | x 0≤0 ∧ x 1≤0} := by
  have hQ : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) | x 0≤0 ∧ x 1≤0} := by
    exact (measurableSet_le (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 0) by fun_prop)
      measurable_const).inter
      (measurableSet_le (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 1) by fun_prop)
        measurable_const)
  have he : (gaussianRhoScaledNoise r a b c) ⁻¹' {x | x 0≤0 ∧ x 1≤0}=
      {p : (ℝ×ℝ)×(ℝ×ℝ) |
        b*p.1.2≤a*p.1.1 ∧ c*p.2.2≤a*(r*p.1.1+Real.sqrt (1-r^2)*p.2.1)} := by
    ext p
    have hdiv (v x y : ℝ) : (-a/Real.sqrt (a^2+v^2))*x+(v/Real.sqrt (a^2+v^2))*y=
        (v*y-a*x)/Real.sqrt (a^2+v^2) := by ring
    simp only [Set.mem_preimage,Set.mem_ofPred_eq]
    change ((-a/Real.sqrt (a^2+b^2))*p.1.1+(b/Real.sqrt (a^2+b^2))*p.1.2≤0 ∧
      (-a/Real.sqrt (a^2+c^2))*(r*p.1.1+Real.sqrt (1-r^2)*p.2.1)+
        (c/Real.sqrt (a^2+c^2))*p.2.2≤0) ↔ _
    simp only [hdiv,div_le_iff₀ (Real.sqrt_pos.mpr hab),div_le_iff₀ (Real.sqrt_pos.mpr hac),
      zero_mul,sub_nonpos]
  rw [← he,← map_measureReal_apply (by fun_prop) hQ,map_gaussianRhoScaledNoise hr a b c hab hac]

theorem scaledGaussianRhoCorrelation_mem {r : ℝ} (hr : r∈Icc (-1) 1) (a b c : ℝ)
    (hab : 0<a^2+b^2) (hac : 0<a^2+c^2) :
    r*a^2/(Real.sqrt (a^2+b^2)*Real.sqrt (a^2+c^2))∈Icc (-1) 1 := by
  have hd := mul_pos (Real.sqrt_pos.mpr hab) (Real.sqrt_pos.mpr hac)
  have hsq : (Real.sqrt (a^2+b^2)*Real.sqrt (a^2+c^2))^2=
      (a^2+b^2)*(a^2+c^2) := by
    rw [mul_pow,Real.sq_sqrt hab.le,Real.sq_sqrt hac.le]
  have hle : a^2≤Real.sqrt (a^2+b^2)*Real.sqrt (a^2+c^2) := by
    nlinarith [sq_nonneg a,mul_nonneg (sq_nonneg a) (sq_nonneg b),
      mul_nonneg (sq_nonneg a) (sq_nonneg c),mul_nonneg (sq_nonneg b) (sq_nonneg c)]
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0≤r+1 by linarith [hr.1]) (sq_nonneg a)]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0≤1-r by linarith [hr.2]) (sq_nonneg a)]

theorem gaussian_scaled_independent_comparison_arcsin {r : ℝ} (hr : r∈Icc (-1) 1) (a b c : ℝ)
    (hab : 0<a^2+b^2) (hac : 0<a^2+c^2) :
    (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
      ((gaussianReal 0 1).prod (gaussianReal 0 1))).real
        {p | b*p.1.2≤a*p.1.1 ∧ c*p.2.2≤a*(r*p.1.1+Real.sqrt (1-r^2)*p.2.1)}=
      1/4+Real.arcsin (r*a^2/(Real.sqrt (a^2+b^2)*Real.sqrt (a^2+c^2)))/(2*Real.pi) := by
  rw [gaussian_scaled_independent_comparison hr a b c hab hac]
  have hq := scaledGaussianRhoCorrelation_mem hr a b c hab hac
  have h := gaussianBivariate_kendallTau hq
  rw [gaussianBivariate_tau_quadrant hq] at h
  have he : (2/Real.pi*Real.arcsin (r*a^2/(Real.sqrt (a^2+b^2)*Real.sqrt (a^2+c^2)))+1)/4=
      1/4+Real.arcsin (r*a^2/(Real.sqrt (a^2+b^2)*Real.sqrt (a^2+c^2)))/(2*Real.pi) := by ring
  rw [← he]
  linarith

end Verification
