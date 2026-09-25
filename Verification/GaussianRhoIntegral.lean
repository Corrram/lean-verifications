import Verification.GaussianRhoNoise
import Verification.ProductRegroup

open ProbabilityTheory MeasureTheory Set

namespace Verification

theorem gaussian_normalCDF_product_integral {r : ℝ} (hr : r∈Icc (-1) 1)
    (a b c : ℝ) (hb : 0<b) (hc : 0<c) :
    (∫ p : ℝ×ℝ, ProbabilityTheory.cdf (gaussianReal 0 1) (a*p.1/b)*
      ProbabilityTheory.cdf (gaussianReal 0 1) (a*(r*p.1+Real.sqrt (1-r^2)*p.2)/c)
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1))=
      1/4+Real.arcsin (r*a^2/(Real.sqrt (a^2+b^2)*Real.sqrt (a^2+c^2)))/(2*Real.pi) := by
  let μ := gaussianReal 0 1
  let P := μ.prod μ
  let S := {p : (ℝ×ℝ)×(ℝ×ℝ) |
    b*p.2.1≤a*p.1.1 ∧ c*p.2.2≤a*(r*p.1.1+Real.sqrt (1-r^2)*p.1.2)}
  have hS : MeasurableSet S := by
    have h1 : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => b*p.2.1) := by fun_prop
    have h2 : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => a*p.1.1) := by fun_prop
    have h3 : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => c*p.2.2) := by fun_prop
    have h4 : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => a*(r*p.1.1+Real.sqrt (1-r^2)*p.1.2)) := by fun_prop
    exact (measurableSet_le h1 h2).inter (measurableSet_le h3 h4)
  have hm := congrArg ENNReal.toReal
    ((measurePreserving_product_regroup μ μ).measure_preimage hS.nullMeasurableSet)
  change (P.prod P).real
      {p | b*p.1.2≤a*p.1.1 ∧ c*p.2.2≤a*(r*p.1.1+Real.sqrt (1-r^2)*p.2.1)}=
    (P.prod P).real S at hm
  have hg := gaussian_scaled_independent_comparison_arcsin hr a b c
    (by nlinarith [sq_nonneg a,sq_pos_of_pos hb]) (by nlinarith [sq_nonneg a,sq_pos_of_pos hc])
  change (P.prod P).real _=_ at hg
  rw [hm] at hg
  rw [← hg,← integral_indicator_one hS]
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) (P.prod P) :=
    (integrable_const _).indicator hS
  change _=(∫ p, S.indicator (fun _ => (1:ℝ)) p ∂P.prod P)
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    let T := Iic (a*p.1/b) ×ˢ Iic (a*(r*p.1+Real.sqrt (1-r^2)*p.2)/c)
    have hT : MeasurableSet T := measurableSet_Iic.prod measurableSet_Iic
    have he : (fun q : ℝ×ℝ => S.indicator (fun _ => (1:ℝ)) (p,q))=T.indicator (fun _ => (1:ℝ)) := by
      funext q
      have hmem : (p,q)∈S ↔ q∈T := by
        simp only [S,T,mem_ofPred_eq,mem_prod,mem_Iic]
        rw [le_div_iff₀ hb,le_div_iff₀ hc]
        simp only [mul_comm]
      simp only [indicator,hmem]
    dsimp only
    rw [he]
    have hint := integral_indicator_one (μ := P) hT
    change _=(∫ q, T.indicator (fun _ => (1:ℝ)) q ∂P)
    change (∫ q, T.indicator (fun _ => (1:ℝ)) q ∂P)=P.real T at hint
    rw [hint]
    simp only [T,P,Measure.real,Measure.prod_prod,ENNReal.toReal_mul,
      ProbabilityTheory.cdf_eq_real,μ]

noncomputable def gaussianRealPair (r : ℝ) : (ℝ×ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℝ ℝ ℝ,
      r • ContinuousLinearMap.fst ℝ ℝ ℝ+Real.sqrt (1-r^2) • ContinuousLinearMap.snd ℝ ℝ ℝ])

theorem map_gaussianRealPair {r : ℝ} (hr : r∈Icc (-1) 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (gaussianRealPair r)=
      multivariateGaussian 0 (bivariateCorrelation r) := by
  have hs : 0≤1-r^2 := by nlinarith [hr.1,hr.2]
  have hs' : ((Real.sqrt (1-r^2):ℝ):ℂ)^2=1-(r:ℂ)^2 := by
    exact_mod_cast Real.sq_sqrt hs
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_eq_charFunDual_toDualMap,charFunDual_map,charFunDual_prod,
    charFunDual_standardNormal,charFunDual_standardNormal,charFun_bivariateGaussian hr]
  simp [gaussianRealPair,PiLp.inner_apply,Fin.sum_univ_two]
  rw [← Complex.exp_add]
  congr 1
  ring_nf
  rw [hs']
  ring

theorem gaussian_cdf_product_integral {r : ℝ} (hr : r∈Icc (-1) 1)
    (a b c : ℝ) (hb : 0<b) (hc : 0<c) :
    (∫ x : EuclideanSpace ℝ (Fin 2), ProbabilityTheory.cdf (gaussianReal 0 1) (a*x 0/b)*
      ProbabilityTheory.cdf (gaussianReal 0 1) (a*x 1/c)
        ∂multivariateGaussian 0 (bivariateCorrelation r))=
      1/4+Real.arcsin (r*a^2/(Real.sqrt (a^2+b^2)*Real.sqrt (a^2+c^2)))/(2*Real.pi) := by
  have hf : Measurable (fun x : EuclideanSpace ℝ (Fin 2) =>
      ProbabilityTheory.cdf (gaussianReal 0 1) (a*x 0/b)*
        ProbabilityTheory.cdf (gaussianReal 0 1) (a*x 1/c)) :=
    ((monotone_cdf (gaussianReal 0 1)).measurable.comp (by fun_prop)).mul
      ((monotone_cdf (gaussianReal 0 1)).measurable.comp (by fun_prop))
  rw [← map_gaussianRealPair hr,integral_map (by fun_prop) hf.aestronglyMeasurable]
  exact gaussian_normalCDF_product_integral hr a b c hb hc

end Verification
