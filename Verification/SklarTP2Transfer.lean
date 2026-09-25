import Verification.ScaleMixtureAbsoluteContinuity
import Copula.Dependence.TotalPositivity

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval ENNReal

namespace Verification

theorem sklar_map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {F : X→Y} (hF : Measurable F) {h : Y→ℝ≥0∞} (hh : Measurable h) :
    (μ.withDensity (fun x => h (F x))).map F=(μ.map F).withDensity h := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun x => h (F x)) := hh.comp hF
  have hfm : Measurable (fun x => f (F x)) := hf.comp hF
  rw [lintegral_map hf hF,lintegral_withDensity_eq_lintegral_mul _ hm hfm,
    lintegral_withDensity_eq_lintegral_mul _ hh hf,lintegral_map (hh.mul hf) hF]
  rfl

theorem joint_tp2_density_of_copula (J : Measure (ℝ×ℝ)) (M : Measure ℝ)
    (m : ℝ→ℝ) (hm : Measurable m) (hn : ∀ x,0≤m x)
    (hM : M=volume.withDensity (fun x => ENNReal.ofReal (m x)))
    (F : ℝ→I) (hF : Measurable F) (hmono : Monotone F) (hinj : Function.Injective F)
    (C : Copula 2)
    (hprod : (M.prod M).map (fun p => ![F p.1,F p.2])=volume)
    (hC : C.toMeasure=J.map (fun p => ![F p.1,F p.2])) (hTP : C.HasMTP2Density) :
    ∃ g : ℝ×ℝ→ℝ, Measurable g ∧ (∀ p,0≤g p) ∧
      (∀ a b c d : ℝ, a≤b → c≤d → g (a,d)*g (b,c)≤g (a,c)*g (b,d)) ∧
      J=volume.withDensity (fun p => ENNReal.ofReal (g p)) := by
  obtain ⟨c,hc,hcn,hct,hcd⟩ := hTP
  let Φ : ℝ×ℝ→(Fin 2→I) := fun p => ![F p.1,F p.2]
  have hΦ : Measurable Φ := by fun_prop
  have hΦinj : Function.Injective Φ := by
    intro p q he
    exact Prod.ext (hinj (congrFun he 0)) (hinj (congrFun he 1))
  have hJ : J=(M.prod M).withDensity (fun p => ENNReal.ofReal (c (Φ p))) := by
    apply (hΦ.measurableEmbedding hΦinj).map_injective
    rw [sklar_map_withDensity_comp _ hΦ hc.ennreal_ofReal,hprod,← hcd,← hC]
  let g : ℝ×ℝ→ℝ := fun p => m p.1*m p.2*c (Φ p)
  refine ⟨g,by fun_prop,fun p => mul_nonneg (mul_nonneg (hn _) (hn _)) (hcn _),?_,?_⟩
  · intro a b u v hab huv
    have ht := (isMTP2_fin_two_iff c).mp hct (F a) (F b) (F u) (F v) (hmono hab) (hmono huv)
    have hh := mul_le_mul_of_nonneg_left ht
      (show 0≤m a*m b*m u*m v from mul_nonneg (mul_nonneg (mul_nonneg (hn _) (hn _)) (hn _)) (hn _))
    dsimp only [g,Φ]
    nlinarith only [hh]
  · rw [hJ,hM,prod_withDensity hm.ennreal_ofReal hm.ennreal_ofReal,← Measure.volume_eq_prod]
    have hw : Measurable (fun p : ℝ×ℝ => ENNReal.ofReal (m p.1)*ENNReal.ofReal (m p.2)) := by fun_prop
    have hv : Measurable (fun p => ENNReal.ofReal (c (Φ p))) := hc.ennreal_ofReal.comp hΦ
    rw [← withDensity_mul _ hw hv]
    congr 1
    funext p
    change ENNReal.ofReal (m p.1)*ENNReal.ofReal (m p.2)*ENNReal.ofReal (c (Φ p))=ENNReal.ofReal (g p)
    rw [← ENNReal.ofReal_mul (hn _),← ENNReal.ofReal_mul (mul_nonneg (hn _) (hn _))]

end Verification
