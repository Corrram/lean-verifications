import Verification.AETotalPositivity
import Copula.UnitInterval
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval Topology

namespace Verification

theorem continuousAt_nonneg_of_ae_imp {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {f : X → ℝ} {x : X} {s : Set X}
    (hf : ContinuousAt f x) (hs : s ∈ 𝓝 x) (ha : ∀ᵐ y ∂μ, y ∈ s → 0 ≤ f y) : 0 ≤ f x := by
  by_contra hn
  have hn' : f x < 0 := lt_of_not_ge hn
  have he : {y | y ∈ s ∧ f y < 0} ∈ 𝓝 x :=
    inter_mem hs (hf (Iio_mem_nhds hn'))
  have hp := μ.measure_pos_of_mem_nhds he
  have hz : μ {y | y ∈ s ∧ f y < 0} = 0 := by
    have hh : ∀ᵐ y ∂μ, ¬(y ∈ s ∧ f y < 0) := by
      filter_upwards [ha] with y hy
      exact fun h => (not_lt.mpr (hy h.1)) h.2
    simpa only [not_not] using ae_iff.mp hh
  exact hp.ne' hz

theorem continuous_density_minor_of_ae (f : I × I → ℝ) (hf : Measurable f)
    (ha : HasAEOrderedMinors 1 (fun u v => f (u,v)))
    (a b c d : I) (hab : a < b) (hcd : c < d)
    (hac : ContinuousAt f (a,c)) (had : ContinuousAt f (a,d))
    (hbc : ContinuousAt f (b,c)) (hbd : ContinuousAt f (b,d)) :
    f (a,d)*f (b,c) ≤ f (a,c)*f (b,d) := by
  let M : (I × (I × (I × I))) → ℝ := fun x =>
    f (x.1,x.2.2.1)*f (x.2.1,x.2.2.2)-f (x.1,x.2.2.2)*f (x.2.1,x.2.2.1)
  have hm : Measurable M := by dsimp [M]; fun_prop
  have hae : ∀ᵐ x : I × (I × (I × I)),
      x.1 ≤ x.2.1 → x.2.2.1 ≤ x.2.2.2 → 0 ≤ M x := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae (by dsimp [M]; measurability)).mpr
    filter_upwards [ha] with a ha
    rw [MeasureTheory.Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae (by dsimp [M]; measurability)).mpr
    filter_upwards [ha] with b hb
    rw [MeasureTheory.Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae (by dsimp [M]; measurability)).mpr
    filter_upwards [hb] with c hc
    filter_upwards [hc] with d hd
    simpa only [M, one_mul] using hd
  have hc : ContinuousAt M (a,b,c,d) := by
    have h₁ := hac.comp (f := fun x : I × (I × (I × I)) => (x.1,x.2.2.1)) (x := (a,b,c,d)) (by fun_prop)
    have h₂ := hbd.comp (f := fun x : I × (I × (I × I)) => (x.2.1,x.2.2.2)) (x := (a,b,c,d)) (by fun_prop)
    have h₃ := had.comp (f := fun x : I × (I × (I × I)) => (x.1,x.2.2.2)) (x := (a,b,c,d)) (by fun_prop)
    have h₄ := hbc.comp (f := fun x : I × (I × (I × I)) => (x.2.1,x.2.2.1)) (x := (a,b,c,d)) (by fun_prop)
    exact (h₁.mul h₂).sub (h₃.mul h₄)
  have hs : {x : I × (I × (I × I)) | x.1 < x.2.1 ∧ x.2.2.1 < x.2.2.2} ∈ 𝓝 (a,b,c,d) := by
    exact inter_mem ((isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds hab)
      ((isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds hcd)
  let : (volume : Measure (I × I)).IsOpenPosMeasure := inferInstance
  let : (volume : Measure (I × (I × I))).IsOpenPosMeasure := inferInstance
  have hn := continuousAt_nonneg_of_ae_imp (X := I × (I × (I × I))) (μ := (volume : Measure (I × (I × (I × I)))))
    hc hs (hae.mono (fun x hx h => hx h.1.le h.2.le))
  exact sub_nonneg.mp hn

/-- A continuous representative of a density inherits the ordered minors of any
TP2 density of the same copula, at every strict rectangle of continuity. -/
theorem copula_continuous_density_minor {C : Copula 2} (hC : C.HasMTP2Density)
    (f : (Fin 2 → I) → ℝ) (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (hd : C.toMeasure = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (a b c d : I) (hab : a < b) (hcd : c < d)
    (hac : ContinuousAt (fun p : I × I => f ![p.1,p.2]) (a,c))
    (had : ContinuousAt (fun p : I × I => f ![p.1,p.2]) (a,d))
    (hbc : ContinuousAt (fun p : I × I => f ![p.1,p.2]) (b,c))
    (hbd : ContinuousAt (fun p : I × I => f ![p.1,p.2]) (b,d)) :
    f ![a,d]*f ![b,c] ≤ f ![a,c]*f ![b,d] := by
  obtain ⟨g,hg,hgn,hgt,hgd⟩ := hC
  have he := density_ae_eq hg hf hgn hn (hgd.symm.trans hd)
  have ha := (aeOrderedMinors_of_tp2 ((Copula.isMTP2_fin_two_iff g).mp hgt)).congr
    (ae_curry_of_ae_eq he)
  exact continuous_density_minor_of_ae (fun p => f ![p.1,p.2])
    (hf.comp (by fun_prop)) ha a b c d hab hcd hac had hbc hbd

end Verification
