import Verification.ContinuousDensityMinors

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace Verification

theorem real_continuous_density_minor_of_ae (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (ha : ∀ᵐ a : ℝ, ∀ᵐ b : ℝ, ∀ᵐ c : ℝ, ∀ᵐ d : ℝ,
      a≤b → c≤d → 0≤f (a,c)*f (b,d)-f (a,d)*f (b,c))
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hac : ContinuousAt f (a,c)) (had : ContinuousAt f (a,d))
    (hbc : ContinuousAt f (b,c)) (hbd : ContinuousAt f (b,d)) :
    f (a,d)*f (b,c) ≤ f (a,c)*f (b,d) := by
  let M : (ℝ × (ℝ × (ℝ × ℝ))) → ℝ := fun x =>
    f (x.1,x.2.2.1)*f (x.2.1,x.2.2.2)-f (x.1,x.2.2.2)*f (x.2.1,x.2.2.1)
  have hm : Measurable M := by dsimp [M]; fun_prop
  have hae : ∀ᵐ x : ℝ × (ℝ × (ℝ × ℝ)),
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
    simpa only [M] using hd
  have hc : ContinuousAt M (a,b,c,d) := by
    have h₁ := hac.comp (f := fun x : ℝ × (ℝ × (ℝ × ℝ)) => (x.1,x.2.2.1)) (x := (a,b,c,d)) (by fun_prop)
    have h₂ := hbd.comp (f := fun x : ℝ × (ℝ × (ℝ × ℝ)) => (x.2.1,x.2.2.2)) (x := (a,b,c,d)) (by fun_prop)
    have h₃ := had.comp (f := fun x : ℝ × (ℝ × (ℝ × ℝ)) => (x.1,x.2.2.2)) (x := (a,b,c,d)) (by fun_prop)
    have h₄ := hbc.comp (f := fun x : ℝ × (ℝ × (ℝ × ℝ)) => (x.2.1,x.2.2.1)) (x := (a,b,c,d)) (by fun_prop)
    exact (h₁.mul h₂).sub (h₃.mul h₄)
  have hs : {x : ℝ × (ℝ × (ℝ × ℝ)) | x.1 < x.2.1 ∧ x.2.2.1 < x.2.2.2} ∈ 𝓝 (a,b,c,d) := by
    exact inter_mem ((isOpen_lt (f := fun x : ℝ × (ℝ × (ℝ × ℝ)) => x.1) (g := fun x => x.2.1) (by fun_prop) (by fun_prop)).mem_nhds hab)
      ((isOpen_lt (f := fun x : ℝ × (ℝ × (ℝ × ℝ)) => x.2.2.1) (g := fun x => x.2.2.2) (by fun_prop) (by fun_prop)).mem_nhds hcd)
  let : (volume : Measure (ℝ × ℝ)).IsOpenPosMeasure := inferInstance
  let : (volume : Measure (ℝ × (ℝ × ℝ))).IsOpenPosMeasure := inferInstance
  have hn := continuousAt_nonneg_of_ae_imp (X := ℝ × (ℝ × (ℝ × ℝ))) (μ := (volume : Measure (ℝ × (ℝ × (ℝ × ℝ)))))
    hc hs (hae.mono (fun x hx h => hx h.1.le h.2.le))
  exact sub_nonneg.mp hn

theorem real_density_minor_of_tp2_ae (f g : ℝ×ℝ→ℝ) (hf : Measurable f)
    (hg : Measurable g) (he : f=ᵐ[volume] g)
    (htp : ∀ a b c d : ℝ, a≤b → c≤d → g (a,d)*g (b,c)≤g (a,c)*g (b,d))
    (a b c d : ℝ) (hab : a<b) (hcd : c<d)
    (hac : ContinuousAt f (a,c)) (had : ContinuousAt f (a,d))
    (hbc : ContinuousAt f (b,c)) (hbd : ContinuousAt f (b,d)) :
    f (a,d)*f (b,c)≤f (a,c)*f (b,d) := by
  have he' : ∀ᵐ x : ℝ, ∀ᵐ y : ℝ, f (x,y)=g (x,y) := by
    rw [Measure.volume_eq_prod] at he
    exact (Measure.ae_prod_iff_ae_ae (by measurability)).mp he
  apply real_continuous_density_minor_of_ae f hf _ a b c d hab hcd hac had hbc hbd
  filter_upwards [he'] with x hx
  filter_upwards [he'] with y hy
  filter_upwards [hx,hy] with u hxu hyu
  filter_upwards [hx,hy] with v hxv hyv
  intro hxy huv
  rw [hxu,hyv,hxv,hyu]
  exact sub_nonneg.mpr (htp x y u v hxy huv)

end Verification
