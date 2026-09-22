import Verification.DensityRectangles
import Copula.Dependence.ConditionalMonotonicity
import Copula.OrdinalSum.Basic

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal

namespace Verification

theorem mtp2_ordered_rectangles {C : Copula 2} (hC : C.HasMTP2Density)
    (S T U V : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hST : ∀ a ∈ S, ∀ b ∈ T, a ≤ b) (hUV : ∀ u ∈ U, ∀ v ∈ V, u ≤ v) :
    C.toMeasure.real {x | x 0 ∈ S ∧ x 1 ∈ V} * C.toMeasure.real {x | x 0 ∈ T ∧ x 1 ∈ U} ≤
      C.toMeasure.real {x | x 0 ∈ S ∧ x 1 ∈ U} * C.toMeasure.real {x | x 0 ∈ T ∧ x 1 ∈ V} := by
  obtain ⟨f,hf,hn,htp,hd⟩ := hC
  have hm : Measurable (fun p : I × I => ENNReal.ofReal (f ![p.1,p.2])) :=
    hf.ennreal_ofReal.comp (by fun_prop)
  have he := tp2_rectangle_integrals (fun a b => ENNReal.ofReal (f ![a,b])) hm
    S T U V hS hT hU hV (by
      intro a ha b hb u hu v hv
      rw [← ENNReal.ofReal_mul (hn ![b,u]),← ENNReal.ofReal_mul (hn ![a,u])]
      apply ENNReal.ofReal_le_ofReal
      have ht := (Copula.isMTP2_fin_two_iff f).mp htp a b u v (hST a ha b hb) (hUV u hu v hv)
      simpa only [mul_comm] using ht)
  rw [← density_rectangle_integral C f hf hd S V hS hV,
    ← density_rectangle_integral C f hf hd T U hT hU,
    ← density_rectangle_integral C f hf hd S U hS hU,
    ← density_rectangle_integral C f hf hd T V hT hV] at he
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) he
  simpa only [ENNReal.toReal_mul,Measure.real] using hr

theorem mtp2_isSI {C : Copula 2} (hC : C.HasMTP2Density) : C.IsSI := by
  intro a b c v hab hbc
  have he := mtp2_ordered_rectangles hC (Ioc a b) (Ioc b c) (Ioc 0 v) (Ioc v 1)
    measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc
    (fun x hx y hy => hx.2.trans hy.1.le) (fun x hx y hy => hx.2.trans hy.1.le)
  rw [measureReal_coordinate_rectangle C a b v 1 hab v.property.2,
    measureReal_coordinate_rectangle C b c 0 v hbc v.property.1,
    measureReal_coordinate_rectangle C a b 0 v hab v.property.1,
    measureReal_coordinate_rectangle C b c v 1 hbc v.property.2] at he
  simp only [Copula.cdf_two_one_right,Copula.cdf_two_zero_right,sub_zero,add_zero] at he
  nlinarith

theorem mtp2_isCI {C : Copula 2} (hC : C.HasMTP2Density) : C.IsCI := by
  refine ⟨mtp2_isSI hC,?_⟩
  intro a b c v hab hbc
  have he := mtp2_ordered_rectangles hC (Ioc 0 v) (Ioc v 1) (Ioc a b) (Ioc b c)
    measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc
    (fun x hx y hy => hx.2.trans hy.1.le) (fun x hx y hy => hx.2.trans hy.1.le)
  rw [measureReal_coordinate_rectangle C 0 v b c v.property.1 hbc,
    measureReal_coordinate_rectangle C v 1 a b v.property.2 hab,
    measureReal_coordinate_rectangle C 0 v a b v.property.1 hab,
    measureReal_coordinate_rectangle C v 1 b c v.property.2 hbc] at he
  simp only [Copula.cdf_two_one_left,Copula.cdf_two_zero_left,sub_zero,add_zero] at he
  simp only [Copula.cdf_transpose]
  nlinarith

end Verification
