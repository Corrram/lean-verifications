import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace Verification

theorem measurePreserving_product_regroup {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] :
    MeasurePreserving (fun p : (α×β)×(α×β) => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μ.prod ν).prod (μ.prod ν)) ((μ.prod μ).prod (ν.prod ν)) := by
  have h1 := measurePreserving_prodAssoc μ ν (μ.prod ν)
  have h2 := (MeasurePreserving.id μ).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc ν μ ν))
  have h3 := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).prod (MeasurePreserving.id ν))
  have h4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc μ ν ν)
  have h5 := MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μ μ (ν.prod ν))
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

end Verification
