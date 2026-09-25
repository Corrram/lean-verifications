import Verification.ClaytonScaledTail
import Verification.PowerRootLimit
import Copula.Reflection.Bivariate

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem survivalClayton_linear_limit {ι : Type*} {l : Filter ι}
    (δ : ℝ) (hδ : 0<δ) (c : ι→ℝ) (hc : ∀ i,0<c i) (hctop : Tendsto c l atTop)
    (u v : I) (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    Tendsto (fun i => c i*((clayton 2 δ hδ).survivalCopula.cdf
      ![unitPower u ((c i)⁻¹) (le_of_lt (inv_pos.mpr (hc i))),unitPower v ((c i)⁻¹) (le_of_lt (inv_pos.mpr (hc i)))]-1))
      l (nhds (Real.log (u:ℝ)+Real.log (v:ℝ)+
        galambosTailKernel δ (-Real.log (u:ℝ)) (-Real.log (v:ℝ)))) := by
  let U := fun i => unitInterval.symm (unitPower u ((c i)⁻¹) (le_of_lt (inv_pos.mpr (hc i))))
  let V := fun i => unitInterval.symm (unitPower v ((c i)⁻¹) (le_of_lt (inv_pos.mpr (hc i))))
  have hU : ∀ i,0<(U i:ℝ) := by
    intro i
    change 0<1-(u:ℝ)^((c i)⁻¹)
    exact sub_pos.mpr (Real.rpow_lt_one u.property.1 hu.2 (inv_pos.mpr (hc i)))
  have hV : ∀ i,0<(V i:ℝ) := by
    intro i
    change 0<1-(v:ℝ)^((c i)⁻¹)
    exact sub_pos.mpr (Real.rpow_lt_one v.property.1 hv.2 (inv_pos.mpr (hc i)))
  have hux : Tendsto (fun i => c i*(U i:ℝ)) l (nhds (-Real.log (u:ℝ))) :=
    (power_root_gap_limit hu.1).comp hctop
  have hvy : Tendsto (fun i => c i*(V i:ℝ)) l (nhds (-Real.log (v:ℝ))) :=
    (power_root_gap_limit hv.1).comp hctop
  have htail := clayton_scaled_cdf_limit δ hδ c hc hctop U V hU hV
    (neg_pos.mpr (Real.log_neg hu.1 hu.2)) (neg_pos.mpr (Real.log_neg hv.1 hv.2)) hux hvy
  have h := (hux.neg.add hvy.neg).add htail
  simp only [neg_neg] at h
  convert h using 1
  funext i
  rw [cdf_survivalCopula]
  change c i*((u:ℝ)^((c i)⁻¹)+(v:ℝ)^((c i)⁻¹)-1+
      (clayton 2 δ hδ).cdf ![U i,V i]-1)=
    -(c i*(1-(u:ℝ)^((c i)⁻¹)))+ -(c i*(1-(v:ℝ)^((c i)⁻¹)))+
      c i*(clayton 2 δ hδ).cdf ![U i,V i]
  ring

end Verification
