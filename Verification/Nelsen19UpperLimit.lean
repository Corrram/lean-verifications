import Verification.Nelsen19Tails

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem nelsen19_cdf_lower_bound {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    (min u v:ℝ)/(1+(min u v:ℝ)*Real.log 2/θ) ≤ (nelsen19 θ hθ.le).cdf ![u,v] := by
  let w : I := min u v
  change (w:ℝ)/(1+(w:ℝ)*Real.log 2/θ) ≤ _
  by_cases hw : w = 0
  · simp only [hw, show ((0:I):ℝ) = 0 from rfl,
      zero_mul, zero_div, add_zero, div_one]
    exact (nelsen19 θ hθ.le).cdf_nonneg _
  have hp : 0 < (w:ℝ) := lt_of_le_of_ne w.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hw))
  have hh := mul_le_mul_of_nonneg_left (nelsen19_lowerTail_bound hθ w hp) hp.le
  have hr : (w:ℝ)*(nelsen19 θ hθ.le).lowerTailRatio w = (nelsen19 θ hθ.le).diagonal w := by
    unfold lowerTailRatio
    field_simp
  rw [hr] at hh
  have he : (w:ℝ)/(1+(w:ℝ)*Real.log 2/θ) = (w:ℝ)*(θ/(θ+(w:ℝ)*Real.log 2)) := by
    field_simp
  rw [he]
  apply hh.trans
  apply (nelsen19 θ hθ.le).monotone_cdf
  intro i
  fin_cases i
  · exact min_le_left u v
  · exact min_le_right u v

theorem nelsen19_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 ≤ θ a) (ht : Tendsto θ l atTop) (u v : I) :
    Tendsto (fun a => (nelsen19 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((comonotonic 2).cdf ![u,v])) := by
  have hi : Tendsto (fun a => (min u v:ℝ)*Real.log 2/θ a) l (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop ht
  have hlo : Tendsto (fun a => (min u v:ℝ)/(1+(min u v:ℝ)*Real.log 2/θ a)) l
      (𝓝 (min u v:ℝ)) := by
    have hh : Tendsto (fun a => (min u v:ℝ)/(1+(min u v:ℝ)*Real.log 2/θ a)) l
        (𝓝 ((min u v:ℝ)/(1+0))) :=
      (tendsto_const_nhds (x := (min u v:ℝ))).div
        (tendsto_const_nhds.add hi) (by norm_num : (1:ℝ)+0 ≠ 0)
    simpa using hh
  have he : (comonotonic 2).cdf ![u,v] = (min u v:ℝ) := by
    rw [cdf_comonotonic_two]
    rfl
  rw [he]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [ht.eventually (eventually_gt_atTop (0:ℝ))] with a ha
    exact nelsen19_cdf_lower_bound ha u v
  · exact Eventually.of_forall fun a => le_min ((nelsen19 (θ a) (hθ a)).cdf_le_coord ![u,v] 0)
      ((nelsen19 (θ a) (hθ a)).cdf_le_coord ![u,v] 1)

end Verification
