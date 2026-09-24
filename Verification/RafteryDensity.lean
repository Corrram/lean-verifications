import Verification.RafteryAnalytic
import Verification.InteriorDensity

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem rafteryDensity_nonneg {a : ℝ} (ha : 1≤a) (u v : I) :
    0≤rafteryDensity a u v := by
  unfold rafteryDensity
  have ha0 : 0≤a := by linarith
  have hm : 0≤min (u:ℝ) v := le_min u.property.1 v.property.1
  have hM : 0≤max (u:ℝ) v := u.property.1.trans (le_max_left _ _)
  exact mul_nonneg (mul_nonneg (div_nonneg ha0 (by linarith)) (Real.rpow_nonneg hm _))
    (add_nonneg (mul_nonneg ha0 (Real.rpow_nonneg hM _))
      (mul_nonneg (sub_nonneg.mpr ha) (Real.rpow_nonneg hM _)))

theorem rafteryDensity_continuousAt {a u v : ℝ} (hu : 0<u) (hv : 0<v) :
    ContinuousAt (Function.uncurry (rafteryDensity a)) (u,v) := by
  have hm : ContinuousAt (fun p : ℝ × ℝ => min p.1 p.2) (u,v) := continuousAt_fst.min continuousAt_snd
  have hM : ContinuousAt (fun p : ℝ × ℝ => max p.1 p.2) (u,v) := continuousAt_fst.max continuousAt_snd
  have hmp : min u v≠0 := (lt_min hu hv).ne'
  have hMp : max u v≠0 := (hu.trans_le (le_max_left _ _)).ne'
  unfold Function.uncurry rafteryDensity
  exact ((hm.rpow_const (Or.inl hmp)).const_mul _).mul
    (((hM.rpow_const (Or.inl hMp)).const_mul a).add
      ((hM.rpow_const (Or.inl hMp)).const_mul (a-1)))

theorem rafteryF_eq_cdf {a : ℝ} (ha : 1<a) (u v : I) :
    rafteryF a u v = (rafteryPower a ha).cdf ![u,v] := by
  rw [rafteryPower_cdf_min]
  by_cases huv : (u:ℝ)≤v
  · simp only [rafteryF,huv,ite_true,min_eq_left huv,max_eq_right huv,rafteryL]
  · have hvu := le_of_not_ge huv
    simp only [rafteryF,huv,ite_false,min_eq_right hvu,max_eq_left hvu,rafteryL]

theorem rafteryPower_toMeasure_density {a : ℝ} (ha : 1<a) :
    (rafteryPower a ha).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (rafteryDensity a (x 0) (x 1))) := by
  apply copula_density_of_interior_derivatives (rafteryPower a ha)
    (rafteryDensity a) (rafteryF a) (rafteryP a)
  · exact rafteryDensity_nonneg ha.le
  · intro u v hu hv; exact rafteryDensity_continuousAt hu.1 hv.1
  · intro u v hu _; exact rafteryP_continuous_first ha hu.1
  · intro u v hu _; exact rafteryF_deriv_first ha hu.1
  · intro u v hu hv; exact rafteryP_deriv_second ha hu.1 hv.1
  · intro u v _ _ _ _; exact rafteryF_eq_cdf ha u v

theorem raftery_toMeasure_density (δ : I) (h1 : δ≠1) :
    (raftery δ).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (rafteryDensity (1/(1-(δ:ℝ))) (x 0) (x 1))) := by
  by_cases h0 : δ=0
  · subst δ
    norm_num [raftery_zero,toMeasure_independence,rafteryDensity]
    rfl
  · simp only [raftery,h0,h1,dite_false]
    exact rafteryPower_toMeasure_density (raftery_shape_gt_one δ h0 h1)

theorem raftery_absolutelyContinuous (δ : I) (h1 : δ≠1) :
    (raftery δ).toMeasure ≪ (volume : Measure (Fin 2 → I)) := by
  rw [raftery_toMeasure_density δ h1]
  exact withDensity_absolutelyContinuous _ _

end Verification
