import Verification.StableTailConstruction
import Verification.ExtremeValueConditional

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Verification

theorem stableTailCopula_isExtremeValue (L : StableTail) :
    (stableTailCopula L).IsExtremeValue := by
  intro u t ht
  by_cases hz : ∃ i,u i=0
  · obtain ⟨i,hi⟩ := hz
    have hp : unitPower (u i) t ht.le=0 := by ext; simp [hi,Real.zero_rpow ht.ne']
    rw [cdf_eq_zero_of_coord_eq_zero _ _ i hp,cdf_eq_zero_of_coord_eq_zero _ _ i hi,
      Real.zero_rpow ht.ne']
  have hp (i) : 0<(u i:ℝ) :=
    lt_of_le_of_ne (u i).property.1 (fun h => hz ⟨i,Subtype.ext h.symm⟩)
  have hn (i) : 0≤-Real.log (u i:ℝ) :=
    neg_nonneg.mpr (Real.log_nonpos (u i).property.1 (u i).property.2)
  have hu : u=![u 0,u 1] := by ext i; fin_cases i <;> rfl
  have he : (fun i => unitPower (u i) t ht.le)=![unitPower (u 0) t ht.le,unitPower (u 1) t ht.le] := by
    ext i; fin_cases i <;> rfl
  rw [he,stableTailCopula_cdf,stableTailCDF_positive_coords L _ _
    (Real.rpow_pos_of_pos (hp 0) _) (Real.rpow_pos_of_pos (hp 1) _)]
  conv_rhs => rw [hu,stableTailCopula_cdf,stableTailCDF_positive_coords L _ _ (hp 0) (hp 1)]
  simp only [coe_unitPower,Real.log_rpow (hp _),neg_mul_eq_mul_neg]
  rw [L.homogeneous (hn 0) (hn 1) ht.le,← Real.exp_mul]
  congr 1
  ring

theorem stableTailCopula_isCI (L : StableTail) : (stableTailCopula L).IsCI :=
  extremeValue_isCI _ (stableTailCopula_isExtremeValue L)

theorem stableTailCopula_pickands (L : StableTail) (t : I) :
    copulaPickands (stableTailCopula L) t=L.value (1-(t:ℝ)) (t:ℝ) := by
  unfold copulaPickands pickandsRay
  rw [stableTailCopula_cdf,stableTailCDF_positive_coords L _ _ (Real.exp_pos _) (Real.exp_pos _)]
  simp only [unitNegExp,Real.log_exp,neg_neg]
  have he : L.value ((1-(t:ℝ))/2) ((t:ℝ)/2)=
      (1/2:ℝ)*L.value (1-(t:ℝ)) (t:ℝ) := by
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using
      L.homogeneous (sub_nonneg.mpr t.property.2) t.property.1 (by norm_num : (0:ℝ)≤1/2)
  rw [he]
  ring

end Verification
