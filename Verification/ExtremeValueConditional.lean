import Verification.ExtremeValueSupport
import Copula.Dependence.ConditionalMonotonicity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Conditional increase of arbitrary bivariate extreme-value copulas -/

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

private theorem unitNegExp_neg_log (u : I) (hu : 0<(u:ℝ)) :
    unitNegExp (-Real.log (u:ℝ)) (neg_nonneg.mpr (Real.log_nonpos u.property.1 u.property.2))=u := by
  apply Subtype.ext
  simp only [unitNegExp,neg_neg,Real.exp_log hu]

private theorem extremeValue_cdf_pos (C : Copula 2) (hC : C.IsExtremeValue)
    (u v : I) (hu : 0<(u:ℝ)) (hv : 0<(v:ℝ)) : 0<C.cdf ![u,v] := by
  have hh := extremeValue_exp_cdf_pos C hC (-Real.log (u:ℝ)) (-Real.log (v:ℝ))
    (neg_nonneg.mpr (Real.log_nonpos u.property.1 u.property.2))
    (neg_nonneg.mpr (Real.log_nonpos v.property.1 v.property.2))
  simpa only [unitNegExp_neg_log u hu,unitNegExp_neg_log v hv] using hh

private theorem extremeValueLogSection_neg_log (C : Copula 2) (u v : I)
    (hu : 0<(u:ℝ)) (hv : 0<(v:ℝ)) :
    extremeValueLogSection C (-Real.log (v:ℝ))
      (neg_nonneg.mpr (Real.log_nonpos v.property.1 v.property.2)) (-Real.log (u:ℝ))=
        -Real.log (C.cdf ![u,v]) := by
  rw [extremeValueLogSection_of_nonneg C _ _ _
    (neg_nonneg.mpr (Real.log_nonpos u.property.1 u.property.2))]
  unfold extremeValueLog
  rw [unitNegExp_neg_log u hu,unitNegExp_neg_log v hv]

theorem extremeValue_cdf_support (C : Copula 2) (hC : C.IsExtremeValue)
    (u v : I) (hu : 0<(u:ℝ)) (hu1 : (u:ℝ)<1) (hv : 0<(v:ℝ)) :
    ∃ m : ℝ, ∀ z : I, C.cdf ![z,v]≤C.cdf ![u,v]+m*((z:ℝ)-u) := by
  let y := -Real.log (v:ℝ)
  have hy : 0≤y := neg_nonneg.mpr (Real.log_nonpos v.property.1 v.property.2)
  obtain ⟨p,hp,hs⟩ := extremeValueLogSection_support C hC y hy (-Real.log (u:ℝ))
    (neg_pos.mpr (Real.log_neg hu hu1))
  have hCu := extremeValue_cdf_pos C hC u v hu hv
  refine ⟨C.cdf ![u,v]*p/(u:ℝ),fun z => ?_⟩
  have hlinear : C.cdf ![u,v]*(1+p*((z:ℝ)/(u:ℝ)-1))=
      C.cdf ![u,v]+C.cdf ![u,v]*p/(u:ℝ)*((z:ℝ)-u) := by field_simp
  rw [← hlinear]
  by_cases hz : z=0
  · subst z
    rw [Copula.cdf_two_zero_left]
    change 0≤C.cdf ![u,v]*(1+p*(0/(u:ℝ)-1))
    simp only [zero_div,zero_sub,mul_neg_one]
    exact mul_nonneg hCu.le (by linarith [hp.2])
  have hzp : 0<(z:ℝ) := lt_of_le_of_ne z.property.1 (Ne.symm (fun h => hz (Subtype.ext h)))
  have hCz := extremeValue_cdf_pos C hC z v hzp hv
  have hh := hs (-Real.log (z:ℝ)) (neg_nonneg.mpr (Real.log_nonpos z.property.1 z.property.2))
  change extremeValueLogSection C (-Real.log (v:ℝ)) hy (-Real.log (u:ℝ))+
    p*(-Real.log (z:ℝ)- -Real.log (u:ℝ))≤
      extremeValueLogSection C (-Real.log (v:ℝ)) hy (-Real.log (z:ℝ)) at hh
  rw [extremeValueLogSection_neg_log C u v hu hv,extremeValueLogSection_neg_log C z v hzp hv] at hh
  have hl : Real.log (C.cdf ![z,v])≤Real.log (C.cdf ![u,v])+p*(Real.log (z:ℝ)-Real.log (u:ℝ)) := by linarith
  have he : Real.exp (Real.log (C.cdf ![u,v])+p*(Real.log (z:ℝ)-Real.log (u:ℝ)))=
      C.cdf ![u,v]*((z:ℝ)/(u:ℝ))^p := by
    rw [Real.exp_add,Real.exp_log hCu,Real.rpow_def_of_pos (div_pos hzp hu),Real.log_div hzp.ne' hu.ne']
    congr 1
    congr 1
    ring
  have hpower : C.cdf ![z,v]≤C.cdf ![u,v]*((z:ℝ)/(u:ℝ))^p := by
    have hh := Real.exp_le_exp.mpr hl
    rwa [Real.exp_log hCz,he] at hh
  have hb := rpow_one_add_le_one_add_mul_self
    (show -1≤(z:ℝ)/(u:ℝ)-1 by have := div_nonneg z.property.1 hu.le; linarith) hp.1 hp.2
  rw [show 1+((z:ℝ)/(u:ℝ)-1)=(z:ℝ)/(u:ℝ) by ring] at hb
  exact hpower.trans (mul_le_mul_of_nonneg_left hb hCu.le)

theorem extremeValue_isSI (C : Copula 2) (hC : C.IsExtremeValue) : C.IsSI := by
  intro a b c v hab hbc
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  rcases eq_or_lt_of_le hbc with rfl | hbc
  · simp
  by_cases hv : v=0
  · subst v; simp
  have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
  have hb0 : 0<(b:ℝ) := lt_of_le_of_lt a.property.1 hab
  have hb1 : (b:ℝ)<1 := lt_of_lt_of_le hbc c.property.2
  obtain ⟨m,hm⟩ := extremeValue_cdf_support C hC b v hb0 hb1 hvp
  have hA := mul_le_mul_of_nonneg_left (hm a) (sub_nonneg.mpr (show (b:ℝ)≤c from hbc.le))
  have hB := mul_le_mul_of_nonneg_left (hm c) (sub_nonneg.mpr (show (a:ℝ)≤b from hab.le))
  nlinarith only [hA,hB]

theorem extremeValue_transpose (C : Copula 2) (hC : C.IsExtremeValue) :
    C.transpose.IsExtremeValue := by
  intro z t ht
  have hz : z=![z 0,z 1] := by funext i; fin_cases i <;> rfl
  have hw : (fun i => unitPower (z i) t ht.le)=![unitPower (z 0) t ht.le,unitPower (z 1) t ht.le] := by
    funext i; fin_cases i <;> rfl
  rw [hw,hz,Copula.cdf_transpose,Copula.cdf_transpose]
  convert hC ![z 1,z 0] t ht using 1
  congr 1
  funext i
  fin_cases i <;> rfl

theorem extremeValue_isCI (C : Copula 2) (hC : C.IsExtremeValue) : C.IsCI :=
  ⟨extremeValue_isSI C hC,extremeValue_isSI C.transpose (extremeValue_transpose C hC)⟩

end Verification
