import Verification.Raftery
import Copula.TailDependence.Derivative

open ProbabilityTheory Copula
open scoped unitInterval

namespace Verification

noncomputable def rafteryDiag (δ t : ℝ) : ℝ :=
  t+(1-δ)/(1+δ)*(t^(2/(1-δ))-t)

theorem rafteryDiag_eq (δ : I) (h1 : δ≠1) (t : I) :
    rafteryDiag δ t = (raftery δ).diagonal t := by
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr
    (lt_of_le_of_ne δ.property.2 (fun h => h1 (Subtype.ext h)))
  rw [diagonal,raftery_cdf δ h1]
  simp only [min_self,max_self]
  by_cases ht : (t:ℝ)=0
  · simp only [ht,rafteryDiag,Real.zero_rpow (ne_of_gt (div_pos (by norm_num : (0:ℝ)<2) hd)),
      Real.zero_rpow (ne_of_gt (one_div_pos.mpr hd)),zero_sub,neg_zero,zero_mul,mul_zero,add_zero]
  have htp : 0<(t:ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
  have hp : (t:ℝ)^(1/(1-(δ:ℝ)))*(t:ℝ)^(1/(1-(δ:ℝ))) = (t:ℝ)^(2/(1-(δ:ℝ))) := by
    rw [← Real.rpow_add htp]
    congr 1; ring
  have hq : (t:ℝ)^(1/(1-(δ:ℝ)))*(t:ℝ)^(-(δ:ℝ)/(1-(δ:ℝ))) = t := by
    rw [← Real.rpow_add htp]
    have he : 1/(1-(δ:ℝ)) + -(δ:ℝ)/(1-(δ:ℝ)) = 1 := by field_simp; ring
    rw [he,Real.rpow_one]
  unfold rafteryDiag
  calc
    _ = (t:ℝ)+(1-(δ:ℝ))/(1+(δ:ℝ))*
        ((t:ℝ)^(1/(1-(δ:ℝ)))*(t:ℝ)^(1/(1-(δ:ℝ)))-
          (t:ℝ)^(1/(1-(δ:ℝ)))*(t:ℝ)^(-(δ:ℝ)/(1-(δ:ℝ)))) := by rw [hp,hq]
    _ = _ := by ring

theorem rafteryDiag_deriv (δ : I) (h1 : δ≠1) (t : ℝ) :
    HasDerivAt (rafteryDiag δ)
      (1+(1-(δ:ℝ))/(1+(δ:ℝ))*(2/(1-(δ:ℝ))*t^(2/(1-(δ:ℝ))-1)-1)) t := by
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr
    (lt_of_le_of_ne δ.property.2 (fun h => h1 (Subtype.ext h)))
  have hp : 1≤2/(1-(δ:ℝ)) := by
    apply (le_div_iff₀ hd).mpr
    linarith [δ.property.1]
  exact (hasDerivAt_id t).add
    (((Real.hasDerivAt_rpow_const (x:=t) (Or.inr hp)).sub (hasDerivAt_id t)).const_mul _)

theorem raftery_tails_lt_one (δ : I) (h1 : δ≠1) :
    (raftery δ).HasLowerTailDependence (2*(δ:ℝ)/(1+(δ:ℝ))) ∧
      (raftery δ).HasUpperTailDependence 0 := by
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr
    (lt_of_le_of_ne δ.property.2 (fun h => h1 (Subtype.ext h)))
  have hb : 0<2/(1-(δ:ℝ))-1 := by
    have hh : 1<2/(1-(δ:ℝ)) := (lt_div_iff₀ hd).mpr (by linarith [δ.property.1])
    linarith
  have hp : 1+(δ:ℝ)≠0 := by linarith [δ.property.1]
  have h0 : HasDerivAt (rafteryDiag δ) (2*(δ:ℝ)/(1+(δ:ℝ))) 0 := by
    convert rafteryDiag_deriv δ h1 0 using 1
    rw [Real.zero_rpow hb.ne']
    field_simp [hp]
    ring
  have he1 : HasDerivAt (rafteryDiag δ) 2 1 := by
    convert rafteryDiag_deriv δ h1 1 using 1
    rw [Real.one_rpow]
    field_simp [hd.ne',hp]
    ring
  exact ⟨hasLowerTailDependence_of_hasDerivWithinAt (rafteryDiag_eq δ h1) h0.hasDerivWithinAt,
    by simpa using hasUpperTailDependence_of_hasDerivWithinAt (rafteryDiag_eq δ h1) he1.hasDerivWithinAt⟩

theorem raftery_tails_one :
    (raftery 1).HasLowerTailDependence 1 ∧ (raftery 1).HasUpperTailDependence 1 := by
  rw [raftery_one]
  exact ⟨hasLowerTailDependence_comonotonic,hasUpperTailDependence_comonotonic⟩

end Verification
