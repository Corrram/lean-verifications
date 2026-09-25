import Papers.AnsariRockel2024.BB5

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem bb5_shape_one (δ : ℝ) (hδ : 0<δ) :
    Verification.bb5 1 δ le_rfl hδ=Verification.galambos δ hδ := by
  apply ext_cdf
  intro u
  have hu : u=![u 0,u 1] := by ext i; fin_cases i <;> rfl
  by_cases hz : ∃ j,u j=0
  · obtain ⟨j,hj⟩ := hz
    simp only [cdf_eq_zero_of_coord_eq_zero _ u j hj]
  by_cases h0 : u 0=1
  · rw [hu,h0,cdf_two_one_left,cdf_two_one_left]
  by_cases h1 : u 1=1
  · rw [hu,h1,cdf_two_one_right,cdf_two_one_right]
  have hp (j) : 0<(u j:ℝ) := lt_of_le_of_ne (u j).property.1
    (fun h => hz ⟨j,Subtype.ext h.symm⟩)
  have hi0 : (u 0:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨hp 0,lt_of_le_of_ne (u 0).property.2 (fun h => h0 (Subtype.ext h))⟩
  have hi1 : (u 1:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨hp 1,lt_of_le_of_ne (u 1).property.2 (fun h => h1 (Subtype.ext h))⟩
  conv_lhs => rw [hu,bb5_cdf_interior 1 δ le_rfl hδ _ _ hi0 hi1]
  conv_rhs => rw [hu,galambos_cdf_interior δ hδ _ _ hi0 hi1]
  rw [Verification.bb5TailKernel_shape_one]
  have he : -(-Real.log (u 0:ℝ)+ -Real.log (u 1:ℝ)-
      Verification.galambosTailKernel δ (-Real.log (u 0:ℝ)) (-Real.log (u 1:ℝ))) =
      Real.log (u 0:ℝ)+Real.log (u 1:ℝ)+
        Verification.galambosTailKernel δ (-Real.log (u 0:ℝ)) (-Real.log (u 1:ℝ)) := by ring
  rw [he,Real.exp_add,Real.exp_add,Real.exp_log (hp 0),Real.exp_log (hp 1)]
  rfl

end Papers.AnsariRockel2024
