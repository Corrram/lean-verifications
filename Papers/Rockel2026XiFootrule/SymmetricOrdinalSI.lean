import Papers.Rockel2026XiFootrule.SymmetricOrdinalEquality

open MeasureTheory ProbabilityTheory Set Verification Copula.OrdinalSum
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

private theorem antitone_unitJoin (a : I) (f g : I → ℝ)
    (hf : Antitone f) (hg : Antitone g)
    (hfg : ∀ u v, g v ≤ f u) :
    Antitone (unitJoin a f g) := by
  intro u w huw
  unfold unitJoin
  by_cases hu : u ≤ a
  · by_cases hw : w ≤ a
    · simp only [ite_eq_left hu, ite_eq_left hw]
      exact hf (lowerCoord_mono a huw)
    · simp only [ite_eq_left hu, ite_eq_right hw]
      exact hfg _ _
  · have hw : ¬ w ≤ a := fun h => hu (huw.trans h)
    simp only [ite_eq_right hu, ite_eq_right hw]
    exact hg (upperCoord_mono a huw)

private theorem ordinalSum_cdf_eq_kernel_integral
    (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1)
    (u v : I) :
    (C.ordinalSum D a).cdf ![u,v] =
      ∫ t in Iic u, blockKernel C D a v t := by
  rw [← conditionalBlocks_eq_ordinalSum C D a ha0 ha1]
  exact copulaOfConditionalAE_cdf
    (blockKernel C D a) (blockKernel_integrable C D a)
    (blockKernel_mono C D a) (blockKernel_zero C D a)
    (blockKernel_one C D a ha0 ha1) (blockKernel_mean C D a ha0 ha1) u v

/-- Binary ordinal sums preserve stochastic increase, including endpoint splits. -/
theorem ordinalSum_isSI (C D : Copula 2)
    (hC : C.IsSI) (hD : D.IsSI) (a : I) :
    (C.ordinalSum D a).IsSI := by
  by_cases ha0 : a = 0
  · subst a
    simpa using hD
  by_cases ha1 : a = 1
  · subst a
    simpa using hC
  have hp : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm ha0)
  have hl : a < 1 := lt_of_le_of_ne a.property.2 ha1
  intro u w x v huw hwx
  by_cases hv : v ≤ a
  · obtain ⟨g, hg, hb, he⟩ := conditionalCDF_antitone_version C hC (lowerCoord a v)
    let k : I → ℝ := unitJoin a g (fun _ => 0)
    have hk : Antitone k := antitone_unitJoin a g (fun _ => 0) hg antitone_const
      (fun t s => (hb t).1)
    have hki : Integrable k := integrable_unit_bounded
      (measurable_unitJoin a hg.measurable measurable_const)
      (fun t => by
        change unitJoin a g (fun _ => 0) t ∈ Icc (0 : ℝ) 1
        unfold unitJoin
        split_ifs
        · exact hb _
        · exact ⟨le_refl _, zero_le_one⟩)
    have he' : (fun t => normalizedCDF C t (lowerCoord a v)) =ᵐ[volume] g :=
      (normalizedCDF_ae C (lowerCoord a v)).trans he
    have hprefix (r : I) :
        (C.ordinalSum D a).cdf ![r,v] = ∫ t in Iic r, k t := by
      rw [ordinalSum_cdf_eq_kernel_integral C D a hp hl]
      change (∫ t in Iic r, unitJoin a
        (fun t => normalizedCDF C t (lowerCoord a v))
        (fun t => normalizedCDF D t (upperCoord a v)) t) =
        ∫ t in Iic r, unitJoin a g (fun _ => 0) t
      have hmC : Measurable (fun t : I => normalizedCDF C t (lowerCoord a v)) :=
        (normalizedCDF_measurable C).comp (measurable_const.prodMk measurable_id)
      have hmD : Measurable (fun t : I => normalizedCDF D t (upperCoord a v)) :=
        (normalizedCDF_measurable D).comp (measurable_const.prodMk measurable_id)
      calc
        _ = (a : ℝ) * (∫ t in Iic (lowerCoord a r), normalizedCDF C t (lowerCoord a v)) +
            (1 - (a : ℝ)) * (∫ t in Iic (upperCoord a r), normalizedCDF D t (upperCoord a v)) :=
          integral_unitJoin_prefix a hp hl _ _ hmC hmD
            (normalizedCDF_integrable C _) (normalizedCDF_integrable D _) r
        _ = (a : ℝ) * (∫ t in Iic (lowerCoord a r), g t) +
            (1 - (a : ℝ)) * (∫ t in Iic (upperCoord a r), (0 : ℝ)) := by
          rw [integral_congr_ae (ae_restrict_of_ae he'), upperCoord_of_le a v hv]
          simp [normalizedCDF_zero]
        _ = _ := (integral_unitJoin_prefix a hp hl g (fun _ => 0)
            hg.measurable measurable_const
            (integrable_unit_bounded hg.measurable hb) (integrable_const _) r).symm
    rw [hprefix u, hprefix w, hprefix x]
    exact Copula.integral_Iic_concave_of_antitone hki hk u w x huw hwx
  · have hav : a ≤ v := le_of_not_ge hv
    obtain ⟨g, hg, hb, he⟩ := conditionalCDF_antitone_version D hD (upperCoord a v)
    let k : I → ℝ := unitJoin a (fun _ => 1) g
    have hk : Antitone k := antitone_unitJoin a (fun _ => 1) g antitone_const hg
      (fun t s => (hb s).2)
    have hki : Integrable k := integrable_unit_bounded
      (measurable_unitJoin a measurable_const hg.measurable)
      (fun t => by
        change unitJoin a (fun _ => 1) g t ∈ Icc (0 : ℝ) 1
        unfold unitJoin
        split_ifs
        · exact ⟨zero_le_one, le_refl _⟩
        · exact hb _)
    have he' : (fun t => normalizedCDF D t (upperCoord a v)) =ᵐ[volume] g :=
      (normalizedCDF_ae D (upperCoord a v)).trans he
    have hprefix (r : I) :
        (C.ordinalSum D a).cdf ![r,v] = ∫ t in Iic r, k t := by
      rw [ordinalSum_cdf_eq_kernel_integral C D a hp hl]
      change (∫ t in Iic r, unitJoin a
        (fun t => normalizedCDF C t (lowerCoord a v))
        (fun t => normalizedCDF D t (upperCoord a v)) t) =
        ∫ t in Iic r, unitJoin a (fun _ => 1) g t
      have hmC : Measurable (fun t : I => normalizedCDF C t (lowerCoord a v)) :=
        (normalizedCDF_measurable C).comp (measurable_const.prodMk measurable_id)
      have hmD : Measurable (fun t : I => normalizedCDF D t (upperCoord a v)) :=
        (normalizedCDF_measurable D).comp (measurable_const.prodMk measurable_id)
      calc
        _ = (a : ℝ) * (∫ t in Iic (lowerCoord a r), normalizedCDF C t (lowerCoord a v)) +
            (1 - (a : ℝ)) * (∫ t in Iic (upperCoord a r), normalizedCDF D t (upperCoord a v)) :=
          integral_unitJoin_prefix a hp hl _ _ hmC hmD
            (normalizedCDF_integrable C _) (normalizedCDF_integrable D _) r
        _ = (a : ℝ) * (∫ t in Iic (lowerCoord a r), (1 : ℝ)) +
            (1 - (a : ℝ)) * (∫ t in Iic (upperCoord a r), g t) := by
          rw [integral_congr_ae (ae_restrict_of_ae he'), lowerCoord_of_ge a v hp hav]
          simp [normalizedCDF_one]
        _ = _ := (integral_unitJoin_prefix a hp hl (fun _ => 1) g
            measurable_const hg.measurable
            (integrable_const _) (integrable_unit_bounded hg.measurable hb) r).symm
    rw [hprefix u, hprefix w, hprefix x]
    exact Copula.integral_Iic_concave_of_antitone hki hk u w x huw hwx


/-- Every finite nested ordinal sum of independence and comonotonic blocks is SI. -/
theorem FinitePiOrdinal.isSI {C : Copula 2} (h : FinitePiOrdinal C) : C.IsSI := by
  induction h with
  | independence => exact Copula.isSI_independence
  | comonotonic => exact Copula.isSI_comonotonic
  | ordinalSum hC hD a ihC ihD => exact ordinalSum_isSI _ _ ihC ihD a

/-- The finite part of the symmetric SI equality construction. -/
theorem FinitePiOrdinal.symmetric_si_rank_equality
    {C : Copula 2} (h : FinitePiOrdinal C) :
    C.IsSI ∧ C.IsExchangeable ∧ C.chatterjeeXi = C.spearmanFootrule :=
  ⟨h.isSI, h.symmetric_rank_equality⟩

end Papers.Rockel2026XiFootrule