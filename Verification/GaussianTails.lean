import Verification.GaussianQuantileConditional
import Verification.GaussianDependence
import Copula.TailDependence.Quadrant
import Copula.TailDependence.Examples

open MeasureTheory ProbabilityTheory Set Copula Filter
open scoped unitInterval Topology

namespace Verification

theorem standardGaussian_lower_triangle {r : ℝ} (hr : r∈Ioo (-1) 1) (a : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {p : ℝ×ℝ | p.1≤a ∧ r*p.1+Real.sqrt (1-r^2)*p.2≤p.1}=
      ∫ x in Iic a, ProbabilityTheory.cdf (gaussianReal 0 1)
        ((x-r*x)/Real.sqrt (1-r^2)) ∂gaussianReal 0 1 := by
  let μ := gaussianReal 0 1
  let S := {p : ℝ×ℝ | p.1≤a ∧ r*p.1+Real.sqrt (1-r^2)*p.2≤p.1}
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le
        ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd))
        measurable_fst)
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) (μ.prod μ) :=
    (integrable_const _).indicator hS
  have hs : 0<Real.sqrt (1-r^2) := Real.sqrt_pos.2 (by nlinarith [hr.1,hr.2])
  change (μ.prod μ).real S=_
  rw [← integral_indicator_one hS]
  change (∫ p, S.indicator (fun _ => (1:ℝ)) p ∂μ.prod μ)=_
  rw [integral_prod _ hi,← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x≤a
    · rw [indicator_of_mem (show x∈Iic a from hx)]
      have hf (y : ℝ) : S.indicator (fun _ => (1:ℝ)) (x,y)=
          if Real.sqrt (1-r^2)*y≤x-r*x then (1:ℝ) else 0 := by
        simp only [S,indicator,mem_ofPred_eq,hx,true_and]
        congr 1
        apply propext
        constructor <;> intro h <;> linarith
      simp_rw [hf]
      exact standardGaussian_linear_halfline hs (x-r*x)
    · simp [S,indicator,hx]

theorem gaussianBivariate_triangle_normal {r : ℝ} (hr : r∈Ioo (-1) 1) (a : ℝ) :
    (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).toMeasure.real
      {u | u 0≤cdfUnit (gaussianReal 0 1) a ∧ u 1≤u 0}=
      ∫ x in Iic a, ProbabilityTheory.cdf (gaussianReal 0 1)
        ((x-r*x)/Real.sqrt (1-r^2)) ∂gaussianReal 0 1 := by
  let μ := gaussianReal 0 1
  let S := {p : ℝ×ℝ | p.1≤a ∧ r*p.1+Real.sqrt (1-r^2)*p.2≤p.1}
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le
        ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd))
        measurable_fst)
  have hm : Measurable (fun x : Fin 2 → ℝ => ![cdfUnit μ (x 0),
      cdfUnit μ (r*x 0+Real.sqrt (1-r^2)*x 1)]) := by fun_prop
  erw [gaussianBivariate_toMeasure_independent]
  have hA : MeasurableSet {u : Fin 2 → I | u 0≤cdfUnit μ a ∧ u 1≤u 0} :=
    (measurableSet_le (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (by fun_prop) (by fun_prop))
  rw [map_measureReal_apply hm hA]
  have hset : (fun x : Fin 2 → ℝ => ![cdfUnit μ (x 0),
      cdfUnit μ (r*x 0+Real.sqrt (1-r^2)*x 1)]) ⁻¹'
      {u | u 0≤cdfUnit μ a ∧ u 1≤u 0}=MeasurableEquiv.finTwoArrow ⁻¹' S := by
    ext x
    change (ProbabilityTheory.cdf μ (x 0)≤ProbabilityTheory.cdf μ a ∧
      ProbabilityTheory.cdf μ (r*x 0+Real.sqrt (1-r^2)*x 1)≤ProbabilityTheory.cdf μ (x 0)) ↔
      (x 0≤a ∧ r*x 0+Real.sqrt (1-r^2)*x 1≤x 0)
    simp only [μ,standardNormalCDF_strictMono.le_iff_le]
  rw [hset]
  have he := congrArg ENNReal.toReal
    ((measurePreserving_finTwoArrow μ).measure_preimage hS.nullMeasurableSet)
  change (Measure.pi (fun _ : Fin 2 => μ)).real (MeasurableEquiv.finTwoArrow ⁻¹' S)=
    (μ.prod μ).real S at he
  rw [he]
  exact standardGaussian_lower_triangle hr a

theorem symmetricCopula_diagonal_le_triangle (C : Copula 2) (hC : C.transpose=C) (t : I) :
    C.diagonal t ≤ 2*C.toMeasure.real {u | u 0≤t ∧ u 1≤u 0} := by
  let A := {u : Fin 2 → I | u 0≤t ∧ u 1≤u 0}
  let B := {u : Fin 2 → I | u 1≤t ∧ u 0≤u 1}
  have hA : MeasurableSet A := (measurableSet_le (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop))
  have he : C.toMeasure.real B=C.toMeasure.real A := by
    have hh := congrArg (fun D : Copula 2 => D.toMeasure.real A) hC
    rw [transpose,toMeasure_reindex,map_measureReal_apply (by fun_prop) hA] at hh
    simpa only [A,B,Set.preimage_ofPred_eq,Function.comp_def,Matrix.cons_val_zero,Matrix.cons_val_one] using hh
  have hs : Iic ![t,t] ⊆ A∪B := by
    intro u hu
    rcases le_total (u 0) (u 1) with h | h
    · exact Or.inr ⟨hu 1,h⟩
    · exact Or.inl ⟨hu 0,h⟩
  exact (measureReal_mono hs).trans ((measureReal_union_le A B).trans_eq (by rw [he]; ring))

theorem normalQuantile_tendsto_zero :
    Tendsto normalQuantile (𝓝[>] (0 : I)) atBot := by
  apply tendsto_atBot.mpr
  intro b
  have ht : Tendsto (fun u : I => (u:ℝ)) (𝓝[>] (0:I)) (𝓝 (0:ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hb := (tendsto_order.mp ht).2 _ (normalCDF_mem_Ioo b).1
  filter_upwards [hb,(self_mem_nhdsWithin : ∀ᶠ u : I in 𝓝[>] (0:I),0<u)] with u hu hu0
  apply standardNormalCDF_strictMono.le_iff_le.mp
  rw [cdf_normalQuantile ⟨hu0,hu.trans (normalCDF_mem_Ioo b).2⟩]
  exact hu.le

theorem gaussianBivariate_diagonal_normal_bound {r : ℝ} (hr : r∈Ioo (-1) 1) (a : ℝ) :
    (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).diagonal (cdfUnit (gaussianReal 0 1) a) ≤
      2*ProbabilityTheory.cdf (gaussianReal 0 1) a *
        ProbabilityTheory.cdf (gaussianReal 0 1) (((1-r)/Real.sqrt (1-r^2))*a) := by
  let μ := gaussianReal 0 1
  let k := (1-r)/Real.sqrt (1-r^2)
  have hk : 0<k := div_pos (by linarith [hr.2]) (Real.sqrt_pos.mpr (by nlinarith [hr.1,hr.2]))
  have hm : Measurable (fun x : ℝ => ProbabilityTheory.cdf μ (k*x)) :=
    (monotone_cdf μ).measurable.comp (by fun_prop)
  have hi : Integrable (fun x : ℝ => ProbabilityTheory.cdf μ (k*x)) μ :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (cdf_nonneg μ _)]
      exact cdf_le_one μ _)
  have hbound : (∫ x in Iic a, ProbabilityTheory.cdf μ (k*x) ∂μ) ≤
      ProbabilityTheory.cdf μ a * ProbabilityTheory.cdf μ (k*a) := by
    calc
      _ ≤ ∫ _ in Iic a, ProbabilityTheory.cdf μ (k*a) ∂μ :=
        setIntegral_mono_on hi.integrableOn (integrable_const _).integrableOn measurableSet_Iic
          (fun x hx => monotone_cdf μ (mul_le_mul_of_nonneg_left hx hk.le))
      _ = _ := by rw [setIntegral_const,smul_eq_mul,← ProbabilityTheory.cdf_eq_real]
  have h := symmetricCopula_diagonal_le_triangle _ (gaussianBivariate_transpose ⟨hr.1.le,hr.2.le⟩) (cdfUnit μ a)
  rw [gaussianBivariate_triangle_normal hr] at h
  have he (x : ℝ) : (x-r*x)/Real.sqrt (1-r^2)=k*x := by dsimp [k]; ring
  simp_rw [he] at h
  exact h.trans (by dsimp only [μ,k] at hbound ⊢; nlinarith)

theorem gaussianBivariate_radiallySymmetric {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).IsRadiallySymmetric := by
  have hn : -r∈Icc (-1) 1 := by constructor <;> linarith [hr.1,hr.2]
  have hf : (gaussianBivariate r hr).reflect {0}=gaussianBivariate (-r) hn := by
    have h := transpose_reflect_first (gaussianBivariate r hr)
    rw [gaussianBivariate_transpose hr,← gaussianBivariate_neg hr] at h
    have he := congrArg Copula.transpose h
    simpa only [transpose_transpose,gaussianBivariate_transpose hn] using he
  change (gaussianBivariate r hr).survivalCopula=gaussianBivariate r hr
  rw [← reflect_first_second,hf,← gaussianBivariate_neg hn]
  simp only [neg_neg]

theorem gaussianBivariate_lowerTail_zero {r : ℝ} (hr : r∈Ioo (-1) 1) :
    (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).HasLowerTailDependence 0 := by
  let C := gaussianBivariate r ⟨hr.1.le,hr.2.le⟩
  let k := (1-r)/Real.sqrt (1-r^2)
  have hk : 0<k := div_pos (by linarith [hr.2]) (Real.sqrt_pos.mpr (by nlinarith [hr.1,hr.2]))
  have ht := (tendsto_cdf_atBot (gaussianReal 0 1)).comp
    (normalQuantile_tendsto_zero.const_mul_atBot hk)
  have htwo : Tendsto (fun u : I => 2*ProbabilityTheory.cdf (gaussianReal 0 1) (k*normalQuantile u))
      (𝓝[>] (0:I)) (𝓝 (0:ℝ)) := by simpa using ht.const_mul 2
  change Tendsto C.lowerTailRatio _ _
  apply squeeze_zero' (Eventually.of_forall fun u => (C.lowerTailRatio_mem_Icc u).1) ?_ htwo
  have hlt : ∀ᶠ u : I in 𝓝[>] (0:I),u<1 :=
    (eventually_lt_nhds (show (0:I)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hlt,(self_mem_nhdsWithin : ∀ᶠ u : I in 𝓝[>] (0:I),0<u)] with u hu1 hu0
  have he : cdfUnit (gaussianReal 0 1) (normalQuantile u)=u :=
    Subtype.ext (cdf_normalQuantile ⟨hu0,hu1⟩)
  have h := gaussianBivariate_diagonal_normal_bound hr (normalQuantile u)
  rw [he,cdf_normalQuantile ⟨hu0,hu1⟩] at h
  apply (div_le_iff₀ (show (0:ℝ)<u from hu0)).mpr
  dsimp only [C,k] at *
  nlinarith

theorem gaussianBivariate_lowerTail {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).HasLowerTailDependence (if r=1 then 1 else 0) := by
  by_cases h1 : r=1
  · subst r
    simpa [gaussianBivariate_one] using hasLowerTailDependence_comonotonic
  rw [ite_eq_right h1]
  by_cases hn : r=-1
  · exact isNQD_hasLowerTailDependence_zero ((gaussianBivariate_isNQD_iff hr).mpr (by linarith))
  exact gaussianBivariate_lowerTail_zero ⟨lt_of_le_of_ne hr.1 (Ne.symm hn),lt_of_le_of_ne hr.2 h1⟩

theorem gaussianBivariate_upperTail {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).HasUpperTailDependence (if r=1 then 1 else 0) :=
  ((gaussianBivariate_radiallySymmetric hr).hasUpperTailDependence_iff _).mpr
    (gaussianBivariate_lowerTail hr)

end Verification
