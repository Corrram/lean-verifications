import Verification.ConcentrationIntegral
import Papers.AnsariRockel2024.StudentOrder
import Verification.CopulaMovingPointLimit
import Verification.NormalQuantile

open ProbabilityTheory MeasureTheory Real Set Filter Copula Verification
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem student_marginal_gaussian_limit {ι : Type*} {l : Filter ι}
    (ν : ι→ℝ) (hν : ∀ i,0<ν i) (ht : Tendsto ν l atTop)
    (r : ℝ) (hr : r∈Icc (-1) 1) (j : Fin 2) (a : ℝ) :
    Tendsto (fun i => ProbabilityTheory.cdf (marginal (studentTLaw (bivariateCorrelation r) (ν i) (hν i)) j) a)
      l (nhds (ProbabilityTheory.cdf (gaussianReal 0 1) a)) := by
  simp only [student_marginal_cdf r hr]
  have hc : Continuous (fun t : ℝ => ProbabilityTheory.cdf (gaussianReal 0 1) (a*Real.sqrt t)) :=
    continuous_standardNormalCDF.comp (by fun_prop)
  have h := gammaPrecision_integral_tendsto (fun i => ν i/2)
    (fun i => div_pos (hν i) (by norm_num)) (ht.atTop_div_const (by norm_num))
    _ hc.measurable hc.continuousAt (B := 1) (fun t => by
      rw [abs_of_nonneg (ProbabilityTheory.cdf_nonneg _ _)]
      exact ProbabilityTheory.cdf_le_one _ _)
  simp only [Real.sqrt_one,mul_one] at h
  exact h

theorem student_joint_gaussian_limit {ι : Type*} {l : Filter ι}
    (ν : ι→ℝ) (hν : ∀ i,0<ν i) (ht : Tendsto ν l atTop)
    (r : ℝ) (hr : r∈Icc (-1) 1) (a b : ℝ) :
    Tendsto (fun i => (studentTLaw (bivariateCorrelation r) (ν i) (hν i)).toMeasure.real (Iic ![a,b]))
      l (nhds ((gaussianBivariate r hr).cdf ![cdfUnit (gaussianReal 0 1) a,cdfUnit (gaussianReal 0 1) b])) := by
  simp only [student_joint_cdf r hr]
  have hN : Continuous (cdfUnit (gaussianReal 0 1)) :=
    continuous_standardNormalCDF.subtype_mk _
  have hc : Continuous (fun t : ℝ => (gaussianBivariate r hr).cdf
      ![cdfUnit (gaussianReal 0 1) (a*Real.sqrt t),cdfUnit (gaussianReal 0 1) (b*Real.sqrt t)]) :=
    (gaussianBivariate r hr).continuous_cdf.comp (by fun_prop)
  have h := gammaPrecision_integral_tendsto (fun i => ν i/2)
    (fun i => div_pos (hν i) (by norm_num)) (ht.atTop_div_const (by norm_num))
    _ hc.measurable hc.continuousAt (B := 1) (fun t => by
      rw [abs_of_nonneg (Copula.cdf_nonneg _ _)]
      exact Copula.cdf_le_one _ _)
  simp only [Real.sqrt_one,mul_one] at h
  exact h

theorem student_copula_gaussian_limit_interior {ι : Type*} {l : Filter ι}
    (ν : ι→ℝ) (hν : ∀ i,0<ν i) (ht : Tendsto ν l atTop)
    (r : ℝ) (hr : r∈Icc (-1) 1) (u : Fin 2→I)
    (hu : ∀ j,(u j:ℝ)∈Ioo (0:ℝ) 1) :
    Tendsto (fun i => (studentBivariate r hr (ν i) (hν i)).cdf u)
      l (nhds ((gaussianBivariate r hr).cdf u)) := by
  let a := normalQuantile (u 0)
  let b := normalQuantile (u 1)
  let v := fun i => marginalTransform (studentTLaw (bivariateCorrelation r) (ν i) (hν i)) ![a,b]
  apply copula_cdf_limit_of_moving_point (fun i => studentBivariate r hr (ν i) (hν i)) v u
  · intro j
    fin_cases j
    · change Tendsto (fun i => ProbabilityTheory.cdf (marginal
        (studentTLaw (bivariateCorrelation r) (ν i) (hν i)) 0) a) l (nhds (u 0:ℝ))
      have h := student_marginal_gaussian_limit ν hν ht r hr 0 a
      rw [cdf_normalQuantile (hu 0)] at h
      exact h
    · change Tendsto (fun i => ProbabilityTheory.cdf (marginal
        (studentTLaw (bivariateCorrelation r) (ν i) (hν i)) 1) b) l (nhds (u 1:ℝ))
      have h := student_marginal_gaussian_limit ν hν ht r hr 1 b
      rw [cdf_normalQuantile (hu 1)] at h
      exact h
  · have he : (fun i => (studentBivariate r hr (ν i) (hν i)).cdf (v i))=
        fun i => (studentTLaw (bivariateCorrelation r) (ν i) (hν i)).toMeasure.real (Iic ![a,b]) := by
      funext i
      exact student_isSklarCopula r hr (ν i) (hν i) ![a,b]
    rw [he]
    have hv : ![cdfUnit (gaussianReal 0 1) a,cdfUnit (gaussianReal 0 1) b]=u := by
      ext j
      fin_cases j
      · exact cdf_normalQuantile (hu 0)
      · exact cdf_normalQuantile (hu 1)
    have h := student_joint_gaussian_limit ν hν ht r hr a b
    rw [hv] at h
    exact h

theorem student_copula_gaussian_limit {ι : Type*} {l : Filter ι}
    (ν : ι→ℝ) (hν : ∀ i,0<ν i) (ht : Tendsto ν l atTop)
    (r : ℝ) (hr : r∈Icc (-1) 1) (u : Fin 2→I) :
    Tendsto (fun i => (studentBivariate r hr (ν i) (hν i)).cdf u)
      l (nhds ((gaussianBivariate r hr).cdf u)) := by
  by_cases h0 : u 0=0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 0 h0]
    exact tendsto_const_nhds
  by_cases h1 : u 1=0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 1 h1]
    exact tendsto_const_nhds
  have he : u=![u 0,u 1] := by ext j; fin_cases j <;> rfl
  by_cases h01 : u 0=1
  · have hb (C : Copula 2) : C.cdf u=(u 1:ℝ) := by
      conv_lhs => rw [he,h01]
      exact cdf_two_one_left _ _
    simp only [hb]
    exact tendsto_const_nhds
  by_cases h11 : u 1=1
  · have hb (C : Copula 2) : C.cdf u=(u 0:ℝ) := by
      conv_lhs => rw [he,h11]
      exact cdf_two_one_right _ _
    simp only [hb]
    exact tendsto_const_nhds
  apply student_copula_gaussian_limit_interior ν hν ht r hr u
  intro j
  fin_cases j
  · exact ⟨lt_of_le_of_ne (u 0).property.1 (fun h => h0 (Subtype.ext h.symm)),
      lt_of_le_of_ne (u 0).property.2 (fun h => h01 (Subtype.ext h))⟩
  · exact ⟨lt_of_le_of_ne (u 1).property.1 (fun h => h1 (Subtype.ext h.symm)),
      lt_of_le_of_ne (u 1).property.2 (fun h => h11 (Subtype.ext h))⟩

end Papers.AnsariRockel2024
