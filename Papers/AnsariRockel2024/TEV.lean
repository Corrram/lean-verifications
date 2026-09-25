import Verification.TEVEndpoints
import Verification.ScaleMixtureMarginals
import Papers.AnsariRockel2024.ExtremeValueOrders
import Papers.AnsariRockel2024.TEVSpectral
import Copula.TailDependence.Examples

/-! # The t-EV family (Tables 1, 4 and 5)

`Verification.tEV ν r` is the spectral extreme-value copula built from normalized positive
powers of a correlated Gaussian pair. Here it is identified with the printed Student-t
Pickands function, and its CI, tail, order and endpoint entries are checked.
`Verification.studentTCDF (ν+1)` is the Student-t CDF `T_{ν+1}`; it coincides with the
marginal CDF of the Student-t law with `ν+1` degrees of freedom used for the Student-t rows.
-/

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- `T_{ν+1}` is the marginal CDF of the standard Student-t law with `ν+1` degrees of freedom. -/
theorem tEV_student_cdf_eq (ν : ℝ) (hν : 0<ν) (x : ℝ) :
    Verification.studentTCDF (ν+1) x=
      ProbabilityTheory.cdf (marginal (studentTLaw (Verification.bivariateCorrelation 0) (ν+1)
        (by positivity)) 0) x := by
  rw [studentTLaw,Verification.gaussianScaleMixtureLaw_marginal _ (Verification.bivariateCorrelation_posSemidef
      (by norm_num)) (by intro j; fin_cases j <;> rfl) _ _ (by fun_prop) 0]
  exact Verification.studentTCDF_eq_mixture_cdf (ν+1) (by positivity) x

/-- The Pickands argument `z_t` in the printed form `sqrt((1+ν)/(1-ρ²))((t/(1-t))^(1/ν)-ρ)`. -/
theorem tEV_arg_def (ν r w : ℝ) :
    Verification.tEVArg ν r w=Real.sqrt ((1+ν)/(1-r^2))*(w-r) := rfl

/-- Tables 1 and 4: the t-EV Pickands function
`A(t)=(1-t)T_{ν+1}(z_{1-t})+t T_{ν+1}(z_t)`. -/
theorem tEV_pickands (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) (t : I)
    (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
    Verification.copulaPickands (Verification.tEV ν r hν ⟨hr.1.le,hr.2.le⟩) t=
      (1-(t:ℝ))*Verification.studentTCDF (ν+1)
        (Verification.tEVArg ν r (((1-(t:ℝ))/(t:ℝ))^(1/ν)))+
      (t:ℝ)*Verification.studentTCDF (ν+1)
        (Verification.tEVArg ν r (((t:ℝ)/(1-(t:ℝ)))^(1/ν))) :=
  Verification.tEV_pickands_formula ν r hν hr t ht

/-- Table 1: the t-EV CDF at interior points. -/
theorem tEV_cdf_interior (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) (u v : I)
    (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    (Verification.tEV ν r hν ⟨hr.1.le,hr.2.le⟩).cdf ![u,v]=Real.exp (-(
      (-Real.log (u:ℝ))*Verification.studentTCDF (ν+1)
        (Verification.tEVArg ν r (((-Real.log (u:ℝ))/(-Real.log (v:ℝ)))^(1/ν)))+
      (-Real.log (v:ℝ))*Verification.studentTCDF (ν+1)
        (Verification.tEVArg ν r (((-Real.log (v:ℝ))/(-Real.log (u:ℝ)))^(1/ν))))) :=
  Verification.tEV_cdf_interior ν r hν hr u v hu hv

/-- Table 5: the t-EV copula is CI for every admissible parameter. -/
theorem tEV_isCI (ν r : ℝ) (hν : 0<ν) (hr : r∈Icc (-1) 1) :
    (Verification.tEV ν r hν hr).IsCI := Verification.tEV_isCI ν r hν hr

/-- The extremal coefficient `2 T_{ν+1}(z_{1/2})`, with `z_{1/2}=sqrt((ν+1)(1-ρ)/(1+ρ))`. -/
theorem tEV_extremalCoefficient (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) :
    (Verification.tEV ν r hν ⟨hr.1.le,hr.2.le⟩).extremalCoefficient=
      2*Verification.studentTCDF (ν+1) (Real.sqrt ((ν+1)*(1-r)/(1+r))) := by
  rw [Verification.tEV_extremalCoefficient ν r hν hr,Verification.tEVArg_one ν r hν hr]

/-- Table 5: lower tail zero and upper tail `2(1-T_{ν+1}(z_{1/2}))` for `-1<ρ<1`. -/
theorem tEV_tails (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) :
    (Verification.tEV ν r hν ⟨hr.1.le,hr.2.le⟩).HasLowerTailDependence 0 ∧
    (Verification.tEV ν r hν ⟨hr.1.le,hr.2.le⟩).HasUpperTailDependence
      (2*(1-Verification.studentTCDF (ν+1) (Real.sqrt ((ν+1)*(1-r)/(1+r))))) := by
  have h := Verification.tEV_tails ν r hν hr
  rw [Verification.tEVArg_one ν r hν hr] at h
  refine ⟨h.1,?_⟩
  convert h.2 using 1
  ring

/-- The correlation endpoint `ρ=1` is the comonotonic copula; in particular the lower tail
coefficient is `1{ρ=1}` across the closed range. -/
theorem tEV_one (ν : ℝ) (hν : 0<ν) :
    Verification.tEV ν 1 hν ⟨by norm_num,le_rfl⟩=comonotonic 2 := Verification.tEV_one ν hν

theorem tEV_negative_one (ν : ℝ) (hν : 0<ν) :
    Verification.tEV ν (-1) hν ⟨le_rfl,by norm_num⟩=independence 2 :=
  Verification.tEV_negative_one ν hν

theorem tEV_lowerTail (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioc (-1) 1) :
    (Verification.tEV ν r hν ⟨hr.1.le,hr.2⟩).HasLowerTailDependence (if r=1 then 1 else 0) := by
  split_ifs with h1
  · subst r
    rw [tEV_one ν hν]
    exact hasLowerTailDependence_comonotonic
  · exact (tEV_tails ν r hν ⟨hr.1,lt_of_le_of_ne hr.2 h1⟩).1

theorem tEV_lowerOrthant_mono (ν r q : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) (hq : q∈Ioo (-1) 1)
    (hrq : r≤q) :
    (Verification.tEV ν r hν ⟨hr.1.le,hr.2.le⟩).LowerOrthantLE (Verification.tEV ν q hν ⟨hq.1.le,hq.2.le⟩) := by
  apply (extremeValue_pickands_order _ _ (Verification.tEV_isExtremeValue ν r hν _)
    (Verification.tEV_isExtremeValue ν q hν _)).mpr
  intro t ht0 ht1
  exact Verification.tEV_pickands_antitone ν r q hν hr hq hrq t ⟨ht0,ht1⟩

theorem tEV_schurBoth_mono (ν r q : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) (hq : q∈Ioo (-1) 1)
    (hrq : r≤q) :
    (Verification.tEV ν r hν ⟨hr.1.le,hr.2.le⟩).SchurBothLE (Verification.tEV ν q hν ⟨hq.1.le,hq.2.le⟩) := by
  apply (extremeValue_schur_iff_pickands_of_ci _ _ (Verification.tEV_isExtremeValue ν r hν _)
    (Verification.tEV_isExtremeValue ν q hν _) (Verification.tEV_isCI ν r hν _)
    (Verification.tEV_isCI ν q hν _)).mpr
  intro t ht0 ht1
  exact Verification.tEV_pickands_antitone ν r q hν hr hq hrq t ⟨ht0,ht1⟩

/-- Table 5: the lower-orthant order is exactly the correlation order on `(-1,1)`. -/
theorem tEV_lowerOrthant_iff (ν r q : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) (hq : q∈Ioo (-1) 1) :
    (Verification.tEV ν r hν ⟨hr.1.le,hr.2.le⟩).LowerOrthantLE
      (Verification.tEV ν q hν ⟨hq.1.le,hq.2.le⟩) ↔ r≤q := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have ht := h.upperTailDependence_le (Verification.tEV_tails ν r hν hr).2
      (Verification.tEV_tails ν q hν hq).2
    have hz := Verification.tEVArg_one_strictAntiOn ν hν hq hr hlt
    have hT := Verification.studentTCDF_strictMono (ν+1) (by linarith) hz
    simp only at hT
    linarith
  · exact tEV_lowerOrthant_mono ν r q hν hr hq

/-- Table 5: the two-direction Schur order is exactly the correlation order on `(-1,1)`. -/
theorem tEV_schurBoth_iff (ν r q : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) (hq : q∈Ioo (-1) 1) :
    (Verification.tEV ν r hν ⟨hr.1.le,hr.2.le⟩).SchurBothLE
      (Verification.tEV ν q hν ⟨hq.1.le,hq.2.le⟩) ↔ r≤q := by
  constructor
  · intro h
    apply (tEV_lowerOrthant_iff ν r q hν hr hq).mp
    exact (cis_schur_iff_orthant _ _ (Verification.tEV_isCI ν r hν _).1
      (Verification.tEV_isCI ν q hν _).1).mp h.1
  · exact tEV_schurBoth_mono ν r q hν hr hq

/-- Increasing lower-orthant order on the closed correlation interval, including the
independence and comonotonic endpoints. -/
theorem tEV_closed_lowerOrthant_mono (ν r q : ℝ) (hν : 0<ν) (hr : r∈Icc (-1) 1) (hq : q∈Icc (-1) 1)
    (hrq : r≤q) :
    (Verification.tEV ν r hν hr).LowerOrthantLE (Verification.tEV ν q hν hq) := by
  rcases hr.1.eq_or_lt with h|h
  · subst r
    rw [tEV_negative_one ν hν]
    exact (isPQD_iff_independence_le _).mp (Verification.tEV_isCI ν q hν hq).isPQD
  rcases hq.2.eq_or_lt with k|k
  · subst q
    rw [tEV_one ν hν]
    exact lowerOrthantLE_comonotonic _
  exact tEV_lowerOrthant_mono ν r q hν ⟨h,lt_of_le_of_lt hrq k⟩ ⟨lt_of_lt_of_le h hrq,k⟩ hrq

theorem tEV_closed_schurBoth_mono (ν r q : ℝ) (hν : 0<ν) (hr : r∈Icc (-1) 1) (hq : q∈Icc (-1) 1)
    (hrq : r≤q) :
    (Verification.tEV ν r hν hr).SchurBothLE (Verification.tEV ν q hν hq) := by
  apply (extremeValue_schur_iff_pickands_of_ci _ _ (Verification.tEV_isExtremeValue ν r hν hr)
    (Verification.tEV_isExtremeValue ν q hν hq) (Verification.tEV_isCI ν r hν hr)
    (Verification.tEV_isCI ν q hν hq)).mpr
  exact (extremeValue_pickands_order _ _ (Verification.tEV_isExtremeValue ν r hν hr)
    (Verification.tEV_isExtremeValue ν q hν hq)).mp (tEV_closed_lowerOrthant_mono ν r q hν hr hq hrq)

end Papers.AnsariRockel2024
