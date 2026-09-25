import Verification.TEVPickandsFormula
import Verification.TEVStudentDensity
import Verification.PickandsDiagonal
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Monotonicity of the t-EV family in the correlation parameter

The Pickands function of the t-EV copula decreases in `r` on `(-1,1)`. The derivative
of the two Student-t terms is `-K t f(z_t) (w²-2rw+1)` with `K>0`, where the balance
identity `(1-t) f(z_{1-t}) = t w² f(z_t)` relates the two Student-t densities.
-/

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Verification

theorem tEVArg_eq_div (ν r w : ℝ) (hν : 0<ν) :
    tEVArg ν r w=Real.sqrt (1+ν)*((w-r)/Real.sqrt (1-r^2)) := by
  unfold tEVArg
  rw [Real.sqrt_div (by linarith)]
  ring

/-- Derivative of the Pickands argument in the correlation parameter. -/
noncomputable def tEVArgDeriv (ν r w : ℝ) : ℝ :=
  Real.sqrt (1+ν)*((r*w-1)/((1-r^2)*Real.sqrt (1-r^2)))

theorem tEVArg_hasDerivAt (ν w : ℝ) (hν : 0<ν) {r : ℝ} (hr : r∈Ioo (-1) 1) :
    HasDerivAt (fun q => tEVArg ν q w) (tEVArgDeriv ν r w) r := by
  have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hsq : 0<Real.sqrt (1-r^2) := Real.sqrt_pos.mpr hs
  have hsq2 : Real.sqrt (1-r^2)^2=1-r^2 := Real.sq_sqrt hs.le
  have h1 : HasDerivAt (fun q : ℝ => 1-q^2) (-(2*r)) r := by
    simpa using (hasDerivAt_pow 2 r).const_sub 1
  have h2 := h1.sqrt hs.ne'
  have h3 := ((hasDerivAt_id r).const_sub w).div h2 hsq.ne'
  have h4 := h3.const_mul (Real.sqrt (1+ν))
  have he : (fun q => tEVArg ν q w)=fun q => Real.sqrt (1+ν)*((w-id q)/Real.sqrt (1-q^2)) := by
    funext q
    rw [tEVArg_eq_div ν q w hν]
    rfl
  rw [he]
  convert h4 using 1
  unfold tEVArgDeriv
  congr 1
  simp only [id]
  field_simp
  rw [hsq2]
  ring

theorem tEVArg_sq (ν r w : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) :
    (tEVArg ν r w)^2=(1+ν)/(1-r^2)*(w-r)^2 := by
  have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  unfold tEVArg
  rw [mul_pow,Real.sq_sqrt (by positivity)]

/-- Balance identity of the Student-t densities at the two Pickands arguments. -/
theorem tEV_density_balance (ν r w : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) (hw : 0<w) :
    studentMarginalPDF (ν+1) (tEVArg ν r w⁻¹)=
      (w^2)^((ν+1)/2+1/2)*studentMarginalPDF (ν+1) (tEVArg ν r w) := by
  have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hX : 0<(ν+1)/2+(tEVArg ν r w)^2/2 := by positivity
  have hw2 : 0<w^2 := by positivity
  have hbase : (ν+1)/2+(tEVArg ν r w⁻¹)^2/2=((ν+1)/2+(tEVArg ν r w)^2/2)/w^2 := by
    rw [tEVArg_sq ν r _ hν hr,tEVArg_sq ν r _ hν hr]
    field_simp
    ring
  unfold studentMarginalPDF
  rw [hbase,Real.div_rpow hX.le hw2.le]
  have hp : 0<(w^2)^((ν+1)/2+1/2) := Real.rpow_pos_of_pos hw2 _
  have hq : 0<((ν+1)/2+(tEVArg ν r w)^2/2)^((ν+1)/2+1/2) := Real.rpow_pos_of_pos hX _
  field_simp

/-- The Pickands expression for fixed `t`, as a function of the correlation. -/
noncomputable def tEVPickandsExpr (ν r t : ℝ) : ℝ :=
  (1-t)*studentTCDF (ν+1) (tEVArg ν r (((1-t)/t)^(1/ν)))+
    t*studentTCDF (ν+1) (tEVArg ν r ((t/(1-t))^(1/ν)))

theorem tEVPickandsExpr_hasDerivAt (ν t : ℝ) (hν : 0<ν) (_ht : t∈Ioo (0:ℝ) 1) {r : ℝ}
    (hr : r∈Ioo (-1) 1) :
    HasDerivAt (fun q => tEVPickandsExpr ν q t)
      ((1-t)*(studentMarginalPDF (ν+1) (tEVArg ν r (((1-t)/t)^(1/ν)))*
          tEVArgDeriv ν r (((1-t)/t)^(1/ν)))+
        t*(studentMarginalPDF (ν+1) (tEVArg ν r ((t/(1-t))^(1/ν)))*
          tEVArgDeriv ν r ((t/(1-t))^(1/ν)))) r := by
  have hk : (0:ℝ)<ν+1 := by linarith
  have hA := ((studentTCDF_hasDerivAt (ν+1) hk _).comp r
    (tEVArg_hasDerivAt ν (((1-t)/t)^(1/ν)) hν hr)).const_mul (1-t)
  have hB := ((studentTCDF_hasDerivAt (ν+1) hk _).comp r
    (tEVArg_hasDerivAt ν ((t/(1-t))^(1/ν)) hν hr)).const_mul t
  exact hA.add hB

theorem tEVPickandsExpr_deriv_nonpos (ν t : ℝ) (hν : 0<ν) (ht : t∈Ioo (0:ℝ) 1) {r : ℝ}
    (hr : r∈Ioo (-1) 1) :
    (1-t)*(studentMarginalPDF (ν+1) (tEVArg ν r (((1-t)/t)^(1/ν)))*
          tEVArgDeriv ν r (((1-t)/t)^(1/ν)))+
        t*(studentMarginalPDF (ν+1) (tEVArg ν r ((t/(1-t))^(1/ν)))*
          tEVArgDeriv ν r ((t/(1-t))^(1/ν)))≤0 := by
  have ht1 : 0<1-t := by linarith [ht.2]
  have hq : 0<t/(1-t) := div_pos ht.1 ht1
  set w : ℝ := (t/(1-t))^(1/ν) with hwdef
  have hw : 0<w := Real.rpow_pos_of_pos hq _
  have hinv : ((1-t)/t)^(1/ν)=w⁻¹ := by
    rw [hwdef,← Real.inv_rpow hq.le,inv_div]
  have hwν : w^ν=t/(1-t) := by
    rw [hwdef,← Real.rpow_mul hq.le,one_div_mul_cancel hν.ne',Real.rpow_one]
  have hP : (1-t)*(w^2)^((ν+1)/2+1/2)=t*w^2 := by
    have : (w^2)^((ν+1)/2+1/2)=w^ν*w^2 := by
      rw [← Real.rpow_two,← Real.rpow_mul hw.le,← Real.rpow_add hw]
      congr 1
      ring
    rw [this,hwν]
    field_simp
  rw [hinv,tEV_density_balance ν r w hν hr hw]
  have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hsq : 0<Real.sqrt (1-r^2) := Real.sqrt_pos.mpr hs
  set f := studentMarginalPDF (ν+1) (tEVArg ν r w)
  have hf : 0<f := studentMarginalPDF_pos (by linarith) _
  set K := Real.sqrt (1+ν)/((1-r^2)*Real.sqrt (1-r^2))
  have hK : 0≤K := by positivity
  have hD (τ : ℝ) : tEVArgDeriv ν r τ=K*(r*τ-1) := by
    unfold tEVArgDeriv
    ring
  rw [hD,hD]
  have he : (1-t)*((w^2)^((ν+1)/2+1/2)*f*(K*(r*w⁻¹-1)))+t*(f*(K*(r*w-1)))=
      -(f*K*t*((w-r)^2+(1-r^2))) := by
    have e1 : (1-t)*((w^2)^((ν+1)/2+1/2)*f*(K*(r*w⁻¹-1)))=
        ((1-t)*(w^2)^((ν+1)/2+1/2))*f*(K*(r*w⁻¹-1)) := by ring
    rw [e1,hP]
    field_simp
    ring
  rw [he]
  have : 0≤f*K*t*((w-r)^2+(1-r^2)) := by
    have := ht.1
    positivity
  linarith

theorem tEVPickandsExpr_antitoneOn (ν t : ℝ) (hν : 0<ν) (ht : t∈Ioo (0:ℝ) 1) :
    AntitoneOn (fun r => tEVPickandsExpr ν r t) (Ioo (-1) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo (-1) 1)
  · intro r hr
    exact (tEVPickandsExpr_hasDerivAt ν t hν ht hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact (tEVPickandsExpr_hasDerivAt ν t hν ht hr).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    rw [(tEVPickandsExpr_hasDerivAt ν t hν ht hr).deriv]
    exact tEVPickandsExpr_deriv_nonpos ν t hν ht hr

theorem tEV_pickands_eq_expr (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) (t : I)
    (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
    copulaPickands (tEV ν r hν ⟨hr.1.le,hr.2.le⟩) t=tEVPickandsExpr ν r t :=
  tEV_pickands_formula ν r hν hr t ht

theorem tEV_pickands_antitone (ν r q : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) (hq : q∈Ioo (-1) 1)
    (hrq : r≤q) (t : I) (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
    copulaPickands (tEV ν q hν ⟨hq.1.le,hq.2.le⟩) t≤copulaPickands (tEV ν r hν ⟨hr.1.le,hr.2.le⟩) t := by
  rw [tEV_pickands_eq_expr ν q hν hq t ht,tEV_pickands_eq_expr ν r hν hr t ht]
  exact tEVPickandsExpr_antitoneOn ν t hν ht hr hq hrq

/-! ## Diagonal, extremal coefficient and tails -/

theorem tEVArg_one (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) :
    tEVArg ν r 1=Real.sqrt ((ν+1)*(1-r)/(1+r)) := by
  have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have h1 : 0<1+r := by linarith [hr.1]
  have h2 : 0<1-r := by linarith [hr.2]
  have he : (ν+1)*(1-r)/(1+r)=(1+ν)/(1-r^2)*(1-r)^2 := by
    field_simp
    ring
  unfold tEVArg
  rw [he,Real.sqrt_mul (by positivity),Real.sqrt_sq h2.le]

theorem tEVArg_one_pos (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) : 0<tEVArg ν r 1 := by
  have h1 : 0<1+r := by linarith [hr.1]
  have h2 : 0<1-r := by linarith [hr.2]
  rw [tEVArg_one ν r hν hr]
  exact Real.sqrt_pos.mpr (by positivity)

theorem tEVArg_one_strictAntiOn (ν : ℝ) (hν : 0<ν) :
    StrictAntiOn (fun r => tEVArg ν r 1) (Ioo (-1) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (-1) 1)
  · intro r hr
    exact (tEVArg_hasDerivAt ν 1 hν hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    rw [(tEVArg_hasDerivAt ν 1 hν hr).deriv]
    have hs : 0<1-r^2 := by nlinarith [hr.1,hr.2]
    have hsq : 0<Real.sqrt (1-r^2) := Real.sqrt_pos.mpr hs
    have h1 : 0<Real.sqrt (1+ν) := Real.sqrt_pos.mpr (by linarith)
    unfold tEVArgDeriv
    apply mul_neg_of_pos_of_neg h1
    apply div_neg_of_neg_of_pos (by linarith [hr.2]) (by positivity)

theorem tEV_pickands_half (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) :
    copulaPickands (tEV ν r hν ⟨hr.1.le,hr.2.le⟩) unitHalf=studentTCDF (ν+1) (tEVArg ν r 1) := by
  rw [tEV_pickands_formula ν r hν hr unitHalf (by norm_num [unitHalf])]
  norm_num [unitHalf]
  ring

theorem tEV_extremalCoefficient (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) :
    (tEV ν r hν ⟨hr.1.le,hr.2.le⟩).extremalCoefficient=2*studentTCDF (ν+1) (tEVArg ν r 1) := by
  rw [extremalCoefficient_eq_twice_pickands _ (tEV_isExtremeValue ν r hν ⟨hr.1.le,hr.2.le⟩),tEV_pickands_half ν r hν hr]

theorem tEV_tails (ν r : ℝ) (hν : 0<ν) (hr : r∈Ioo (-1) 1) :
    (tEV ν r hν ⟨hr.1.le,hr.2.le⟩).HasLowerTailDependence 0 ∧
    (tEV ν r hν ⟨hr.1.le,hr.2.le⟩).HasUpperTailDependence
      (2-2*studentTCDF (ν+1) (tEVArg ν r 1)) := by
  have hp := (tEV_isExtremeValue ν r hν ⟨hr.1.le,hr.2.le⟩).hasPowerDiagonal
  rw [tEV_extremalCoefficient ν r hν hr] at hp
  have h := studentTCDF_strictMono (ν+1) (by linarith) (tEVArg_one_pos ν r hν hr)
  rw [studentTCDF_zero (ν+1) (by linarith)] at h
  exact ⟨hp.hasLowerTailDependence_zero (by linarith),hp.hasUpperTailDependence⟩

end Verification
