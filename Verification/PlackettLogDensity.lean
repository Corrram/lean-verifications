import Verification.PlackettLogPolynomial
import Verification.PlackettDensity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open ProbabilityTheory Set
open scoped unitInterval

namespace Verification

def plackettN (θ u v : ℝ) : ℝ := 1+(θ-1)*(u+v-2*u*v)
noncomputable def plackettLogDensity (θ u v : ℝ) : ℝ :=
  Real.log θ+Real.log (plackettN θ u v)-(3/2:ℝ)*Real.log (plackettD θ u v)
noncomputable def plackettLogScore (θ u v : ℝ) : ℝ :=
  (θ-1)*(1-2*v)/plackettN θ u v-
    3*(θ-1)*(plackettA θ u v-2*θ*v)/plackettD θ u v

theorem plackettN_pos {θ u v : ℝ} (hθ : 1 ≤ θ)
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) : 0 < plackettN θ u v := by
  have hs : 0 ≤ u+v-2*u*v := by
    nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hv.2),mul_nonneg hv.1 (sub_nonneg.mpr hu.2)]
  have hh := mul_nonneg (sub_nonneg.mpr hθ) hs
  unfold plackettN
  linarith

theorem plackettDensity_pos {θ u v : ℝ} (hθ : 1 ≤ θ)
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) : 0 < plackettDensity θ u v :=
  div_pos (mul_pos (by linarith) (plackettN_pos hθ hu hv))
    (pow_pos (Real.sqrt_pos.mpr (plackettD_pos (by linarith) hu hv)) _)

theorem plackettLogDensity_eq {θ u v : ℝ} (hθ : 1 ≤ θ)
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) :
    plackettLogDensity θ u v = Real.log (plackettDensity θ u v) := by
  have hn := plackettN_pos hθ hu hv
  have hd := plackettD_pos (by linarith : 0 < θ) hu hv
  change _ = Real.log (θ*plackettN θ u v/(Real.sqrt (plackettD θ u v))^3)
  rw [Real.log_div (mul_pos (by linarith) hn).ne' (pow_pos (Real.sqrt_pos.mpr hd) 3).ne',
    Real.log_mul (by linarith : θ ≠ 0) hn.ne',Real.log_pow,Real.log_sqrt hd.le]
  unfold plackettLogDensity
  ring

theorem plackettLogDensity_deriv {θ u v : ℝ}
    (hN : 0 < plackettN θ u v) (hD : 0 < plackettD θ u v) :
    HasDerivAt (fun x => plackettLogDensity θ x v) (plackettLogScore θ u v) u := by
  have hn : HasDerivAt (fun x => plackettN θ x v) ((θ-1)*(1-2*v)) u := by
    convert ((((hasDerivAt_id u).add_const v).sub
      ((hasDerivAt_id u).const_mul (2*v))).const_mul (θ-1)).const_add 1 using 1
    · funext x; dsimp [plackettN]; ring
    · ring
  have ha : HasDerivAt (fun x => plackettA θ x v) (θ-1) u := by
    convert (((hasDerivAt_id u).add_const v).const_mul (θ-1)).const_add 1 using 1 <;> simp [plackettA]
  have hd : HasDerivAt (fun x => plackettD θ x v)
      (2*(θ-1)*(plackettA θ u v-2*θ*v)) u := by
    convert (ha.pow 2).sub ((hasDerivAt_id u).const_mul (4*θ*(θ-1)*v)) using 1
    · funext x; dsimp [plackettD]; ring
    · ring
  have hh := ((hn.log hN.ne').const_add (Real.log θ)).sub ((hd.log hD.ne').const_mul (3/2:ℝ))
  convert hh using 1
  · rfl
  · unfold plackettLogScore
    ring

theorem plackettLogScore_deriv {θ u v : ℝ}
    (hN : 0 < plackettN θ u v) (hD : 0 < plackettD θ u v) :
    HasDerivAt (plackettLogScore θ u)
      ((θ-1)*plackettLogPolynomial (θ-1) u v/(plackettN θ u v^2*plackettD θ u v^2)) v := by
  have hn : HasDerivAt (plackettN θ u) ((θ-1)*(1-2*u)) v := by
    convert ((((hasDerivAt_id v).const_add u).sub
      ((hasDerivAt_id v).const_mul (2*u))).const_mul (θ-1)).const_add 1 using 1
    · rfl
    · ring
  have ha : HasDerivAt (plackettA θ u) (θ-1) v := by
    change HasDerivAt (fun x => 1+(θ-1)*(u+x)) (θ-1) v
    convert (((hasDerivAt_id v).const_add u).const_mul (θ-1)).const_add 1 using 1 <;> simp
  have hd : HasDerivAt (plackettD θ u)
      (2*(θ-1)*(plackettA θ u v-2*θ*u)) v := by
    convert (ha.pow 2).sub ((hasDerivAt_id v).const_mul (4*θ*(θ-1)*u)) using 1
    · rfl
    · ring
  have hh := (((((hasDerivAt_id v).const_mul 2).const_sub 1).const_mul (θ-1)).div hn hN.ne').sub
    (((ha.sub ((hasDerivAt_id v).const_mul (2*θ))).const_mul (3*(θ-1))).div hd hD.ne')
  convert hh using 1
  · rfl
  · dsimp [plackettLogPolynomial]
    have he : θ-1+1=θ := by ring
    rw [he]
    change (θ-1)*_/(plackettN θ u v^2*plackettD θ u v^2) = _
    field_simp [hN.ne',hD.ne']
    dsimp [plackettN,plackettD,plackettA]
    ring

end Verification
