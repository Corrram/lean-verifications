import Copula.Classical.Bivariate
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

open ProbabilityTheory Set
open scoped unitInterval

namespace Verification

def plackettA (θ u v : ℝ) := 1+(θ-1)*(u+v)
def plackettD (θ u v : ℝ) := (plackettA θ u v)^2-4*θ*(θ-1)*u*v
noncomputable def plackettF (θ u v : ℝ) :=
  (plackettA θ u v-Real.sqrt (plackettD θ u v))/(2*(θ-1))
noncomputable def plackettP (θ u v : ℝ) :=
  (1-(plackettA θ u v-2*θ*v)/Real.sqrt (plackettD θ u v))/2
noncomputable def plackettDensity (θ u v : ℝ) :=
  θ*(1+(θ-1)*(u+v-2*u*v))/(Real.sqrt (plackettD θ u v))^3

theorem plackettD_pos {θ u v : ℝ} (hθ : 0 < θ) (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) :
    0 < plackettD θ u v := by
  by_cases hp : 1 ≤ θ
  · have he : plackettD θ u v = (1+(θ-1)*(u-v))^2+4*(θ-1)*v*(1-u) := by
      unfold plackettD plackettA; ring
    rw [he]
    have hn : 0 ≤ 4*(θ-1)*v*(1-u) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp)) hv.1) (sub_nonneg.mpr hu.2)
    by_cases hs : 1+(θ-1)*(u-v) = 0
    · have hp' : 0 < θ-1 := by
        have : θ-1 ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
        exact lt_of_le_of_ne (sub_nonneg.mpr hp) (Ne.symm this)
      have hv' : 0 < v := by
        by_contra hh
        have hz : v=0 := le_antisymm (le_of_not_gt hh) hv.1
        rw [hz] at hs
        nlinarith [mul_nonneg hp'.le hu.1]
      have hu' : 0 < 1-u := by
        by_contra hh
        have hz : u=1 := by linarith [hu.2]
        rw [hz] at hs
        nlinarith [mul_nonneg hp'.le (sub_nonneg.mpr hv.2)]
      positivity
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) hn
  · have hn : 0 < 1-θ := by linarith
    have he : plackettD θ u v = (plackettA θ u v)^2+4*θ*(1-θ)*u*v := by
      unfold plackettD; ring
    rw [he]
    by_cases hu0 : u=0
    · subst u
      have hp : 0 < plackettA θ 0 v := by
        unfold plackettA
        nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hv.2)]
      simp only [mul_zero,zero_mul,add_zero]
      exact sq_pos_of_pos hp
    by_cases hv0 : v=0
    · subst v
      have hp : 0 < plackettA θ u 0 := by
        unfold plackettA
        nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hu.2)]
      simp only [mul_zero,add_zero]
      exact sq_pos_of_pos hp
    have hup := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    have hvp := lt_of_le_of_ne hv.1 (Ne.symm hv0)
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)

theorem plackettDensity_nonneg {θ u v : ℝ} (hθ : 0 < θ)
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) : 0 ≤ plackettDensity θ u v := by
  have hs0 : 0 ≤ u+v-2*u*v := by
    nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hv.2),mul_nonneg hv.1 (sub_nonneg.mpr hu.2)]
  have hs1 : u+v-2*u*v ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hv.2),mul_nonneg hu.1 hv.1]
  have hn : 0 ≤ 1+(θ-1)*(u+v-2*u*v) := by
    by_cases ht : 1 ≤ θ
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht) hs0]
    · nlinarith [mul_nonneg (show 0 ≤ 1-θ by linarith) (sub_nonneg.mpr hs1)]
  exact div_nonneg (mul_nonneg hθ.le hn) (pow_nonneg (Real.sqrt_nonneg _) _)

theorem plackettF_deriv {θ u v : ℝ} (hθ : θ ≠ 1) (hD : 0 < plackettD θ u v) :
    HasDerivAt (fun x => plackettF θ x v) (plackettP θ u v) u := by
  have hA : HasDerivAt (fun x => plackettA θ x v) (θ-1) u := by
    convert (((hasDerivAt_id u).add_const v).const_mul (θ-1)).const_add 1 using 1 <;> simp [plackettA]
  have hD' : HasDerivAt (fun x => plackettD θ x v)
      (2*plackettA θ u v*(θ-1)-4*θ*(θ-1)*v) u := by
    convert (hA.pow 2).sub ((hasDerivAt_id u).const_mul (4*θ*(θ-1)*v)) using 1
    · funext x; dsimp [plackettD,plackettA]; ring
    · ring
  have hh := (hA.sub (hD'.sqrt hD.ne')).div_const (2*(θ-1))
  convert hh using 1
  · rfl
  · unfold plackettP
    field_simp [sub_ne_zero.mpr hθ,(Real.sqrt_pos.mpr hD).ne']
    ring

theorem plackettP_deriv {θ u v : ℝ} (hD : 0 < plackettD θ u v) :
    HasDerivAt (plackettP θ u) (plackettDensity θ u v) v := by
  have hA : HasDerivAt (plackettA θ u) (θ-1) v := by
    change HasDerivAt (fun x => 1+(θ-1)*(u+x)) (θ-1) v
    convert (((hasDerivAt_id v).const_add u).const_mul (θ-1)).const_add 1 using 1 <;> simp
  have hD' : HasDerivAt (plackettD θ u)
      (2*plackettA θ u v*(θ-1)-4*θ*(θ-1)*u) v := by
    convert (hA.pow 2).sub ((hasDerivAt_id v).const_mul (4*θ*(θ-1)*u)) using 1
    · rfl
    · ring
  have hh := (((hA.sub ((hasDerivAt_id v).const_mul (2*θ))).div
    (hD'.sqrt hD.ne') (Real.sqrt_pos.mpr hD).ne').const_sub 1).div_const 2
  convert hh using 1
  · rfl
  · unfold plackettDensity
    have hs := Real.sq_sqrt hD.le
    field_simp [(Real.sqrt_pos.mpr hD).ne']
    rw [hs]
    dsimp [plackettD,plackettA]
    ring

end Verification
