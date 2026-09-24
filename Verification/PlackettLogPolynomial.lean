import Verification.PlackettAnalytic
import Mathlib.Data.Fin.VecNotation

open Set

namespace Verification

/-- Numerator of the mixed log-density derivative after extracting theta-1. -/
def plackettLogPolynomial (p u v : ℝ) : ℝ :=
  (p+2)*plackettD (p+1) u v*(3*(1+p*(u+v-2*u*v))^2-plackettD (p+1) u v)+
    6*p*(1+p*(u+v-2*u*v))^2*(plackettA (p+1) u v-2*(p+1)*u)*
      (plackettA (p+1) u v-2*(p+1)*v)

/-- Integer coefficients in the unnormalized tensor Bernstein basis of degrees (5,4,4). -/
def plackettLogCoefficients : Fin 6 → Fin 5 → Fin 5 → ℝ :=
  ![
    ![![4,16,24,16,4],
      ![16,64,96,64,16],
      ![24,96,144,96,24],
      ![16,64,96,64,16],
      ![4,16,24,16,4]],
    ![![28,116,180,124,32],
      ![116,472,720,488,124],
      ![180,720,1080,720,180],
      ![124,488,720,472,116],
      ![32,124,180,116,28]],
    ![![72,324,528,372,96],
      ![324,1384,2168,1480,372],
      ![528,2168,3280,2168,528],
      ![372,1480,2168,1384,324],
      ![96,372,528,324,72]],
    ![![88,436,756,536,128],
      ![436,2004,3276,2244,536],
      ![756,3276,5040,3276,756],
      ![536,2244,3276,2004,436],
      ![128,536,756,436,88]],
    ![![52,284,528,368,64],
      ![284,1424,2476,1712,368],
      ![528,2476,3896,2476,528],
      ![368,1712,2476,1424,284],
      ![64,368,528,284,52]],
    ![![12,72,144,96,0],
      ![72,396,744,528,96],
      ![144,744,1200,744,144],
      ![96,528,744,396,72],
      ![0,96,144,72,12]]]

theorem plackettLogCoefficients_nonneg (i : Fin 6) (j k : Fin 5) :
    0 ≤ plackettLogCoefficients i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [plackettLogCoefficients]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem plackettLogPolynomial_certificate (p u v : ℝ) :
    plackettLogPolynomial p u v =
      ∑ i : Fin 6, ∑ j : Fin 5, ∑ k : Fin 5,
        plackettLogCoefficients i j k*p^(i:ℕ)*(1-p)^(5-(i:ℕ))*
          u^(j:ℕ)*(1-u)^(4-(j:ℕ))*v^(k:ℕ)*(1-v)^(4-(k:ℕ)) := by
  norm_num [Fin.sum_univ_succ,plackettLogCoefficients,plackettLogPolynomial,plackettD,plackettA]
  ring

theorem plackettLogPolynomial_nonneg {p u v : ℝ}
    (hp : p ∈ Icc 0 1) (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) :
    0 ≤ plackettLogPolynomial p u v := by
  rw [plackettLogPolynomial_certificate]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro k _
  have hc := plackettLogCoefficients_nonneg i j k
  have hp0 := hp.1
  have hp1 := sub_nonneg.mpr hp.2
  have hu0 := hu.1
  have hu1 := sub_nonneg.mpr hu.2
  have hv0 := hv.1
  have hv1 := sub_nonneg.mpr hv.2
  positivity

end Verification
