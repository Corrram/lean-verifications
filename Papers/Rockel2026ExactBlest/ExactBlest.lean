import Verification.Blest.RightBoundary
import Copula.OrdinalSum.Measure
import Verification.AxiomAudit
import Mathlib.Tactic

/-!
# Checks for exact-blest-regions.tex

The population coefficient below is the CDF-based Blest coefficient from the
pinned supplement, not a new moment-only surrogate. See COVERAGE.md for the
mapping from manuscript claims to their checked formal statements.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest

noncomputable section

noncomputable def eta (C : Copula 2) : ℝ := (blestNu C + blestNu C.transpose) / 2

theorem eta_transpose (C : Copula 2) : eta C.transpose = eta C := by
  simp only [eta, Copula.transpose_transpose]
  ring

theorem nu_transpose (C : Copula 2) : blestNu C.transpose = 2 * eta C - blestNu C := by
  unfold eta
  ring

theorem eta_mix (C D : Copula 2) (t : I) :
    eta (C.mix D t) = (t : ℝ) * eta C + (1 - (t : ℝ)) * eta D := by
  simp only [eta, Copula.transpose_mix, blest_mix]
  ring

theorem eta_mem_Icc (C : Copula 2) : eta C ∈ Icc (-1) 1 := by
  have h := blest_mem_Icc C
  have ht := blest_mem_Icc C.transpose
  constructor <;> dsimp [eta] <;> linarith [h.1, h.2, ht.1, ht.2]

theorem nu_survival (C : Copula 2) :
    blestNu C.survivalCopula = 2 * C.spearmanRho - blestNu C := by
  have h := blest_eq_rho_of_radiallySymmetric (C.mix C.survivalCopula Copula.unitHalf)
    (Copula.isRadiallySymmetric_symmetrize C)
  rw [blest_mix, Copula.spearmanRho_mix, Copula.spearmanRho_survivalCopula] at h
  dsimp [Copula.unitHalf] at h
  linarith

theorem eta_survival (C : Copula 2) :
    eta C.survivalCopula = 2 * C.spearmanRho - eta C := by
  simp only [eta, Copula.transpose_survivalCopula, nu_survival,
    Copula.spearmanRho_transpose]
  ring

theorem nu_reflect_first (C : Copula 2) :
    blestNu (C.reflect {0}) = blestNu C - 2 * C.spearmanRho := by
  have h := blest_reflect_second (C.reflect {0})
  rw [Copula.reflect_first_second, nu_survival] at h
  linarith

theorem eta_reflect_second (C : Copula 2) :
    eta (C.reflect {1}) = -C.spearmanRho + (blestNu C.transpose - blestNu C) / 2 := by
  have h : (C.reflect {1}).transpose = C.transpose.reflect {0} := by
    have h := Copula.transpose_reflect_first C.transpose
    rw [Copula.transpose_transpose] at h
    exact congrArg Copula.transpose h.symm |>.trans (Copula.transpose_transpose _)
  simp only [eta, h, blest_reflect_second, nu_reflect_first, Copula.spearmanRho_transpose]
  ring

theorem reflection_byproduct (C : Copula 2) :
    blestNu (C.reflect {1}) - eta (C.reflect {1}) = C.spearmanRho - eta C := by
  rw [blest_reflect_second, eta_reflect_second]
  unfold eta
  ring

theorem asymmetry_identity (C : Copula 2) :
    |blestNu C - blestNu C.transpose| = 2 * |blestNu C - eta C| := by
  have h : blestNu C - blestNu C.transpose = 2 * (blestNu C - eta C) := by
    unfold eta
    ring
  rw [h, abs_mul]
  norm_num

theorem support_identity (C : Copula 2) (k : ℝ) :
    (1 + k) * blestNu C - 2 * k * eta C = blestNu C - k * blestNu C.transpose := by
  unfold eta
  ring

theorem integral_weighted_upper_indicator (u : I) :
    (∫ t : I, if u ≤ t then 1 - (t : ℝ) else 0) = (1 - (u : ℝ)) ^ 2 / 2 := by
  classical
  have hs := unitInterval.measurePreserving_symm.integral_comp
    unitInterval.symmMeasurableEquiv.measurableEmbedding
    (fun t : I => if u ≤ t then 1 - (t : ℝ) else 0)
  rw [← hs]
  have he : (fun t : I => if u ≤ unitInterval.symm t then 1 - (unitInterval.symm t : ℝ) else 0) =
      fun t : I => (Set.indicator {s : ℝ | s ≤ 1 - (u : ℝ)} (fun s => s)) t := by
    funext t
    have h : u ≤ unitInterval.symm t ↔ (t : ℝ) ≤ 1 - (u : ℝ) := by
      change (u : ℝ) ≤ 1 - (t : ℝ) ↔ _
      constructor <;> intro h <;> linarith
    simp [h, Set.indicator, unitInterval.coe_symm_eq]
  rw [he, Copula.integral_unitInterval,
    intervalIntegral.integral_indicator (show 1 - (u : ℝ) ∈ Icc (0 : ℝ) 1 from
      ⟨by linarith [u.property.2], by linarith [u.property.1]⟩), integral_id]
  ring

theorem nu_moment (C : Copula 2) :
    blestNu C = 12 * (∫ y, (1 - (y 0 : ℝ)) ^ 2 * (1 - (y 1 : ℝ)) ∂C.toMeasure) - 2 := by
  classical
  have hf : Integrable (fun p : (Fin 2 → I) × (Fin 2 → I) =>
      if p.2 ≤ p.1 then 1 - (p.1 0 : ℝ) else 0)
      ((Copula.independence 2).toMeasure.prod C.toMeasure) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((by fun_prop : Measurable (fun p : (Fin 2 → I) × (Fin 2 → I) =>
        1 - (p.1 0 : ℝ))).ite (measurableSet_le measurable_snd measurable_fst)
          measurable_const).aestronglyMeasurable
    · split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(p.1 0).property.2])]
        linarith [(p.1 0).property.1]
      · norm_num
  have hc (x : Fin 2 → I) : (1 - (x 0 : ℝ)) * C.cdf x =
      ∫ y, if y ≤ x then 1 - (x 0 : ℝ) else 0 ∂C.toMeasure := by
    have hi : C.cdf x = ∫ y, if y ≤ x then (1 : ℝ) else 0 ∂C.toMeasure := by
      symm
      simpa [Set.indicator, Copula.cdf] using
        integral_indicator_one (μ := C.toMeasure) (s := Iic x) measurableSet_Iic
    rw [hi, ← integral_const_mul]
    congr 1
    funext y
    split_ifs <;> ring
  have hi (y : Fin 2 → I) :
      (∫ x, if y ≤ x then 1 - (x 0 : ℝ) else 0 ∂(Copula.independence 2).toMeasure) =
        (1 - (y 0 : ℝ)) ^ 2 / 2 * (1 - (y 1 : ℝ)) := by
    have he : (fun x : Fin 2 → I => if y ≤ x then 1 - (x 0 : ℝ) else 0) =
        fun x => (if y 0 ≤ x 0 then 1 - (x 0 : ℝ) else 0) *
          (if y 1 ≤ x 1 then (1 : ℝ) else 0) := by
      funext x
      simp only [Pi.le_def, Fin.forall_fin_two]
      by_cases h0 : y 0 ≤ x 0 <;> by_cases h1 : y 1 ≤ x 1 <;> simp [h0, h1]
    rw [he, Copula.integral_independence_mul
      (fun t : I => if y 0 ≤ t then 1 - (t : ℝ) else 0)
      (fun t : I => if y 1 ≤ t then (1 : ℝ) else 0),
      integral_weighted_upper_indicator, Copula.integral_unit_upper_indicator]
  have h := calc
    (∫ x, (1 - (x 0 : ℝ)) * C.cdf x ∂(Copula.independence 2).toMeasure) =
        ∫ x, ∫ y, if y ≤ x then 1 - (x 0 : ℝ) else 0 ∂C.toMeasure
          ∂(Copula.independence 2).toMeasure := by simp_rw [hc]
    _ = ∫ y, ∫ x, if y ≤ x then 1 - (x 0 : ℝ) else 0
          ∂(Copula.independence 2).toMeasure ∂C.toMeasure := integral_integral_swap hf
    _ = ∫ y, (1 - (y 0 : ℝ)) ^ 2 / 2 * (1 - (y 1 : ℝ)) ∂C.toMeasure := by simp_rw [hi]
    _ = (∫ y, (1 - (y 0 : ℝ)) ^ 2 * (1 - (y 1 : ℝ)) ∂C.toMeasure) / 2 := by
      simp_rw [div_mul_eq_mul_div]
      exact integral_div 2 _
  unfold blestNu
  rw [h]
  ring

theorem nu_transpose_moment (C : Copula 2) :
    blestNu C.transpose = 12 * (∫ y, (1 - (y 0 : ℝ)) * (1 - (y 1 : ℝ)) ^ 2 ∂C.toMeasure) - 2 := by
  rw [nu_moment, C.integral_transpose _ (by fun_prop)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm]

theorem eta_moment (C : Copula 2) :
    eta C = 6 * (∫ y, (1 - (y 0 : ℝ)) * (1 - (y 1 : ℝ)) *
      ((1 - (y 0 : ℝ)) + (1 - (y 1 : ℝ))) ∂C.toMeasure) - 2 := by
  have he : (fun y : Fin 2 → I => (1 - (y 0 : ℝ)) * (1 - (y 1 : ℝ)) *
      ((1 - (y 0 : ℝ)) + (1 - (y 1 : ℝ)))) =
      fun y => (1 - (y 0 : ℝ)) ^ 2 * (1 - (y 1 : ℝ)) +
        (1 - (y 0 : ℝ)) * (1 - (y 1 : ℝ)) ^ 2 := by funext y; ring
  rw [eta, nu_moment, nu_transpose_moment, he, integral_add]
  · ring
  all_goals exact Copula.integrable_continuous_cube _ (by fun_prop)

theorem support_moment (C : Copula 2) (k : ℝ) :
    (1 + k) * blestNu C - 2 * k * eta C =
      12 * (∫ y, (1 - (y 0 : ℝ)) ^ 2 * (1 - (y 1 : ℝ)) -
        k * (1 - (y 0 : ℝ)) * (1 - (y 1 : ℝ)) ^ 2 ∂C.toMeasure) - 2 * (1 - k) := by
  rw [support_identity, nu_moment, nu_transpose_moment]
  simp_rw [mul_assoc k]
  rw [integral_sub, integral_const_mul]
  · ring
  all_goals exact Copula.integrable_continuous_cube _ (by fun_prop)

#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_transpose
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_mix
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_mem_Icc
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_survival
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_survival
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_reflect_first
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_reflect_second
#assert_standard_axioms Papers.Rockel2026ExactBlest.reflection_byproduct
#assert_standard_axioms Papers.Rockel2026ExactBlest.asymmetry_identity
#assert_standard_axioms Papers.Rockel2026ExactBlest.support_identity
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_weighted_upper_indicator
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_moment
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_moment
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_moment
#assert_standard_axioms Papers.Rockel2026ExactBlest.support_moment

/-! Explicit antiderivatives for the two transport certificates. -/

def cost (k x z : ℝ) : ℝ := x ^ 2 * z - k * x * z ^ 2
def antiPhi (k x : ℝ) : ℝ := -k * x + (1 + k) * x ^ 2 - (2 + k) * x ^ 3 / 3
def linearPsi (k m b z : ℝ) : ℝ :=
  (m ^ 2 - 2 * k * m) * z ^ 3 / 3 + b * (m - k) * z ^ 2 + b ^ 2 * z
def kA (w : ℝ) : ℝ := (1 + 2 * w) / (2 * (1 - w))
def phiA0 (w x : ℝ) : ℝ := antiPhi (kA w) x - antiPhi (kA w) w
def graphPhi (w x : ℝ) : ℝ :=
  (2 - kA w) * x ^ 3 / 3 + w * (kA w - 1) * x ^ 2 - kA w * w ^ 2 * x
def phiA1 (w x : ℝ) : ℝ := graphPhi w x - graphPhi w w
def psiA0 (w z : ℝ) : ℝ := linearPsi (kA w) 1 w z
def psiA1 (w z : ℝ) : ℝ :=
  psiA0 w (1 - w) + linearPsi (kA w) (-1) 1 z - linearPsi (kA w) (-1) 1 (1 - w)
def phiA (w x : ℝ) : ℝ := if x ≤ w then phiA0 w x else phiA1 w x
def psiA (w z : ℝ) : ℝ := if z ≤ 1 - w then psiA0 w z else psiA1 w z

set_option maxHeartbeats 800000

theorem slackA00 (w x z : ℝ) (hw : w ≠ 1) :
    phiA0 w x + psiA0 w z - cost (kA w) x z =
      w * z ^ 2 * (1 - w - z) / (1 - w) +
      ((1 - w - z) * ((1 - 2 * w) * (1 - w) + z * (2 * w + 1)) * (w - x) +
        (((1 - 2 * w) * (1 - w) + z * (2 * w + 1)) + (1 - w - z) * (5 - 2 * w)) *
          (w - x) ^ 2 / 2 + (5 - 2 * w) * (w - x) ^ 3 / 3) / (2 * (1 - w)) := by
  unfold phiA0 psiA0 antiPhi linearPsi cost kA
  field_simp
  ring

theorem slackA01 (w x z : ℝ) (hw : w ≠ 1) :
    phiA0 w x + psiA1 w z - cost (kA w) x z =
      (x + z - 1) ^ 2 * (3 * (1 - w) + (5 - 2 * w) * (w - x) +
        (2 * w + 4) * (z - (1 - w))) / (6 * (1 - w)) := by
  unfold phiA0 psiA1 psiA0 antiPhi linearPsi cost kA
  field_simp
  ring

theorem slackA10 (w x z : ℝ) (hw : w ≠ 1) :
    phiA1 w x + psiA0 w z - cost (kA w) x z =
      (x - w - z) ^ 2 * (2 * w * (1 - w - z) + (x - w) * (1 - 2 * w)) /
        (2 * (1 - w)) := by
  unfold phiA1 graphPhi psiA0 linearPsi cost kA
  field_simp
  ring

theorem slackA11 (w x z : ℝ) (hw : w ≠ 1) :
    phiA1 w x + psiA1 w z - cost (kA w) x z =
      (x - w) * (1 - 2 * w) * (1 - x) ^ 2 / (2 * (1 - w)) +
      ((x - w) * ((1 - w) * (1 + w - x)) * (z - (1 - w)) +
        ((1 - w) * (1 + w - x) + (x - w) * (w + 2)) * (z - (1 - w)) ^ 2 / 2 +
        (w + 2) * (z - (1 - w)) ^ 3 / 3) / (1 - w) := by
  unfold phiA1 graphPhi psiA1 psiA0 linearPsi cost kA
  field_simp
  ring

theorem dualA (w x z : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 2)
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    cost (kA w) x z ≤ phiA w x + psiA w z := by
  have hw : w ≠ 1 := by linarith
  have hden : 0 < 1 - w := by linarith
  have hw2 : 0 ≤ 1 - 2 * w := by linarith
  have hw5 : 0 ≤ 5 - 2 * w := by linarith
  have hwx : 0 ≤ 1 + w - x := by linarith [hx.2]
  have hz0 := hz.1
  suffices h : 0 ≤ phiA w x + psiA w z - cost (kA w) x z by linarith
  unfold phiA psiA
  split_ifs with hxx hzz hzz
  · rw [slackA00 w x z hw]
    have hy : 0 ≤ w - x := sub_nonneg.mpr hxx
    have ht : 0 ≤ 1 - w - z := by linarith
    positivity
  · rw [slackA01 w x z hw]
    have hy : 0 ≤ w - x := sub_nonneg.mpr hxx
    have ht : 0 ≤ z - (1 - w) := by linarith
    positivity
  · rw [slackA10 w x z hw]
    have hy : 0 ≤ x - w := by linarith
    have ht : 0 ≤ 1 - w - z := by linarith
    positivity
  · rw [slackA11 w x z hw]
    have hy : 0 ≤ x - w := by linarith
    have ht : 0 ≤ z - (1 - w) := by linarith
    positivity

#assert_standard_axioms Papers.Rockel2026ExactBlest.slackA00
#assert_standard_axioms Papers.Rockel2026ExactBlest.slackA01
#assert_standard_axioms Papers.Rockel2026ExactBlest.slackA10
#assert_standard_axioms Papers.Rockel2026ExactBlest.slackA11
#assert_standard_axioms Papers.Rockel2026ExactBlest.dualA

def kB (a : ℝ) : ℝ := 2 * a / (1 - a)
def cutB (a : ℝ) : ℝ := (1 - a) / (2 * a)
def phiB0 (a x : ℝ) : ℝ := antiPhi (kB a) x - antiPhi (kB a) a
def splitPhi (a x : ℝ) : ℝ := x ^ 3 / (3 * a) - x ^ 2 / 2 - kB a * (x - a) ^ 3 / (12 * a ^ 2)
def phiB1 (a x : ℝ) : ℝ := splitPhi a x - splitPhi a a
def psiB0 (a z : ℝ) : ℝ := linearPsi (kB a) (2 * a) a z
def psiB1 (a z : ℝ) : ℝ := psiB0 a (cutB a) +
  linearPsi (kB a) (-2 * a / (2 * a - 1)) (a / (2 * a - 1)) z -
  linearPsi (kB a) (-2 * a / (2 * a - 1)) (a / (2 * a - 1)) (cutB a)
def psiB2 (a z : ℝ) : ℝ := psiB1 a (1 - a) +
  linearPsi (kB a) (-1) 1 z - linearPsi (kB a) (-1) 1 (1 - a)
def phiB (a x : ℝ) : ℝ := if x ≤ a then phiB0 a x else phiB1 a x
def psiB (a z : ℝ) : ℝ :=
  if z ≤ cutB a then psiB0 a z else if z ≤ 1 - a then psiB1 a z else psiB2 a z

theorem slackB00 (a x z : ℝ) (ha : a ≠ 1) :
    phiB0 a x + psiB0 a z - cost (kB a) x z =
      2 * a * z ^ 2 * ((1 - a) * (2 * a - 1) + (1 + a) * (1 - a - 2 * a * z)) /
        (3 * (1 - a)) +
      2 * ((1 - a - z) * a * z * (a - x) +
        (1 - a - z + a * z) * (a - x) ^ 2 / 2 + (a - x) ^ 3 / 3) / (1 - a) := by
  unfold phiB0 psiB0 antiPhi linearPsi cost kB
  field_simp
  ring

theorem slackB01 (a x z : ℝ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : 2 * a - 1 ≠ 0) :
    phiB0 a x + psiB1 a z - cost (kB a) x z =
      2 * a * (1 - a - z) ^ 2 *
        ((1 - a) * (2 * a - 1) + (3 * a - 1) * (2 * a * z - (1 - a))) /
        (3 * (1 - a) * (2 * a - 1) ^ 2) +
      2 * ((1 - a - z) * a * z * (a - x) +
        (1 - a - z + a * z) * (a - x) ^ 2 / 2 + (a - x) ^ 3 / 3) / (1 - a) := by
  unfold phiB0 psiB1 psiB0 cutB antiPhi linearPsi cost kB
  field_simp
  ring

theorem slackB02 (a x z : ℝ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : 2 * a - 1 ≠ 0) :
    phiB0 a x + psiB2 a z - cost (kB a) x z =
      (x + z - 1) ^ 2 * (3 * a * (1 - a) + 2 * (a - x) + (3 * a + 1) * (z - (1 - a))) /
        (3 * (1 - a)) := by
  unfold phiB0 psiB2 psiB1 psiB0 cutB antiPhi linearPsi cost kB
  field_simp
  ring

theorem slackB10 (a x z : ℝ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    phiB1 a x + psiB0 a z - cost (kB a) x z =
      (x - 2 * a * z - a) ^ 2 *
        ((2 * a - 1) * (1 - x) + (1 + a) * (1 - a - 2 * a * z)) / (6 * a * (1 - a)) := by
  unfold phiB1 splitPhi psiB0 linearPsi cost kB
  field_simp
  ring

theorem slackB11 (a x z : ℝ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : 2 * a - 1 ≠ 0) :
    phiB1 a x + psiB1 a z - cost (kB a) x z =
      (x * (2 * a - 1) + 2 * a * z - a) ^ 2 *
        ((2 * a - 1) * (1 - x) + (3 * a - 1) * (2 * a * z - (1 - a))) /
        (6 * a * (1 - a) * (2 * a - 1) ^ 2) := by
  calc
    _ = (phiB0 a x + psiB1 a z - cost (kB a) x z) + (phiB1 a x - phiB0 a x) := by ring
    _ = _ := by
      rw [slackB01 a x z ha0 ha1 ha2]
      unfold phiB1 splitPhi phiB0 antiPhi kB
      field_simp
      ring

theorem slackB12 (a x z : ℝ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : 2 * a - 1 ≠ 0) :
    phiB1 a x + psiB2 a z - cost (kB a) x z =
      (z - (1 - a)) ^ 2 * (3 * a * (1 - a) + (3 * a + 1) * (z - (1 - a))) /
        (3 * (1 - a)) +
      ((2 * a * z - (x - a)) * (2 * a * (z - (1 - a))) * (x - a) +
        (2 * a * (z - (1 - a)) + (2 * a * z - (x - a)) * (2 * a - 1)) * (x - a) ^ 2 / 2 +
        (2 * a - 1) * (x - a) ^ 3 / 6) / (2 * a * (1 - a)) := by
  calc
    _ = (phiB0 a x + psiB2 a z - cost (kB a) x z) + (phiB1 a x - phiB0 a x) := by ring
    _ = _ := by
      rw [slackB02 a x z ha0 ha1 ha2]
      unfold phiB1 splitPhi phiB0 antiPhi kB
      field_simp
      ring

theorem dualB (a x z : ℝ) (ha0 : 1 / 2 < a) (ha1 : a < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    cost (kB a) x z ≤ phiB a x + psiB a z := by
  have ha : 0 < a := by linarith
  have hn0 : a ≠ 0 := ne_of_gt ha
  have hn1 : a ≠ 1 := ne_of_lt ha1
  have ha2 : 0 < 2 * a - 1 := by linarith
  have hn2 := ne_of_gt ha2
  have ha3 : 0 < 3 * a - 1 := by linarith
  have hden : 0 < 1 - a := by linarith
  have hxa : 0 ≤ 1 - x := by linarith [hx.2]
  have hz0 := hz.1
  have hcut : cutB a ≤ 1 - a := by
    unfold cutB
    apply (div_le_iff₀ (by positivity : 0 < 2 * a)).2
    nlinarith [mul_nonneg (le_of_lt hden) (le_of_lt ha2)]
  suffices h : 0 ≤ phiB a x + psiB a z - cost (kB a) x z by linarith
  unfold phiB psiB
  split_ifs with hxx hzcut hzmid hzcut hzmid
  · rw [slackB00 a x z hn1]
    have hy : 0 ≤ a - x := by linarith
    have ht : 0 ≤ 1 - a - z := by linarith
    have hr : 0 ≤ 1 - a - 2 * a * z := by
      have := (le_div_iff₀ (by positivity : 0 < 2 * a)).mp hzcut
      nlinarith
    positivity
  · rw [slackB01 a x z hn0 hn1 hn2]
    have hy : 0 ≤ a - x := by linarith
    have ht : 0 ≤ 1 - a - z := by linarith
    have hr : 0 ≤ 2 * a * z - (1 - a) := by
      have := (div_lt_iff₀ (by positivity : 0 < 2 * a)).mp (lt_of_not_ge hzcut)
      nlinarith
    positivity
  · rw [slackB02 a x z hn0 hn1 hn2]
    have hy : 0 ≤ a - x := by linarith
    have ht : 0 ≤ z - (1 - a) := by linarith
    positivity
  · rw [slackB10 a x z hn0 hn1]
    have hr : 0 ≤ 1 - a - 2 * a * z := by
      have := (le_div_iff₀ (by positivity : 0 < 2 * a)).mp hzcut
      nlinarith
    positivity
  · rw [slackB11 a x z hn0 hn1 hn2]
    have hr : 0 ≤ 2 * a * z - (1 - a) := by
      have := (div_lt_iff₀ (by positivity : 0 < 2 * a)).mp (lt_of_not_ge hzcut)
      nlinarith
    positivity
  · rw [slackB12 a x z hn0 hn1 hn2]
    have hy : 0 ≤ x - a := by linarith
    have ht : 0 ≤ z - (1 - a) := by linarith
    have hr : 0 ≤ 2 * a * z - (x - a) := by
      nlinarith [mul_nonneg (le_of_lt ha2) (le_of_lt hden), mul_nonneg (le_of_lt ha) ht, hx.2]
    positivity

#assert_standard_axioms Papers.Rockel2026ExactBlest.slackB00
#assert_standard_axioms Papers.Rockel2026ExactBlest.slackB01
#assert_standard_axioms Papers.Rockel2026ExactBlest.slackB02
#assert_standard_axioms Papers.Rockel2026ExactBlest.slackB10
#assert_standard_axioms Papers.Rockel2026ExactBlest.slackB11
#assert_standard_axioms Papers.Rockel2026ExactBlest.slackB12
#assert_standard_axioms Papers.Rockel2026ExactBlest.dualB

theorem integral_poly3 (A B D E l r : ℝ) :
    (∫ x in l..r, A * x ^ 3 + B * x ^ 2 + D * x + E) =
      A * (r ^ 4 - l ^ 4) / 4 + B * (r ^ 3 - l ^ 3) / 3 +
        D * (r ^ 2 - l ^ 2) / 2 + E * (r - l) := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · simp only [intervalIntegral.integral_const_mul, integral_pow,
      intervalIntegral.integral_const, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul D (fun x : ℝ => x), integral_id]
    norm_num
    ring
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _

theorem integral_unit_piecewise (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ u : I, if (u : ℝ) ≤ t then f u else g u) =
      (∫ x in (0 : ℝ)..t, f x) + ∫ x in t..1, g x := by
  classical
  have he : (fun u : I => if (u : ℝ) ≤ t then f u else g u) =
      fun u : I => g u + (Set.indicator {x : ℝ | x ≤ t} (fun x => f x - g x)) u := by
    funext u
    by_cases h : (u : ℝ) ≤ t <;> simp [h, Set.indicator]
  have hgi : Integrable (fun u : I => g u) := Copula.integrable_continuous_unit _ (by fun_prop)
  have hfi : Integrable (fun u : I =>
      (Set.indicator {x : ℝ | x ≤ t} (fun x => f x - g x)) u) := by
    exact (Copula.integrable_continuous_unit _ (show Continuous (fun u : I => f u - g u) by
      fun_prop)).indicator (measurableSet_le measurable_subtype_coe measurable_const)
  rw [he, integral_add hgi hfi, Copula.integral_unitInterval g,
    Copula.integral_unitInterval, intervalIntegral.integral_indicator ht,
    intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable (0 : ℝ) t) (hg.intervalIntegrable t 1)
  linarith

theorem integral_phiA_quarter : (∫ u : I, phiA (1 / 4) u) = 115 / 1536 := by
  have he : (fun u : I => phiA (1 / 4) u) = fun u : I =>
      if (u : ℝ) ≤ 1 / 4 then (-1 : ℝ) * (u : ℝ) ^ 3 + 2 * (u : ℝ) ^ 2 + (-1) * (u : ℝ) + 9 / 64
      else (1 / 3 : ℝ) * (u : ℝ) ^ 3 + 0 * (u : ℝ) ^ 2 + (-1 / 16) * (u : ℝ) + 1 / 96 := by
    funext u
    unfold phiA
    split_ifs <;> norm_num [phiA0, phiA1, graphPhi, antiPhi, kA] <;> ring
  rw [he, integral_unit_piecewise
    (fun x : ℝ => (-1) * x ^ 3 + 2 * x ^ 2 + (-1) * x + 9 / 64)
    (fun x : ℝ => (1 / 3) * x ^ 3 + 0 * x ^ 2 + (-1 / 16) * x + 1 / 96)
    (by fun_prop) (by fun_prop) _ (by norm_num),
    integral_poly3, integral_poly3]
  norm_num

theorem integral_psiA_quarter : (∫ u : I, psiA (1 / 4) u) = -61 / 1536 := by
  have he : (fun u : I => psiA (1 / 4) u) = fun u : I =>
      if (u : ℝ) ≤ 3 / 4 then (-1 / 3 : ℝ) * (u : ℝ) ^ 3 + 0 * (u : ℝ) ^ 2 + (1 / 16) * (u : ℝ) + 0
      else (1 : ℝ) * (u : ℝ) ^ 3 + (-2) * (u : ℝ) ^ 2 + 1 * (u : ℝ) + (-9 / 64) := by
    funext u
    unfold psiA
    norm_num
    split_ifs <;> norm_num [psiA0, psiA1, linearPsi, kA] <;> ring
  rw [he, integral_unit_piecewise
    (fun x : ℝ => (-1 / 3) * x ^ 3 + 0 * x ^ 2 + (1 / 16) * x + 0)
    (fun x : ℝ => 1 * x ^ 3 + (-2) * x ^ 2 + 1 * x + (-9 / 64))
    (by fun_prop) (by fun_prop) _ (by norm_num),
    integral_poly3, integral_poly3]
  norm_num

theorem integrable_phiA (C : Copula 2) (w : ℝ) (i : Fin 2) :
    Integrable (fun x => phiA w (x i)) C.toMeasure := by
  classical
  exact Integrable.piecewise
    (measurableSet_le (show Measurable (fun x : Fin 2 → I => (x i : ℝ)) by fun_prop) measurable_const)
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I => phiA0 w (x i)) by
      unfold phiA0 antiPhi; fun_prop)).integrableOn
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I => phiA1 w (x i)) by
      unfold phiA1 graphPhi; fun_prop)).integrableOn

theorem integrable_psiA (C : Copula 2) (w : ℝ) (i : Fin 2) :
    Integrable (fun x => psiA w (x i)) C.toMeasure := by
  classical
  exact Integrable.piecewise
    (measurableSet_le (show Measurable (fun x : Fin 2 → I => (x i : ℝ)) by fun_prop) measurable_const)
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I => psiA0 w (x i)) by
      unfold psiA0 linearPsi; fun_prop)).integrableOn
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I => psiA1 w (x i)) by
      unfold psiA1 linearPsi; fun_prop)).integrableOn

theorem measurable_phiA (w : ℝ) : Measurable (fun u : I => phiA w u) := by
  exact (show Measurable (fun u : I => phiA0 w u) by unfold phiA0 antiPhi; fun_prop).ite
    (measurableSet_le measurable_subtype_coe measurable_const)
    (show Measurable (fun u : I => phiA1 w u) by unfold phiA1 graphPhi; fun_prop)

theorem measurable_psiA (w : ℝ) : Measurable (fun u : I => psiA w u) := by
  exact (show Measurable (fun u : I => psiA0 w u) by unfold psiA0 linearPsi; fun_prop).ite
    (measurableSet_le measurable_subtype_coe measurable_const)
    (show Measurable (fun u : I => psiA1 w u) by unfold psiA1 linearPsi; fun_prop)

theorem transport_asymmetry_upper (C : Copula 2) :
    (∫ x, cost 1 (x 0) (x 1) ∂C.toMeasure) ≤ 9 / 256 := by
  have h := integral_mono
    (Copula.integrable_continuous_cube C.toMeasure (show Continuous (fun x : Fin 2 → I =>
      cost 1 (x 0) (x 1)) by unfold cost; fun_prop))
    ((integrable_phiA C (1 / 4) 0).add (integrable_psiA C (1 / 4) 1))
    (fun x => by
      have hd := dualA (1 / 4) (x 0) (x 1) (by norm_num) (by norm_num) (x 0).property (x 1).property
      norm_num [kA] at hd
      exact hd)
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_phiA C (1 / 4) 0) (integrable_psiA C (1 / 4) 1),
    C.integral_eval 0 _ (measurable_phiA _), C.integral_eval 1 _ (measurable_psiA _),
    integral_phiA_quarter, integral_psiA_quarter] at h
  linarith

theorem support_moment_survival (C : Copula 2) (k : ℝ) :
    (1 + k) * blestNu C - 2 * k * eta C =
      12 * (∫ y, cost k (y 0) (y 1) ∂C.survivalCopula.toMeasure) - 2 * (1 - k) := by
  rw [Copula.survivalCopula, C.integral_reflect _ _ (by unfold cost; fun_prop)]
  simp only [Copula.reflectPoint, Finset.mem_univ, ite_true, unitInterval.coe_symm_eq, cost]
  exact support_moment C k

/-- The universal inequality, for the original CDF coefficient, not just its boundary formula.
Attainment and uniqueness are separate obligations; see COVERAGE.md. -/
theorem nu_eta_upper (C : Copula 2) : blestNu C - eta C ≤ 27 / 128 := by
  have h := transport_asymmetry_upper C.survivalCopula
  have hs := support_moment_survival C 1
  norm_num at hs
  linarith

theorem nu_eta_bound (C : Copula 2) : |blestNu C - eta C| ≤ 27 / 128 := by
  have hu := nu_eta_upper C
  have hl := nu_eta_upper C.transpose
  rw [eta_transpose, nu_transpose] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

theorem nu_transpose_bound (C : Copula 2) : |blestNu C - blestNu C.transpose| ≤ 27 / 64 := by
  rw [asymmetry_identity]
  linarith [nu_eta_bound C]

theorem rho_eta_bound (C : Copula 2) : |C.spearmanRho - eta C| ≤ 27 / 128 := by
  have h := nu_eta_bound (C.reflect {1})
  rwa [reflection_byproduct] at h

#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_poly3
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_unit_piecewise
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_phiA_quarter
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_psiA_quarter
#assert_standard_axioms Papers.Rockel2026ExactBlest.integrable_phiA
#assert_standard_axioms Papers.Rockel2026ExactBlest.integrable_psiA
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_phiA
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_psiA
#assert_standard_axioms Papers.Rockel2026ExactBlest.transport_asymmetry_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.support_moment_survival
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_eta_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_eta_bound
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_bound
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_eta_bound

def rhoPhi (x : ℝ) : ℝ := (4 / 3) * |x - 1 / 2| ^ 3
def rhoPsi (z : ℝ) : ℝ := z ^ 3 / 12 - z / 4

theorem rho_slack (x z : ℝ) :
    rhoPhi x + rhoPsi z - (x ^ 2 - x) * z =
      (z - 2 * |x - 1 / 2|) ^ 2 * (z + 4 * |x - 1 / 2|) / 12 := by
  calc
    _ = (z ^ 3 - 12 * |x - 1 / 2| ^ 2 * z + 16 * |x - 1 / 2| ^ 3) / 12 := by
      rw [sq_abs]
      unfold rhoPhi rhoPsi
      ring
    _ = _ := by ring

theorem rho_dual (x z : ℝ) (hz : 0 ≤ z) : (x ^ 2 - x) * z ≤ rhoPhi x + rhoPsi z := by
  have h : 0 ≤ rhoPhi x + rhoPsi z - (x ^ 2 - x) * z := by
    rw [rho_slack]
    positivity
  linarith

theorem integral_rhoPhi : (∫ u : I, rhoPhi u) = 1 / 24 := by
  have he : (fun u : I => rhoPhi u) = fun u : I =>
      if (u : ℝ) ≤ 1 / 2 then (-4 / 3 : ℝ) * (u : ℝ) ^ 3 + 2 * (u : ℝ) ^ 2 + (-1) * (u : ℝ) + 1 / 6
      else (4 / 3 : ℝ) * (u : ℝ) ^ 3 + (-2) * (u : ℝ) ^ 2 + 1 * (u : ℝ) + (-1 / 6) := by
    funext u
    unfold rhoPhi
    split_ifs with h
    · rw [abs_of_nonpos (by linarith : (u : ℝ) - 1 / 2 ≤ 0)]
      ring
    · rw [abs_of_nonneg (by linarith : 0 ≤ (u : ℝ) - 1 / 2)]
      ring
  rw [he, integral_unit_piecewise
    (fun x : ℝ => (-4 / 3) * x ^ 3 + 2 * x ^ 2 + (-1) * x + 1 / 6)
    (fun x : ℝ => (4 / 3) * x ^ 3 + (-2) * x ^ 2 + 1 * x + (-1 / 6))
    (by fun_prop) (by fun_prop) _ (by norm_num), integral_poly3, integral_poly3]
  norm_num

theorem integral_rhoPsi : (∫ u : I, rhoPsi u) = -5 / 48 := by
  have he : rhoPsi = fun x : ℝ => (1 / 12) * x ^ 3 + 0 * x ^ 2 + (-1 / 4) * x + 0 := by
    funext x
    unfold rhoPsi
    ring
  rw [he, Copula.integral_unitInterval
    (fun x : ℝ => (1 / 12) * x ^ 3 + 0 * x ^ 2 + (-1 / 4) * x + 0), integral_poly3]
  norm_num

theorem transport_rho_upper (C : Copula 2) :
    (∫ x, ((x 0 : ℝ) ^ 2 - (x 0 : ℝ)) * (x 1 : ℝ) ∂C.toMeasure) ≤ -1 / 16 := by
  have hp : Integrable (fun x : Fin 2 → I => rhoPhi (x 0)) C.toMeasure :=
    Copula.integrable_continuous_cube _ (by unfold rhoPhi; fun_prop)
  have hq : Integrable (fun x : Fin 2 → I => rhoPsi (x 1)) C.toMeasure :=
    Copula.integrable_continuous_cube _ (by unfold rhoPsi; fun_prop)
  have h := integral_mono (Copula.integrable_continuous_cube C.toMeasure (by fun_prop))
    (hp.add hq) (fun x => rho_dual (x 0) (x 1) (x 1).property.1)
  simp only [Pi.add_apply] at h
  rw [integral_add hp hq,
    C.integral_eval 0 (fun u : I => rhoPhi u) (by unfold rhoPhi; fun_prop),
    C.integral_eval 1 (fun u : I => rhoPsi u) (by unfold rhoPsi; fun_prop), integral_rhoPhi, integral_rhoPsi] at h
  linarith

theorem nu_rho_moment (C : Copula 2) :
    blestNu C - C.spearmanRho =
      12 * (∫ x, ((x 0 : ℝ) ^ 2 - (x 0 : ℝ)) * (x 1 : ℝ) ∂C.survivalCopula.toMeasure) + 1 := by
  have hn := support_moment_survival C 0
  norm_num [cost] at hn
  have hr : C.spearmanRho =
      12 * (∫ x, (x 0 : ℝ) * (x 1 : ℝ) ∂C.survivalCopula.toMeasure) - 3 := by
    rw [← Copula.spearmanRho_survivalCopula C]
    rfl
  rw [hn, hr]
  simp_rw [sub_mul]
  rw [integral_sub]
  · ring
  all_goals exact Copula.integrable_continuous_cube _ (by fun_prop)

theorem nu_rho_upper (C : Copula 2) : blestNu C - C.spearmanRho ≤ 1 / 4 := by
  rw [nu_rho_moment]
  linarith [transport_rho_upper C.survivalCopula]

theorem nu_rho_bound (C : Copula 2) : |blestNu C - C.spearmanRho| ≤ 1 / 4 := by
  have hu := nu_rho_upper C
  have hl := nu_rho_upper C.survivalCopula
  rw [nu_survival, Copula.spearmanRho_survivalCopula] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

def betaUpper (b : ℝ) : ℝ := 1 - (3 / 16) * (1 - b) ^ 3
def betaLower (b : ℝ) : ℝ := -1 + (3 / 16) * (1 + b) ^ 3

theorem beta_width (b : ℝ) : betaUpper b - betaLower b = (13 - 9 * b ^ 2) / 8 := by
  unfold betaUpper betaLower
  ring

/-- Scalar consequence of the cubic boundaries; this is not the copula region theorem. -/
theorem beta_scalar_bound (b n : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1)
    (hn : n ∈ Icc (betaLower b) (betaUpper b)) : |n - b| ≤ 8 / 9 := by
  have h1 : 0 ≤ (3 * b + 1) ^ 2 * (11 - 3 * b) :=
    mul_nonneg (sq_nonneg _) (by linarith [hb.2])
  have h2 : 0 ≤ (3 * b - 1) ^ 2 * (11 + 3 * b) :=
    mul_nonneg (sq_nonneg _) (by linarith [hb.1])
  dsimp [betaUpper, betaLower] at hn
  exact abs_le.mpr ⟨by nlinarith [hn.1], by nlinarith [hn.2]⟩

theorem graph_gap_max (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
    2 * w * (1 - w) ^ 3 ≤ 27 / 128 := by
  have h : 0 ≤ (4 * w - 1) ^ 2 * (16 * (1 - w) ^ 2 + 8 * (1 - w) + 3) :=
    mul_nonneg (sq_nonneg _) (by nlinarith [sq_nonneg (1 - w), hw.2])
  nlinarith

theorem graph_gap_max_iff (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
    2 * w * (1 - w) ^ 3 = 27 / 128 ↔ w = 1 / 4 := by
  constructor
  · intro h
    have hp : 0 < 16 * (1 - w) ^ 2 + 8 * (1 - w) + 3 := by
      nlinarith [sq_nonneg (1 - w), hw.2]
    have hz : (4 * w - 1) ^ 2 * (16 * (1 - w) ^ 2 + 8 * (1 - w) + 3) = 0 := by nlinarith
    have hs : (4 * w - 1) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hp)
    nlinarith [sq_nonneg (4 * w - 1)]
  · rintro rfl
    norm_num

#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_slack
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_dual
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_rhoPhi
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_rhoPsi
#assert_standard_axioms Papers.Rockel2026ExactBlest.transport_rho_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_rho_moment
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_rho_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_rho_bound
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_width
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_scalar_bound
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_gap_max
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_gap_max_iff

theorem integral_unit_poly3 (A B D E : ℝ) :
    (∫ u : I, A * (u : ℝ) ^ 3 + B * (u : ℝ) ^ 2 + D * (u : ℝ) + E) =
      A / 4 + B / 3 + D / 2 + E := by
  rw [Copula.integral_unitInterval (fun x : ℝ => A * x ^ 3 + B * x ^ 2 + D * x + E), integral_poly3]
  norm_num

/-- The paper's A_w in original coordinates, constructed as an actual library copula.
Its reflected-coordinate coupling is supported on z=1-x below w and z=x-w above w. -/
def familyA (w : I) : Copula 2 :=
  ((Copula.comonotonic 2).ordinalSum Copula.countermonotonic w).reflect {0}

theorem nu_familyA (w : I) : blestNu (familyA w) = 2 * (1 + (w : ℝ)) * (1 - (w : ℝ)) ^ 3 - 1 := by
  rw [nu_moment]
  unfold familyA
  rw [Copula.integral_reflect _ _ _ (by fun_prop)]
  simp only [Copula.reflectPoint, Finset.mem_singleton, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false, unitInterval.coe_symm_eq, sub_sub_cancel]
  rw [Copula.integral_ordinalSum _ _ _ (by fun_prop),
    Copula.integral_comonotonic _ (by fun_prop), Copula.integral_countermonotonic _ (by fun_prop)]
  simp only [Copula.OrdinalSum.lowerEmbed, Copula.OrdinalSum.upperEmbed,
    Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq]
  have h0 : (fun u : I => ((w : ℝ) * (u : ℝ)) ^ 2 * (1 - (w : ℝ) * (u : ℝ))) =
      fun u : I => (-(w : ℝ) ^ 3) * (u : ℝ) ^ 3 + (w : ℝ) ^ 2 * (u : ℝ) ^ 2 + 0 * (u : ℝ) + 0 := by
    funext u; ring
  have h1 : (fun u : I => ((w : ℝ) + (1 - (w : ℝ)) * (u : ℝ)) ^ 2 *
      (1 - ((w : ℝ) + (1 - (w : ℝ)) * (1 - (u : ℝ))))) =
      fun u : I => (1 - (w : ℝ)) ^ 3 * (u : ℝ) ^ 3 +
        (2 * (w : ℝ) * (1 - (w : ℝ)) ^ 2) * (u : ℝ) ^ 2 +
        ((w : ℝ) ^ 2 * (1 - (w : ℝ))) * (u : ℝ) + 0 := by funext u; ring
  rw [h0, h1, integral_unit_poly3, integral_unit_poly3]
  ring

theorem nu_transpose_familyA (w : I) :
    blestNu (familyA w).transpose = 2 * (1 - (w : ℝ)) ^ 4 - 1 := by
  rw [nu_transpose_moment]
  unfold familyA
  rw [Copula.integral_reflect _ _ _ (by fun_prop)]
  simp only [Copula.reflectPoint, Finset.mem_singleton, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false, unitInterval.coe_symm_eq, sub_sub_cancel]
  rw [Copula.integral_ordinalSum _ _ _ (by fun_prop),
    Copula.integral_comonotonic _ (by fun_prop), Copula.integral_countermonotonic _ (by fun_prop)]
  simp only [Copula.OrdinalSum.lowerEmbed, Copula.OrdinalSum.upperEmbed,
    Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq]
  have h0 : (fun u : I => (w : ℝ) * (u : ℝ) * (1 - (w : ℝ) * (u : ℝ)) ^ 2) =
      fun u : I => (w : ℝ) ^ 3 * (u : ℝ) ^ 3 + (-2 * (w : ℝ) ^ 2) * (u : ℝ) ^ 2 +
        (w : ℝ) * (u : ℝ) + 0 := by funext u; ring
  have h1 : (fun u : I => ((w : ℝ) + (1 - (w : ℝ)) * (u : ℝ)) *
      (1 - ((w : ℝ) + (1 - (w : ℝ)) * (1 - (u : ℝ)))) ^ 2) =
      fun u : I => (1 - (w : ℝ)) ^ 3 * (u : ℝ) ^ 3 +
        ((w : ℝ) * (1 - (w : ℝ)) ^ 2) * (u : ℝ) ^ 2 + 0 * (u : ℝ) + 0 := by funext u; ring
  rw [h0, h1, integral_unit_poly3, integral_unit_poly3]
  ring

theorem eta_familyA (w : I) : eta (familyA w) = 2 * (1 - (w : ℝ)) ^ 3 - 1 := by
  rw [eta, nu_familyA, nu_transpose_familyA]
  ring

def quarter : I := ⟨1 / 4, by norm_num⟩

theorem quarter_values : eta (familyA quarter) = -5 / 32 ∧ blestNu (familyA quarter) = 7 / 128 := by
  rw [eta_familyA, nu_familyA]
  norm_num [quarter]

theorem asymmetry_attained : ∃ C : Copula 2, blestNu C - eta C = 27 / 128 := by
  refine ⟨familyA quarter, ?_⟩
  rw [quarter_values.1, quarter_values.2]
  norm_num

theorem asymmetry_lower_attained : ∃ C : Copula 2, blestNu C - eta C = -27 / 128 := by
  refine ⟨(familyA quarter).transpose, ?_⟩
  rw [eta_transpose, nu_transpose, quarter_values.1, quarter_values.2]
  norm_num

theorem transposition_attained : ∃ C : Copula 2, |blestNu C - blestNu C.transpose| = 27 / 64 := by
  obtain ⟨C, h⟩ := asymmetry_attained
  refine ⟨C, ?_⟩
  rw [asymmetry_identity, h]
  norm_num

theorem rho_eta_attained : ∃ C : Copula 2, C.spearmanRho - eta C = 27 / 128 := by
  obtain ⟨C, h⟩ := asymmetry_attained
  refine ⟨C.reflect {1}, ?_⟩
  have hr := reflection_byproduct (C.reflect {1})
  rw [Copula.reflect_reflect] at hr
  linarith

#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_unit_poly3
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_familyA
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_familyA
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_familyA
#assert_standard_axioms Papers.Rockel2026ExactBlest.quarter_values
#assert_standard_axioms Papers.Rockel2026ExactBlest.asymmetry_attained
#assert_standard_axioms Papers.Rockel2026ExactBlest.asymmetry_lower_attained
#assert_standard_axioms Papers.Rockel2026ExactBlest.transposition_attained
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_eta_attained

end
end Papers.Rockel2026ExactBlest
