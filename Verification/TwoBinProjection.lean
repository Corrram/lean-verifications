import Verification.StepDensity
import Copula.Rank.ConditionalDerivative

/-! # Two-bin Jensen inequality as an exact squared-distance identity -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def twoBin (v : I) (a b : ℝ) (u : I) : ℝ := b + (a - b) * lowerStep v u

theorem twoBin_eq (v : I) (a b : ℝ) (u : I) :
    twoBin v a b u = if u ≤ v then a else b := by
  unfold twoBin lowerStep
  split_ifs <;> ring

theorem integrable_twoBin (v : I) (a b : ℝ) : Integrable (twoBin v a b) :=
  (integrable_const b).add ((integrable_lowerStep v).const_mul _)

theorem integral_twoBin_Iic (v : I) (a b : ℝ) (u : I) :
    (∫ t in Iic u, twoBin v a b t) = b * (u : ℝ) + (a - b) * min (u : ℝ) v := by
  unfold twoBin
  rw [integral_add (integrable_const _) ((integrable_lowerStep v).const_mul _).integrableOn,
    integral_const_mul, integral_lowerStep]
  simp only [setIntegral_const, smul_eq_mul, Measure.real, unitInterval.volume_Iic,
    ENNReal.toReal_ofReal u.property.1]
  ring

theorem integral_twoBin (v : I) (a b : ℝ) :
    (∫ u : I, twoBin v a b u) = (v : ℝ) * a + (1 - v) * b := by
  have hs : (∫ u : I, lowerStep v u) = (v : ℝ) := by
    have h := integral_lowerStep v 1
    have ht : Iic (1 : I) = univ := by ext u; simp [unitInterval.le_one']
    rw [ht, setIntegral_univ] at h
    change (∫ u : I, lowerStep v u) = min (1 : ℝ) v at h
    simpa only [min_eq_right v.property.2] using h
  unfold twoBin
  rw [integral_add (integrable_const _) ((integrable_lowerStep v).const_mul _), integral_const_mul, hs]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

theorem twoBin_sq (v : I) (a b : ℝ) :
    (fun u => twoBin v a b u ^ 2) = twoBin v (a ^ 2) (b ^ 2) := by
  funext u
  simp only [twoBin_eq]
  split_ifs <;> rfl

theorem integrable_mul_twoBin {g : I → ℝ} (hg : Integrable g) (v : I) (a b : ℝ) :
    Integrable (fun u => g u * twoBin v a b u) := by
  have hid : (fun u => g u * twoBin v a b u) =
      fun u => b * g u + (a - b) * (Iic v).indicator g u := by
    funext u
    by_cases hu : u ≤ v
    · simp [twoBin_eq, hu, mem_Iic.mpr hu]; ring
    · simp [twoBin_eq, hu, show u ∉ Iic v from hu, mul_comm]
  rw [hid]
  exact (hg.const_mul b).add ((hg.indicator measurableSet_Iic).const_mul _)

theorem integral_mul_twoBin {g : I → ℝ} (hg : Integrable g) (v : I) (a b : ℝ) :
    (∫ u : I, g u * twoBin v a b u) = b * (∫ u : I, g u) + (a - b) * ∫ u in Iic v, g u := by
  have hid : (fun u => g u * twoBin v a b u) =
      fun u => b * g u + (a - b) * (Iic v).indicator g u := by
    funext u
    by_cases hu : u ≤ v
    · simp [twoBin_eq, hu, mem_Iic.mpr hu]; ring
    · simp [twoBin_eq, hu, show u ∉ Iic v from hu, mul_comm]
  rw [hid, integral_add (hg.const_mul b) ((hg.indicator measurableSet_Iic).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator measurableSet_Iic]

theorem twoBin_projection {g : I → ℝ} (hg : Integrable g) (hs : Integrable (fun u => g u ^ 2))
    (v : I) (a b : ℝ) (hm : (∫ u : I, g u) = (v : ℝ) * a + (1 - v) * b)
    (hl : (∫ u in Iic v, g u) = (v : ℝ) * a) :
    Integrable (fun u => (g u - twoBin v a b u) ^ 2) ∧
      (∫ u : I, (g u - twoBin v a b u) ^ 2) =
        (∫ u : I, g u ^ 2) - ((v : ℝ) * a ^ 2 + (1 - v) * b ^ 2) := by
  have ht : Integrable (fun u => twoBin v a b u ^ 2) := by rw [twoBin_sq]; exact integrable_twoBin _ _ _
  have hp := integrable_mul_twoBin hg v a b
  have hh : Integrable (fun u => g u ^ 2 + twoBin v a b u ^ 2) := hs.add ht
  have hid : (fun u => (g u - twoBin v a b u) ^ 2) =
      fun u => g u ^ 2 + twoBin v a b u ^ 2 - 2 * (g u * twoBin v a b u) := by funext u; ring
  constructor
  · rw [hid]
    exact hh.sub (hp.const_mul 2)
  · rw [hid, integral_sub hh (hp.const_mul 2), integral_add hs ht,
      integral_const_mul, integral_mul_twoBin hg, twoBin_sq, integral_twoBin, hm, hl]
    ring

theorem twoBin_jensen {g : I → ℝ} (hg : Integrable g) (hs : Integrable (fun u => g u ^ 2))
    (v : I) (a b : ℝ) (hm : (∫ u : I, g u) = (v : ℝ) * a + (1 - v) * b)
    (hl : (∫ u in Iic v, g u) = (v : ℝ) * a) :
    (v : ℝ) * a ^ 2 + (1 - v) * b ^ 2 ≤ ∫ u : I, g u ^ 2 := by
  have hp := (twoBin_projection hg hs v a b hm hl).2
  have hn : 0 ≤ (∫ u : I, (g u - twoBin v a b u) ^ 2) :=
    integral_nonneg (fun u : I => sq_nonneg (g u - twoBin v a b u))
  linarith

theorem twoBin_jensen_eq_iff {g : I → ℝ} (hg : Integrable g) (hs : Integrable (fun u => g u ^ 2))
    (v : I) (a b : ℝ) (hm : (∫ u : I, g u) = (v : ℝ) * a + (1 - v) * b)
    (hl : (∫ u in Iic v, g u) = (v : ℝ) * a) :
    (∫ u : I, g u ^ 2) = (v : ℝ) * a ^ 2 + (1 - v) * b ^ 2 ↔
      g =ᵐ[volume] twoBin v a b := by
  have hp := twoBin_projection hg hs v a b hm hl
  constructor
  · intro he
    have hz : (∫ u : I, (g u - twoBin v a b u) ^ 2) = 0 := by rw [hp.2, he, sub_self]
    have ha := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) hp.1).mp hz
    filter_upwards [ha] with u hu
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hu)
  · intro he
    have hh : (∫ u : I, g u ^ 2) = ∫ u : I, twoBin v a b u ^ 2 :=
      integral_congr_ae (he.fun_comp (fun z : ℝ => z ^ 2))
    rw [hh, twoBin_sq, integral_twoBin]

end Verification
