import Verification.Nelsen17Tails
import Mathlib.Analysis.SpecificLimits.Basic

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem n17_diagonal_lower_bound {θ : ℝ} (hθ : 1 ≤ θ) (t : I) :
    (1+(t:ℝ))*(4:ℝ)^(-θ⁻¹)-1 ≤ (nelsen17 θ (by linarith)).diagonal t := by
  have hp : 0 < θ := by linarith
  let x : ℝ := (1+(t:ℝ))^(-θ)
  let z : ℝ := (2:ℝ)^(-θ)
  have hx : 0 < x := Real.rpow_pos_of_pos (by linarith [t.property.1]) _
  have hz : 0 < z := Real.rpow_pos_of_pos (by norm_num) _
  have hzx : z ≤ x := Real.rpow_le_rpow_of_nonpos (by linarith [t.property.1] : 0 < 1+(t:ℝ))
    (by linarith [t.property.2] : 1+(t:ℝ) ≤ 2) (by linarith : -θ ≤ 0)
  have hx1 : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [t.property.1]) (by linarith)
  have hz1 : z ≤ 1/2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (show -θ ≤ -1 by linarith)
    simpa only [Real.rpow_neg_one,one_div] using hh
  have hd : 0 < 1-z := by linarith
  let B : ℝ := 1-(x-1)^2/(1-z)
  have hBx : x ≤ B := by
    dsimp [B]
    have hh : (x-1)^2/(1-z) ≤ 1-x := (div_le_iff₀ hd).mpr (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hzx)])
    linarith
  have hB : 0 < B := hx.trans_le hBx
  have hB4 : B ≤ 4*x := by
    dsimp [B]
    have hh : 1-4*x ≤ (x-1)^2/(1-z) := (le_div_iff₀ hd).mpr (by
      nlinarith [sq_nonneg x, mul_nonneg hx.le (show 0 ≤ 1/2-z by linarith)])
    linarith
  have hh := Real.rpow_le_rpow_of_nonpos hB hB4 (neg_nonpos.mpr (inv_pos.mpr hp).le)
  have hpow : (4*x)^(-θ⁻¹) = (4:ℝ)^(-θ⁻¹)*(1+(t:ℝ)) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hx.le]
    dsimp [x]
    rw [← Real.rpow_mul (by linarith [t.property.1] : 0 ≤ 1+(t:ℝ)),
      show -θ * -θ⁻¹ = 1 by field_simp, Real.rpow_one]
  rw [hpow] at hh
  rw [← n17Diagonal_eq]
  have he : 1+((1+(t:ℝ))^(-θ)-1)^2/n17A (-θ) = B := by
    rw [show n17A (-θ) = -(1-z) by dsimp [n17A,z]; ring, div_neg]
    rfl
  unfold n17Diagonal
  rw [he,inv_neg]
  nlinarith

theorem nelsen17_cdf_lower_bound {θ : ℝ} (hθ : 1 ≤ θ) (u v : I) :
    (1+(min u v:ℝ))*(4:ℝ)^(-θ⁻¹)-1 ≤ (nelsen17 θ (by linarith)).cdf ![u,v] := by
  have hh := n17_diagonal_lower_bound hθ (min u v)
  apply hh.trans
  apply (nelsen17 θ (by linarith)).monotone_cdf
  intro i
  fin_cases i
  · exact min_le_left u v
  · exact min_le_right u v

theorem nelsen17_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, θ a ≠ 0) (ht : Tendsto θ l atTop) (u v : I) :
    Tendsto (fun a => (nelsen17 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((comonotonic 2).cdf ![u,v])) := by
  have hi : Tendsto (fun a => -(θ a)⁻¹) l (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,neg_zero] using (tendsto_inv_atTop_zero.comp ht).neg
  have hp : Tendsto (fun a => (4:ℝ)^(-(θ a)⁻¹)) l (𝓝 (1:ℝ)) := by
    simpa only [Real.rpow_zero] using tendsto_const_nhds.rpow hi (Or.inl (by norm_num : (4:ℝ) ≠ 0))
  have hlo : Tendsto (fun a => (1+(min u v:ℝ))*(4:ℝ)^(-(θ a)⁻¹)-1) l
      (𝓝 (min u v:ℝ)) := by simpa using (hp.const_mul (1+(min u v:ℝ))).sub_const 1
  have he : (comonotonic 2).cdf ![u,v] = (min u v:ℝ) := by rw [cdf_comonotonic_two]; rfl
  rw [he]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [ht.eventually (eventually_ge_atTop (1:ℝ))] with a ha
    exact nelsen17_cdf_lower_bound ha u v
  · exact Eventually.of_forall fun a => le_min ((nelsen17 (θ a) (hθ a)).cdf_le_coord ![u,v] 0)
      ((nelsen17 (θ a) (hθ a)).cdf_le_coord ![u,v] 1)

end Verification
