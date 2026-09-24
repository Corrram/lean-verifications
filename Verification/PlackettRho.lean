import Verification.PlackettOrder
import Verification.CubeFubini
import Copula.Rank.SpearmanCDF

open MeasureTheory ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

private theorem plackett_inverse_den_pos {θ : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1)
    (u v : I) (hv : 0 < (v : ℝ)) :
    0 < θ * v - (θ - 1) * plackettF θ u v := by
  have he : plackettF θ u v = (plackett θ hθ).cdf ![u,v] :=
    (plackett_cdf hθ hne u v).symm
  rw [he]
  have hc := (plackett θ hθ).cdf_nonneg ![u,v]
  have hb : (plackett θ hθ).cdf ![u,v] ≤ (v : ℝ) :=
    (plackett θ hθ).cdf_le_coord ![u,v] 1
  by_cases hp : 0 ≤ θ - 1
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr hb)]
  · nlinarith [mul_pos hθ hv, mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp) hc]

private noncomputable def plackettPrimitive (θ u v : ℝ) : ℝ :=
  u * plackettF θ u v - (plackettF θ u v)^2 / 2 +
    (1-v) * plackettF θ u v / (θ-1) +
    θ*v*(1-v)/(θ-1)^2 * Real.log (θ*v-(θ-1)*plackettF θ u v)

private theorem plackettPrimitive_deriv {θ : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1)
    (u v : I) (hv : 0 < (v : ℝ)) :
    HasDerivAt (fun x => plackettPrimitive θ x v) (plackettF θ u v) u := by
  have hc := plackettF_deriv hne (plackettD_pos hθ u.property v.property)
  have hd := plackett_inverse_den_pos hθ hne u v hv
  have hd' : θ*(v:ℝ)-plackettF θ u v*(θ-1) ≠ 0 := by
    simpa only [mul_comm (θ-1)] using hd.ne'
  have hl := ((hasDerivAt_const (u:ℝ) (θ*(v:ℝ))).sub
    (hc.const_mul (θ-1))).log hd.ne'
  have hh := (((hasDerivAt_id (u:ℝ)).mul hc).sub ((hc.pow 2).div_const 2)).add
    ((hc.const_mul (1-(v:ℝ))).div_const (θ-1))
  have hh' := hh.add (hl.const_mul (θ*(v:ℝ)*(1-v)/(θ-1)^2))
  have ho := plackett_odds_equation hθ u v
  have he : (plackett θ hθ).cdf ![u,v] = plackettF θ u v := plackett_cdf hθ hne u v
  rw [he] at ho
  convert hh' using 1
  · funext x
    rfl
  · simp only [id, Pi.sub_apply, Nat.cast_ofNat, show (2:ℕ)-1=1 from rfl, pow_one,
      one_mul, zero_sub]
    change plackettF θ u v = plackettF θ u v + (u:ℝ)*plackettP θ u v -
      2*plackettF θ u v*plackettP θ u v/2 +
      (1-(v:ℝ))*plackettP θ u v/(θ-1) +
      θ*(v:ℝ)*(1-v)/(θ-1)^2 *
        (-((θ-1)*plackettP θ u v)/(θ*(v:ℝ)-(θ-1)*plackettF θ u v))
    field_simp [sub_ne_zero.mpr hne, hd.ne', hd']
    field_simp [hd']
    linear_combination (-(θ-1) * plackettP θ u v) * ho

theorem integral_plackett_section {θ : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1) (v : I) :
    (∫ u : I, (plackett θ hθ).cdf ![u,v]) =
      (v:ℝ) - (v:ℝ)^2/2 - (v:ℝ)*(1-v)*(θ*Real.log θ-θ+1)/(θ-1)^2 := by
  by_cases hv : (v:ℝ) = 0
  · have hv' : v = 0 := Subtype.ext hv
    subst v
    simp
  have hvp : 0 < (v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm hv)
  have he (u : I) : (plackett θ hθ).cdf ![u,v] = plackettF θ u v :=
    plackett_cdf hθ hne u v
  simp_rw [he]
  rw [Copula.integral_unitInterval (fun u => plackettF θ u v)]
  have hc : ContinuousOn (fun u => plackettF θ u v) (uIcc 0 1) := by
    unfold plackettF plackettD plackettA
    fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u (hu : u ∈ uIcc (0:ℝ) 1) =>
      plackettPrimitive_deriv hθ hne ⟨u, by simpa only [uIcc_of_le zero_le_one] using hu⟩ v hvp)
    hc.intervalIntegrable
  rw [hh]
  unfold plackettPrimitive
  rw [plackettF_one hθ hne v.property, plackettF_zero hθ v.property]
  have hd : θ*(v:ℝ)-(θ-1)*v = v := by ring
  rw [hd]
  simp only [mul_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), zero_div, zero_add]
  rw [Real.log_mul hθ.ne' hv]
  field_simp
  ring

theorem integral_plackett_cdf {θ : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1) :
    (∫ x : Fin 2 → I, (plackett θ hθ).cdf x) =
      1/3 - (θ*Real.log θ-θ+1)/(6*(θ-1)^2) := by
  have hi := (plackett θ hθ).integrable_cdf volume
  have he := integral_cube_Iic_iterated hi 1 1
  have htop : Iic (![(1:I),1]) = Set.univ := by
    ext x
    simp only [mem_Iic, mem_univ, iff_true, Pi.le_def, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨(x 0).property.2, (x 1).property.2⟩
  simp only [htop, Measure.restrict_univ, show Iic (1:I) = Set.univ from Set.Iic_top] at he
  have hs (u v : I) : (plackett θ hθ).cdf ![u,v] = (plackett θ hθ).cdf ![v,u] := by
    rw [plackett_cdf hθ hne, plackett_cdf hθ hne]
    exact plackettF_symm θ u v
  rw [he]
  have hs' (u : I) : (∫ v : I, (plackett θ hθ).cdf ![u,v]) =
      (u:ℝ)-(u:ℝ)^2/2-(u:ℝ)*(1-u)*(θ*Real.log θ-θ+1)/(θ-1)^2 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun v => hs u v))]
    exact integral_plackett_section hθ hne u
  simp_rw [hs']
  let k := (θ*Real.log θ-θ+1)/(θ-1)^2
  have hp (u : I) : (u:ℝ)-(u:ℝ)^2/2-(u:ℝ)*(1-u)*(θ*Real.log θ-θ+1)/(θ-1)^2 =
      (1-k)*(u:ℝ)+(k-1/2)*(u:ℝ)^2 := by dsimp [k]; ring
  simp_rw [hp]
  have hi1 : Integrable (fun u : I => (u:ℝ)) :=
    Copula.integrable_continuous_unit volume continuous_subtype_val
  have hi2 : Integrable (fun u : I => (u:ℝ)^2) :=
    Copula.integrable_continuous_unit volume (continuous_subtype_val.pow 2)
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
    integral_const_mul, Copula.integral_unit_id, Copula.integral_unit_pow]
  dsimp [k]
  field_simp [sub_ne_zero.mpr hne]
  ring

/-- Spearman rho obtained by integration of the actual Plackett CDF. -/
theorem plackett_spearmanRho {θ : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1) :
    (plackett θ hθ).spearmanRho =
      (θ+1)/(θ-1)-2*θ*Real.log θ/(θ-1)^2 := by
  rw [Copula.spearmanRho_eq_integral_cdf, Copula.toMeasure_independence]
  change 12*(∫ x : Fin 2 → I, (plackett θ hθ).cdf x)-3 = _
  rw [integral_plackett_cdf hθ hne]
  field_simp [sub_ne_zero.mpr hne]
  ring

theorem plackett_spearmanRho_one : (plackett 1 (by norm_num)).spearmanRho = 0 := by
  rw [plackett_one, Copula.spearmanRho_independence]

/-- The doubled logarithmic term printed in arXiv v3 Table 6 fails already at theta=2. -/
theorem plackett_printed_rho_false :
    (plackett 2 (by norm_num)).spearmanRho ≠
      ((2:ℝ)+1)/(2-1)-2*(2*2/(2-1)^2)*Real.log 2 := by
  rw [plackett_spearmanRho (by norm_num) (by norm_num)]
  norm_num

end Verification
