import Papers.OrendayLaresRockel2026XiBeta.DExchangeShuffle
import Copula.Symmetry
import Copula.Rank.Basic
import Copula.Dependence.Basic

/-! # Proposition 4.2: the right-boundary copulas `D_b`

`D_b` is the copula of `(U, T_b(U))` (see `dExchange`). This file proves: `T_b` is measure
preserving (`intervalExchange_measurePreserving`), `D_b` is completely dependent with
`ξ(D_b) = 1`, `β(D_b) = b`, `D_b` is exchangeable, radially symmetric, and PQD for `b ≥ 0`.
All statements hold for every `b ∈ [-1, 1]`, including the degenerate cut points
`s_b ∈ {0, 1/2}`.
-/

open MeasureTheory Set ProbabilityTheory
open ProbabilityTheory.Copula.RankRegion.XiBlest.Support
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- `D_b` lives on the graph of `T_b`. -/
theorem dExchange_ae_graph (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    ∀ᵐ x ∂(dExchange b hb).toMeasure, x 1 = intervalExchange b (x 0) := by
  rw [dExchange_eq_shuffle]
  exact exchangeShuffle_ae_graph _

/-- `D_b` is completely dependent: the second coordinate is a.s. a measurable,
Lebesgue-measure-preserving function of the first. -/
theorem dExchange_completelyDependent (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    ∃ f : I → I, Measurable f ∧ MeasurePreserving f volume volume ∧
      ∀ᵐ x ∂(dExchange b hb).toMeasure, x 1 = f (x 0) :=
  ⟨intervalExchange b, measurable_xchg _, intervalExchange_measurePreserving hb,
    dExchange_ae_graph b hb⟩

theorem dExchange_xi (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    (dExchange b hb).chatterjeeXi = 1 :=
  Copula.chatterjeeXi_eq_one_of_function _ (measurable_xchg _) (dExchange_ae_graph b hb)

/-- Explicit CDF of the four-strip shuffle. -/
noncomputable def dCdf (s u v : ℝ) : ℝ :=
  min (stripCut s 0 u) (stripCut s 0 v) +
    min (stripCut (1 / 2 - s) s u) (stripCut (1 / 2 - s) (1 / 2) v) +
    min (stripCut (1 / 2 - s) (1 / 2) u) (stripCut (1 / 2 - s) s v) +
    min (stripCut s (1 - s) u) (stripCut s (1 - s) v)

theorem dExchange_cdf (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) (u v : I) :
    (dExchange b hb).cdf ![u, v] = dCdf (exchangeCut b) u v := by
  rw [dExchange_eq_shuffle]
  change (exchangeShuffle _).copula.cdf ![u, v] = _
  rw [PositiveShuffle.cdf]
  simp [Fin.sum_univ_four, exchangeShuffle, exchangeStrips, dCdf]

theorem stripCut_nonneg {s a u : ℝ} (hs : 0 ≤ s) : 0 ≤ stripCut s a u :=
  le_min hs (le_max_left _ _)

theorem dExchange_beta (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    (dExchange b hb).blomqvistBeta = b := by
  have hs := exchangeCut_mem hb
  obtain ⟨hs0, hs1⟩ := hs
  have hcut : exchangeCut b = (1 + b) / 4 := rfl
  have hw : 0 ≤ (1 / 2 : ℝ) - exchangeCut b := by linarith
  unfold Copula.blomqvistBeta
  have h := dExchange_cdf b hb Copula.unitHalf Copula.unitHalf
  have hu : ((Copula.unitHalf : I) : ℝ) = 1 / 2 := rfl
  rw [h, dCdf, hu]
  have t0 : stripCut (exchangeCut b) 0 (1 / 2) = exchangeCut b :=
    stripCut_full (by linarith)
  have t1 : stripCut (1 / 2 - exchangeCut b) (exchangeCut b) (1 / 2) = 1 / 2 - exchangeCut b :=
    stripCut_full (by linarith)
  have t2 : stripCut (1 / 2 - exchangeCut b) (1 / 2) (1 / 2) = 0 := stripCut_zero hw le_rfl
  have t3 : stripCut (exchangeCut b) (1 - exchangeCut b) (1 / 2) = 0 :=
    stripCut_zero hs0 (by linarith)
  rw [t0, t1, t2, t3]
  simp only [min_self, min_eq_right hw, min_eq_left hw, min_self]
  rw [hcut]
  ring

theorem dExchange_exchangeable (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    (dExchange b hb).IsExchangeable := by
  rw [Copula.isExchangeable_iff]
  intro u v
  rw [dExchange_cdf, dExchange_cdf, dCdf, dCdf]
  have e0 := min_comm (stripCut (exchangeCut b) 0 (u : ℝ)) (stripCut (exchangeCut b) 0 (v : ℝ))
  have e1 := min_comm (stripCut (1 / 2 - exchangeCut b) (exchangeCut b) (u : ℝ))
    (stripCut (1 / 2 - exchangeCut b) (1 / 2) (v : ℝ))
  have e2 := min_comm (stripCut (1 / 2 - exchangeCut b) (1 / 2) (u : ℝ))
    (stripCut (1 / 2 - exchangeCut b) (exchangeCut b) (v : ℝ))
  have e3 := min_comm (stripCut (exchangeCut b) (1 - exchangeCut b) (u : ℝ))
    (stripCut (exchangeCut b) (1 - exchangeCut b) (v : ℝ))
  linarith

theorem dExchange_radiallySymmetric (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    (dExchange b hb).IsRadiallySymmetric := by
  apply Copula.ext
  change ((dExchange b hb).reflect Finset.univ).toMeasure = (dExchange b hb).toMeasure
  have hg : Measurable (fun u : I => ![u, intervalExchange b u]) :=
    measurable_graph (measurable_xchg _)
  rw [Copula.toMeasure_reflect, toMeasure_dExchange, Measure.map_map (Copula.measurable_reflectPoint _) hg]
  conv_rhs => rw [← unitInterval.measurePreserving_symm.map_eq]
  rw [Measure.map_map hg unitInterval.measurable_symm]
  apply Measure.map_congr
  have hs := exchangeCut_mem hb
  filter_upwards [ae_coe_ne (exchangeCut b), ae_coe_ne (1 / 2), ae_coe_ne (1 - exchangeCut b)]
    with u h1 h2 h3
  have hx := xchg_symm hs h1 h2 h3
  funext i
  fin_cases i
  · simp [Copula.reflectPoint]
  · simp only [Function.comp, Copula.reflectPoint]
    change unitInterval.symm (intervalExchange b u) = intervalExchange b (unitInterval.symm u)
    exact hx.symm

theorem dCdf_ge_mul {s : ℝ} (hs1 : 1 / 4 ≤ s) (hs2 : s ≤ 1 / 2) {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) : u * v ≤ dCdf s u v := by
  have hw : 0 ≤ (1 / 2 : ℝ) - s := by linarith
  have t1 : min (stripCut (1 / 2 - s) s u) (stripCut (1 / 2 - s) (1 / 2) v) = 0 := by
    rw [stripCut_zero hw hv1]
    exact min_eq_right (stripCut_nonneg hw)
  have t3 : min (stripCut s (1 - s) u) (stripCut s (1 - s) v) = 0 := by
    rw [stripCut_zero (by linarith) (by linarith : v ≤ 1 - s)]
    exact min_eq_right (stripCut_nonneg (by linarith))
  unfold dCdf
  rw [t1, t3]
  have hw2 : 0 ≤ min (1 / 2 - s) (max 0 (u - 1 / 2)) := le_min hw (le_max_left _ _)
  unfold stripCut
  rw [sub_zero, sub_zero, max_eq_right hu0, max_eq_right hv0]
  rcases le_total v s with hvs | hvs
  · rw [max_eq_left (by linarith : v - s ≤ 0), min_eq_right hw, min_eq_right hw2,
      min_eq_right hvs]
    have : u * v ≤ min (min s u) v :=
      le_min (le_min (by nlinarith) (by nlinarith)) (by nlinarith)
    linarith
  · rw [min_eq_left hvs, max_eq_right (by linarith : 0 ≤ v - s),
      min_eq_right (by linarith : v - s ≤ 1 / 2 - s)]
    rcases le_total u (1 / 2) with hu | hu
    · rw [max_eq_left (by linarith : u - 1 / 2 ≤ 0), min_eq_right hw]
      have h0 : min (0 : ℝ) (v - s) = 0 := min_eq_left (by linarith)
      have hm : min (min s u) s = min s u := min_eq_left (min_le_left _ _)
      have : u * v ≤ min s u := le_min (by nlinarith) (by nlinarith)
      rw [h0, hm]
      linarith
    · rw [max_eq_right (by linarith : 0 ≤ u - 1 / 2), min_eq_left (by linarith : s ≤ u), min_self]
      rcases le_total (v - s) (min (1 / 2 - s) (u - 1 / 2)) with h | h
      · rw [min_eq_right h]
        nlinarith [mul_nonneg (sub_nonneg.2 hu1) hv0]
      · rw [min_eq_left h]
        rcases le_total (1 / 2 - s) (u - 1 / 2) with h' | h'
        · rw [min_eq_left h']
          nlinarith [mul_nonneg hu0 (sub_nonneg.2 hv1)]
        · rw [min_eq_right h']
          nlinarith [mul_nonneg hu0 (sub_nonneg.2 hv1)]

theorem dExchange_pqd (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) (hpos : 0 ≤ b) :
    (dExchange b hb).IsPQD := by
  have hs := exchangeCut_mem hb
  have hs1 : 1 / 4 ≤ exchangeCut b := by
    change 1 / 4 ≤ (1 + b) / 4
    linarith
  intro u v
  have hrs := (Copula.isRadiallySymmetric_iff _).mp (dExchange_radiallySymmetric b hb) u v
  rcases le_total (v : ℝ) (1 / 2) with hv | hv
  · rw [dExchange_cdf]
    exact dCdf_ge_mul hs1 hs.2 u.property.1 u.property.2 v.property.1 hv
  · have hv' : ((unitInterval.symm v : I) : ℝ) ≤ 1 / 2 := by
      rw [unitInterval.coe_symm_eq]; linarith
    have h := dCdf_ge_mul hs1 hs.2 (unitInterval.symm u).property.1
      (unitInterval.symm u).property.2 (unitInterval.symm v).property.1 hv'
    rw [← dExchange_cdf b hb] at h
    simp only [unitInterval.coe_symm_eq] at h hrs
    nlinarith

/-- Proposition 4.2 (right boundary): for every `b ∈ [-1,1]`, `D_b` is exchangeable and
radially symmetric, `ξ(D_b) = 1` and `β(D_b) = b`, and `D_b` is PQD for `b ≥ 0`. -/
theorem proposition_4_2 (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    (dExchange b hb).IsExchangeable ∧ (dExchange b hb).IsRadiallySymmetric ∧
      (dExchange b hb).chatterjeeXi = 1 ∧ (dExchange b hb).blomqvistBeta = b ∧
      (0 ≤ b → (dExchange b hb).IsPQD) :=
  ⟨dExchange_exchangeable b hb, dExchange_radiallySymmetric b hb, dExchange_xi b hb,
    dExchange_beta b hb, dExchange_pqd b hb⟩

theorem dCdf_le_half {s : ℝ} (hs1 : 0 ≤ s) (hs2 : s ≤ 1 / 2) {u v : ℝ}
    (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) :
    dCdf s u v = min (min s u) (min s v) +
      min (min (1 / 2 - s) (max 0 (u - 1 / 2))) (min (1 / 2 - s) (max 0 (v - s))) := by
  have hw : 0 ≤ (1 / 2 : ℝ) - s := by linarith
  have t1 : min (stripCut (1 / 2 - s) s u) (stripCut (1 / 2 - s) (1 / 2) v) = 0 := by
    rw [stripCut_zero hw hv1]
    exact min_eq_right (stripCut_nonneg hw)
  have t3 : min (stripCut s (1 - s) u) (stripCut s (1 - s) v) = 0 := by
    rw [stripCut_zero hs1 (by linarith : v ≤ 1 - s)]
    exact min_eq_right (stripCut_nonneg hs1)
  unfold dCdf
  rw [t1, t3]
  unfold stripCut
  rw [sub_zero, sub_zero, max_eq_right hu0, max_eq_right hv0]
  ring

/-- The article's formula for `v ≤ s_b`: `D_b(u,v) = min{u,v}`. -/
theorem dExchange_cdf_low (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) (u v : I)
    (hv : (v : ℝ) ≤ (1 + b) / 4) : (dExchange b hb).cdf ![u, v] = min (u : ℝ) v := by
  have hs := exchangeCut_mem hb
  have hcut : exchangeCut b = (1 + b) / 4 := rfl
  have hs2 : (1 + b) / 4 ≤ 1 / 2 := by rw [← hcut]; exact hs.2
  have hs1 : 0 ≤ (1 + b) / 4 := by rw [← hcut]; exact hs.1
  rw [dExchange_cdf, hcut, dCdf_le_half hs1 hs2 u.property.1 v.property.1 (by linarith)]
  have hw : 0 ≤ (1 / 2 : ℝ) - (1 + b) / 4 := by linarith
  have h2 : max 0 ((v : ℝ) - (1 + b) / 4) = 0 := max_eq_left (by linarith)
  rw [h2, min_eq_right hw, min_eq_right (le_min hw (le_max_left _ _)),
    min_eq_right hv, min_comm ((1 + b) / 4) (u : ℝ), min_assoc, min_eq_right hv]
  ring

/-- The article's formula for `s_b < v ≤ 1/2`:
`D_b(u,v) = min{u, s_b} + (min{u, v + 1/2 - s_b} - 1/2)_+`. -/
theorem dExchange_cdf_mid (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) (u v : I)
    (hv1 : (1 + b) / 4 < (v : ℝ)) (hv2 : (v : ℝ) ≤ 1 / 2) :
    (dExchange b hb).cdf ![u, v] =
      min (u : ℝ) ((1 + b) / 4) +
        max 0 (min (u : ℝ) ((v : ℝ) + 1 / 2 - (1 + b) / 4) - 1 / 2) := by
  have hs := exchangeCut_mem hb
  have hcut : exchangeCut b = (1 + b) / 4 := rfl
  have hs2 : (1 + b) / 4 ≤ 1 / 2 := by rw [← hcut]; exact hs.2
  have hs1 : 0 ≤ (1 + b) / 4 := by rw [← hcut]; exact hs.1
  rw [dExchange_cdf, hcut, dCdf_le_half hs1 hs2 u.property.1 v.property.1 hv2]
  have hw : 0 ≤ (1 / 2 : ℝ) - (1 + b) / 4 := by linarith
  have e1 : min ((1 + b) / 4) (v : ℝ) = (1 + b) / 4 := min_eq_left hv1.le
  have e2 : max 0 ((v : ℝ) - (1 + b) / 4) = (v : ℝ) - (1 + b) / 4 := max_eq_right (by linarith)
  have e3 : min (1 / 2 - (1 + b) / 4) ((v : ℝ) - (1 + b) / 4) = (v : ℝ) - (1 + b) / 4 :=
    min_eq_right (by linarith)
  rw [e1, e2, e3]
  have hu0 := u.property.1
  rcases le_total (u : ℝ) (1 / 2) with hu | hu
  · rw [max_eq_left (by linarith : (u : ℝ) - 1 / 2 ≤ 0), min_eq_right hw,
      min_eq_left (by linarith : (0 : ℝ) ≤ (v : ℝ) - (1 + b) / 4),
      min_eq_left (by linarith : (u : ℝ) ≤ (v : ℝ) + 1 / 2 - (1 + b) / 4),
      max_eq_left (by linarith : (u : ℝ) - 1 / 2 ≤ 0)]
    rw [min_comm ((1 + b) / 4) (u : ℝ), min_assoc, min_self]
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ (u : ℝ) - 1 / 2),
      min_eq_left (by linarith : (1 + b) / 4 ≤ (u : ℝ)),
      min_eq_right (by linarith : (1 + b) / 4 ≤ (u : ℝ)),
      max_eq_right (by
        have : (1 / 2 : ℝ) ≤ min (u : ℝ) ((v : ℝ) + 1 / 2 - (1 + b) / 4) :=
          le_min hu (by linarith)
        linarith)]
    simp only [min_def]
    split_ifs <;> linarith

end Papers.OrendayLaresRockel2026XiBeta
