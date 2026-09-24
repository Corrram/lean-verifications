import Papers.Rockel2026ExactBlest.ExactBlestBeta
import Papers.Rockel2026ExactBlest.ExactBlestGraph

/-! Copula construction and exact fibres for the two-branch eta regime.
Only claims from exact-blest-regions.tex are formalized here. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026XiBlest
open Copula.OrdinalSum

namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

/-- Put the second coordinate in one of two adjacent horizontal strips. -/
def stripLower (a : I) (x : Fin 2 → I) : Fin 2 → I := ![x 0, lowerEmbed a (x 1)]
def stripUpper (a : I) (x : Fin 2 → I) : Fin 2 → I := ![x 0, upperEmbed a (x 1)]

theorem continuous_stripLower (a : I) : Continuous (stripLower a) := by
  unfold stripLower
  fun_prop

theorem continuous_stripUpper (a : I) : Continuous (stripUpper a) := by
  unfold stripUpper
  fun_prop

attribute [fun_prop] continuous_stripLower continuous_stripUpper

theorem map_embed_eval (C : Copula 2) (i : Fin 2) (f : I → I) (hf : Measurable f) :
    C.toMeasure.map (fun x => f (x i)) = (volume : Measure I).map f := by
  rw [← C.map_eval i, Measure.map_map hf (measurable_pi_apply i)]
  rfl

theorem uniform_split (a : I) :
    ENNReal.ofReal (a : ℝ) • (volume : Measure I).map (lowerEmbed a) +
      ENNReal.ofReal (1 - (a : ℝ)) • (volume : Measure I).map (upperEmbed a) = volume := by
  have h := congrArg (fun μ : Measure (Fin 2 → I) => μ.map (fun x => x 0))
    (Copula.toMeasure_ordinalSum (Copula.comonotonic 2) (Copula.comonotonic 2) a)
  rw [Copula.map_eval, Measure.map_add _ _ (measurable_pi_apply 0),
    Measure.map_smul _ (measurable_pi_apply 0).aemeasurable,
    Measure.map_smul _ (measurable_pi_apply 0).aemeasurable,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  simp only [Function.comp_def] at h
  rw [map_embed_eval _ _ _ (by fun_prop), map_embed_eval _ _ _ (by fun_prop)] at h
  exact h.symm

def stripMeasure (C D : Copula 2) (a : I) : Measure (Fin 2 → I) :=
  ENNReal.ofReal (a : ℝ) • C.toMeasure.map (stripLower a) +
    ENNReal.ofReal (1 - (a : ℝ)) • D.toMeasure.map (stripUpper a)

theorem stripMeasure_probability (C D : Copula 2) (a : I) :
    IsProbabilityMeasure (stripMeasure C D a) := by
  refine ⟨?_⟩
  simp only [stripMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (continuous_stripLower a).measurable MeasurableSet.univ,
    Measure.map_apply (continuous_stripUpper a).measurable MeasurableSet.univ,
    preimage_univ, measure_univ, mul_one]
  rw [← ENNReal.ofReal_add a.property.1 (sub_nonneg.mpr a.property.2)]
  simp

theorem stripMeasure_marginal (C D : Copula 2) (a : I) (i : Fin 2) :
    (stripMeasure C D a).map (fun x => x i) = volume := by
  rw [stripMeasure, Measure.map_add _ _ (measurable_pi_apply i),
    Measure.map_smul _ (measurable_pi_apply i).aemeasurable,
    Measure.map_smul _ (measurable_pi_apply i).aemeasurable,
    Measure.map_map (by fun_prop) (continuous_stripLower a).measurable,
    Measure.map_map (by fun_prop) (continuous_stripUpper a).measurable]
  fin_cases i
  · change ENNReal.ofReal (a : ℝ) • C.toMeasure.map (fun x => x 0) +
      ENNReal.ofReal (1 - (a : ℝ)) • D.toMeasure.map (fun x => x 0) = volume
    rw [Copula.map_eval, Copula.map_eval]
    rw [← add_smul, ← ENNReal.ofReal_add a.property.1 (sub_nonneg.mpr a.property.2)]
    simp
  · change ENNReal.ofReal (a : ℝ) • C.toMeasure.map (fun x => lowerEmbed a (x 1)) +
      ENNReal.ofReal (1 - (a : ℝ)) • D.toMeasure.map (fun x => upperEmbed a (x 1)) = volume
    rw [map_embed_eval _ _ _ (by fun_prop), map_embed_eval _ _ _ (by fun_prop)]
    exact uniform_split a

/-- Horizontal gluing, with both marginals proved uniform. -/
def stripCopula (C D : Copula 2) (a : I) : Copula 2 where
  measure := ⟨stripMeasure C D a, stripMeasure_probability C D a⟩
  marginal_eq := stripMeasure_marginal C D a

theorem integral_stripCopula (C D : Copula 2) (a : I)
    {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂(stripCopula C D a).toMeasure) =
      (a : ℝ) * (∫ x, f (stripLower a x) ∂C.toMeasure) +
        (1 - (a : ℝ)) * ∫ x, f (stripUpper a x) ∂D.toMeasure := by
  change (∫ x, f x ∂(stripMeasure C D a)) = _
  rw [stripMeasure, integral_add_measure
    ((Copula.integrable_continuous_cube _ hf).smul_measure ENNReal.ofReal_ne_top)
    ((Copula.integrable_continuous_cube _ hf).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    integral_map (continuous_stripLower a).measurable.aemeasurable hf.aestronglyMeasurable,
    integral_map (continuous_stripUpper a).measurable.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal a.property.1, ENNReal.toReal_ofReal (sub_nonneg.mpr a.property.2)]
  rfl

#assert_standard_axioms Papers.Rockel2026ExactBlest.continuous_stripLower
#assert_standard_axioms Papers.Rockel2026ExactBlest.continuous_stripUpper
#assert_standard_axioms Papers.Rockel2026ExactBlest.map_embed_eval
#assert_standard_axioms Papers.Rockel2026ExactBlest.uniform_split
#assert_standard_axioms Papers.Rockel2026ExactBlest.stripMeasure_probability
#assert_standard_axioms Papers.Rockel2026ExactBlest.stripMeasure_marginal
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_stripCopula

def skewTent (p : I) : Copula 2 := stripCopula (Copula.comonotonic 2) Copula.countermonotonic p

theorem nu_skewTent (p : I) : blestNu (skewTent p) = 2 * (p : ℝ) - 1 := by
  rw [nu_moment, skewTent, integral_stripCopula _ _ _ (by fun_prop),
    Copula.integral_comonotonic _ (by fun_prop), Copula.integral_countermonotonic _ (by fun_prop)]
  simp only [stripLower, stripUpper, lowerEmbed, upperEmbed,
    Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq]
  have h0 : (fun u : I => (1 - (u : ℝ)) ^ 2 * (1 - ((p : ℝ) * (u : ℝ)))) =
      fun u : I => (-(p : ℝ)) * (u : ℝ) ^ 3 + (2 * (p : ℝ) + 1) * (u : ℝ) ^ 2 + (-(p : ℝ) - 2) * (u : ℝ) + (1) := by funext u; ring
  have h1 : (fun u : I => (1 - (u : ℝ)) ^ 2 * (1 - ((p : ℝ) + (1 - (p : ℝ)) * (1 - (u : ℝ))))) =
      fun u : I => (1 - (p : ℝ)) * (u : ℝ) ^ 3 + (2 * (p : ℝ) - 2) * (u : ℝ) ^ 2 + (1 - (p : ℝ)) * (u : ℝ) + (0) := by funext u; ring
  rw [h0, h1, integral_unit_poly3, integral_unit_poly3]
  ring
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_skewTent

theorem nu_transpose_skewTent (p : I) : blestNu (skewTent p).transpose = -(p : ℝ) ^ 2 + 3 * (p : ℝ) - 1 := by
  rw [nu_transpose_moment, skewTent, integral_stripCopula _ _ _ (by fun_prop),
    Copula.integral_comonotonic _ (by fun_prop), Copula.integral_countermonotonic _ (by fun_prop)]
  simp only [stripLower, stripUpper, lowerEmbed, upperEmbed,
    Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq]
  have h0 : (fun u : I => (1 - (u : ℝ)) * (1 - ((p : ℝ) * (u : ℝ))) ^ 2) =
      fun u : I => (-(p : ℝ) ^ 2) * (u : ℝ) ^ 3 + ((p : ℝ) ^ 2 + 2 * (p : ℝ)) * (u : ℝ) ^ 2 + (-2 * (p : ℝ) - 1) * (u : ℝ) + (1) := by funext u; ring
  have h1 : (fun u : I => (1 - (u : ℝ)) * (1 - ((p : ℝ) + (1 - (p : ℝ)) * (1 - (u : ℝ)))) ^ 2) =
      fun u : I => (-(p : ℝ) ^ 2 + 2 * (p : ℝ) - 1) * (u : ℝ) ^ 3 + ((p : ℝ) ^ 2 - 2 * (p : ℝ) + 1) * (u : ℝ) ^ 2 + (0) * (u : ℝ) + (0) := by funext u; ring
  rw [h0, h1, integral_unit_poly3, integral_unit_poly3]
  ring
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_skewTent

theorem rho_skewTent (p : I) : (skewTent p).spearmanRho = 2 * (p : ℝ) - 1 := by
  rw [Copula.spearmanRho, skewTent, integral_stripCopula _ _ _ (by fun_prop),
    Copula.integral_comonotonic _ (by fun_prop), Copula.integral_countermonotonic _ (by fun_prop)]
  simp only [stripLower, stripUpper, lowerEmbed, upperEmbed,
    Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq]
  have h0 : (fun u : I => (u : ℝ) * ((p : ℝ) * (u : ℝ))) =
      fun u : I => (0) * (u : ℝ) ^ 3 + ((p : ℝ)) * (u : ℝ) ^ 2 + (0) * (u : ℝ) + (0) := by funext u; ring
  have h1 : (fun u : I => (u : ℝ) * ((p : ℝ) + (1 - (p : ℝ)) * (1 - (u : ℝ)))) =
      fun u : I => (0) * (u : ℝ) ^ 3 + ((p : ℝ) - 1) * (u : ℝ) ^ 2 + (1) * (u : ℝ) + (0) := by funext u; ring
  rw [h0, h1, integral_unit_poly3, integral_unit_poly3]
  ring
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_skewTent

def randomSplit (a : I) (ha : (1 / 2 : ℝ) ≤ a) : I :=
  ⟨(2 * (a : ℝ) - 1) / (2 * (a : ℝ)), by
    have hp : 0 < 2 * (a : ℝ) := by linarith
    exact ⟨div_nonneg (by linarith) hp.le, (div_le_one hp).mpr (by linarith)⟩⟩

/-- The original-coordinate B_a, including the continuous coefficient endpoint a=1. -/
def familyB (a : I) (ha : (1 / 2 : ℝ) ≤ a) : Copula 2 :=
  ((Copula.comonotonic 2).ordinalSum (skewTent (randomSplit a ha)) a).reflect {0}

def nuB (a : ℝ) : ℝ := -1 + (1 + a) * (1 - a) ^ 3 / a
def etaB (a : ℝ) : ℝ := -1 + (1 - a) ^ 3 * (2 * a ^ 2 + 5 * a + 1) / (8 * a ^ 2)

theorem nu_familyB (a : I) (ha : (1 / 2 : ℝ) ≤ a) :
    blestNu (familyB a ha) = nuB a := by
  have h0 : (a : ℝ) ≠ 0 := by linarith
  rw [familyB, nu_reflect_first, blest_ordinalSum, Copula.spearmanRho_ordinalSum,
    blest_comonotonic, Copula.spearmanRho_comonotonic, nu_skewTent, rho_skewTent]
  dsimp [randomSplit, nuB]
  field_simp
  ring

theorem transpose_comonotonic_two : (Copula.comonotonic 2).transpose = Copula.comonotonic 2 := by
  apply Copula.ext_cdf
  intro x
  have he : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [he, Copula.cdf_transpose, Copula.cdf_comonotonic_two, Copula.cdf_comonotonic_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, min_comm]

theorem nu_transpose_familyB (a : I) (ha : (1 / 2 : ℝ) ≤ a) :
    blestNu (familyB a ha).transpose = 2 * etaB a - nuB a := by
  have h0 : (a : ℝ) ≠ 0 := by linarith
  rw [familyB, Copula.transpose_reflect_first, blest_reflect_second, Copula.transpose_ordinalSum,
    transpose_comonotonic_two, blest_ordinalSum, blest_comonotonic,
    Copula.spearmanRho_comonotonic, nu_transpose_skewTent]
  dsimp [randomSplit, nuB, etaB]
  field_simp
  ring

theorem eta_familyB (a : I) (ha : (1 / 2 : ℝ) ≤ a) : eta (familyB a ha) = etaB a := by
  rw [eta, nu_familyB, nu_transpose_familyB]
  ring

#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_familyB
#assert_standard_axioms Papers.Rockel2026ExactBlest.transpose_comonotonic_two
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_familyB
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_familyB

theorem nu_rho_upper_attained : ∃ C : Copula 2, blestNu C - C.spearmanRho = 1 / 4 := by
  refine ⟨(skewTent Copula.unitHalf).transpose, ?_⟩
  rw [nu_transpose_skewTent, Copula.spearmanRho_transpose, rho_skewTent]
  norm_num [Copula.unitHalf]

theorem nu_rho_lower_attained : ∃ C : Copula 2, blestNu C - C.spearmanRho = -1 / 4 := by
  obtain ⟨C, h⟩ := nu_rho_upper_attained
  refine ⟨C.survivalCopula, ?_⟩
  rw [nu_survival, Copula.spearmanRho_survivalCopula]
  linarith

def threePieces (c b : ℝ) (f0 f1 f2 : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ c then f0 x else if x ≤ b then f1 x else f2 x

theorem integral_threePieces (c b : ℝ) (hc : c ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hcb : c ≤ b) (f0 f1 f2 : ℝ → ℝ)
    (h0 : Continuous f0) (h1 : Continuous f1) (h2 : Continuous f2) :
    (∫ u : I, threePieces c b f0 f1 f2 u) =
      (∫ u : I, f2 u) + (∫ x in (0 : ℝ)..b, f1 x - f2 x) +
        (∫ x in (0 : ℝ)..c, f0 x - f1 x) := by
  have he : threePieces c b f0 f1 f2 = fun x =>
      f2 x + cutValue (fun x => f1 x - f2 x) b x + cutValue (fun x => f0 x - f1 x) c x := by
    funext x
    unfold threePieces cutValue
    split_ifs <;> linarith
  have hi2 : Integrable (fun u : I => f2 u) := Copula.integrable_continuous_unit _ (by fun_prop)
  have hi1 := integrable_cutValue (fun x => f1 x - f2 x) (h1.sub h2) b
  have hi0 := integrable_cutValue (fun x => f0 x - f1 x) (h0.sub h1) c
  have ha0 := integral_add (hi2.add hi1) hi0
  have ha1 := integral_add hi2 hi1
  simp only [Pi.add_apply] at ha0 ha1
  rw [he]
  dsimp only
  rw [ha0, ha1, integral_cutValue _ _ hb, integral_cutValue _ _ hc]

theorem integrable_phiB (C : Copula 2) (a : ℝ) (i : Fin 2) :
    Integrable (fun x => phiB a (x i)) C.toMeasure := by
  classical
  exact Integrable.piecewise
    (measurableSet_le (show Measurable (fun x : Fin 2 → I => (x i : ℝ)) by fun_prop) measurable_const)
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I => phiB0 a (x i)) by
      unfold phiB0 antiPhi; fun_prop)).integrableOn
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I => phiB1 a (x i)) by
      unfold phiB1 splitPhi; fun_prop)).integrableOn

theorem integrable_psiB (C : Copula 2) (a : ℝ) (i : Fin 2) :
    Integrable (fun x => psiB a (x i)) C.toMeasure := by
  classical
  have hm (t : ℝ) : MeasurableSet {x : Fin 2 → I | (x i : ℝ) ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  exact Integrable.piecewise (hm _)
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I => psiB0 a (x i)) by
      unfold psiB0 linearPsi; fun_prop)).integrableOn
    (Integrable.piecewise (hm _)
      (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I => psiB1 a (x i)) by
        unfold psiB1 linearPsi; fun_prop)).integrableOn
      (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I => psiB2 a (x i)) by
        unfold psiB2 linearPsi; fun_prop)).integrableOn).integrableOn

theorem measurable_phiB (a : ℝ) : Measurable (fun u : I => phiB a u) := by
  exact (show Measurable (fun u : I => phiB0 a u) by unfold phiB0 antiPhi; fun_prop).ite
    (measurableSet_le measurable_subtype_coe measurable_const)
    (show Measurable (fun u : I => phiB1 a u) by unfold phiB1 splitPhi; fun_prop)

theorem measurable_psiB (a : ℝ) : Measurable (fun u : I => psiB a u) := by
  exact (show Measurable (fun u : I => psiB0 a u) by unfold psiB0 linearPsi; fun_prop).ite
    (measurableSet_le measurable_subtype_coe measurable_const)
    ((show Measurable (fun u : I => psiB1 a u) by unfold psiB1 linearPsi; fun_prop).ite
      (measurableSet_le measurable_subtype_coe measurable_const)
      (show Measurable (fun u : I => psiB2 a u) by unfold psiB2 linearPsi; fun_prop))

#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_rho_upper_attained
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_rho_lower_attained
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_threePieces
#assert_standard_axioms Papers.Rockel2026ExactBlest.integrable_phiB
#assert_standard_axioms Papers.Rockel2026ExactBlest.integrable_psiB
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_phiB
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_psiB

theorem integral_phiB (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    (∫ u : I, phiB a u) = (2 * a ^ 5 - a ^ 4 - 8 * a ^ 3 + 2 * a ^ 2 + 2 * a - 1) / (24 * a * (a - 1)) := by
  have h0 : a ≠ 0 := by linarith
  have h1 : a - 1 ≠ 0 := by linarith
  have h1p : 1 - a ≠ 0 := by linarith
  change (∫ u : I, if (u : ℝ) ≤ a then phiB0 a u else phiB1 a u) = _
  rw [integral_unit_piecewise (phiB0 a) (phiB1 a)
    (by unfold phiB0 antiPhi; fun_prop) (by unfold phiB1 splitPhi; fun_prop) a ⟨by linarith, ha1.le⟩]
  have he0 : phiB0 a = fun x : ℝ => (2/(3 * (a - 1))) * x ^ 3 + (-(a + 1)/(a - 1)) * x ^ 2 + (2 * a/(a - 1)) * x + (a ^ 2 * (a - 3)/(3 * (a - 1))) := by
    funext x; unfold phiB0 antiPhi kB; field_simp; ring
  have he1 : phiB1 a = fun x : ℝ => ((2 * a - 1)/(6 * a * (a - 1))) * x ^ 3 + (-a/(2 * (a - 1))) * x ^ 2 + (a/(2 * (a - 1))) * x + (a ^ 2 * (a - 2)/(6 * (a - 1))) := by
    funext x; unfold phiB1 splitPhi kB; field_simp; ring
  rw [he0, he1, integral_poly3, integral_poly3]
  field_simp
  ring
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_phiB

theorem integral_psiB (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    (∫ u : I, psiB a u) = -a * (a ^ 3 - 6 * a + 1) / (12 * (a - 1)) := by
  have h0 : a ≠ 0 := by linarith
  have h1 : a - 1 ≠ 0 := by linarith
  have h1p : 1 - a ≠ 0 := by linarith
  have h2 : 2 * a - 1 ≠ 0 := by linarith
  have hp : 0 < 2 * a := by linarith
  have hc : cutB a ∈ Icc (0 : ℝ) 1 := by
    unfold cutB
    exact ⟨div_nonneg (by linarith) hp.le, (div_le_one hp).mpr (by linarith)⟩
  have hcb : cutB a ≤ 1 - a := by
    unfold cutB
    apply (div_le_iff₀ hp).mpr
    nlinarith
  change (∫ u : I, threePieces (cutB a) (1 - a) (psiB0 a) (psiB1 a) (psiB2 a) u) = _
  rw [integral_threePieces _ _ hc ⟨by linarith, by linarith⟩ hcb _ _ _
    (by unfold psiB0 linearPsi; fun_prop) (by unfold psiB1 linearPsi; fun_prop)
    (by unfold psiB2 linearPsi; fun_prop)]
  have he0 : psiB2 a = fun x : ℝ => (-(3 * a + 1)/(3 * (a - 1))) * x ^ 3 + ((a + 1)/(a - 1)) * x ^ 2 + (1) * x + (-(a - 1) ^ 2/3) := by
    funext x; unfold psiB2 psiB1 psiB0 linearPsi cutB kB; field_simp; ring
  have he1 : (fun x : ℝ => psiB1 a x - psiB2 a x) = fun x : ℝ => (-(4 * a ^ 2 + a - 1)/(3 * (a - 1) * (2 * a - 1) ^ 2)) * x ^ 3 + (-(2 * a ^ 2 + 2 * a - 1)/(2 * a - 1) ^ 2) * x ^ 2 + (-(a - 1) * (3 * a - 1)/(2 * a - 1) ^ 2) * x + ((a - 1) ^ 2 * (2 * a ^ 2 - 4 * a + 1)/(3 * (2 * a - 1) ^ 2)) := by
    funext x; unfold psiB2 psiB1 psiB0 linearPsi cutB kB; field_simp; ring
  have he2 : (fun x : ℝ => psiB0 a x - psiB1 a x) = fun x : ℝ => (16 * a ^ 5/(3 * (a - 1) * (2 * a - 1) ^ 2)) * x ^ 3 + (8 * a ^ 4/(2 * a - 1) ^ 2) * x ^ 2 + (4 * a ^ 3 * (a - 1)/(2 * a - 1) ^ 2) * x + (2 * a ^ 2 * (a - 1) ^ 2/(3 * (2 * a - 1) ^ 2)) := by
    funext x; unfold psiB1 psiB0 linearPsi cutB kB; field_simp; ring
  rw [he1, he2, he0, Copula.integral_unitInterval (fun x : ℝ => (-(3 * a + 1)/(3 * (a - 1))) * x ^ 3 + ((a + 1)/(a - 1)) * x ^ 2 + (1) * x + (-(a - 1) ^ 2/3)),
    integral_poly3, integral_poly3, integral_poly3]
  unfold cutB
  have hpoly : 1 - a * 4 + a ^ 2 * 4 ≠ 0 := by
    convert pow_ne_zero 2 h2 using 1
    ring
  field_simp [hpoly]
  ring_nf
  field_simp [hpoly]
  ring
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_psiB

theorem integral_potentialsB (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    (∫ u : I, phiB a u) + (∫ u : I, psiB a u) =
      ((1 + kB a) * nuB a - 2 * kB a * etaB a + 2 * (1 - kB a)) / 12 := by
  have h0 : a ≠ 0 := by linarith
  have h1 : a - 1 ≠ 0 := by linarith
  have h1p : 1 - a ≠ 0 := by linarith
  rw [integral_phiB a ha ha1, integral_psiB a ha ha1]
  unfold kB nuB etaB
  field_simp
  ring

theorem randomized_support (C : Copula 2) (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    (1 + kB a) * blestNu C - 2 * kB a * eta C ≤
      (1 + kB a) * nuB a - 2 * kB a * etaB a := by
  let D := C.survivalCopula
  have hp := integrable_phiB D a 0
  have hq := integrable_psiB D a 1
  have hi : Integrable (fun x : Fin 2 → I => cost (kB a) (x 0) (x 1)) D.toMeasure :=
    Copula.integrable_continuous_cube _ (by unfold cost; fun_prop)
  have h := integral_mono hi (hp.add hq)
    (fun x => dualB a (x 0) (x 1) ha ha1 (x 0).property (x 1).property)
  simp only [Pi.add_apply] at h
  rw [integral_add hp hq, D.integral_eval 0 _ (measurable_phiB a),
    D.integral_eval 1 _ (measurable_psiB a), integral_potentialsB a ha ha1] at h
  have hs := support_moment_survival C (kB a)
  change (1 + kB a) * blestNu C - 2 * kB a * eta C =
    12 * (∫ x, cost (kB a) (x 0) (x 1) ∂D.toMeasure) - 2 * (1 - kB a) at hs
  linarith

theorem nu_le_familyB (C : Copula 2) (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1)
    (he : eta C = etaB a) : blestNu C ≤ nuB a := by
  have h := randomized_support C a ha ha1
  rw [he] at h
  have hk : 0 < 1 + kB a := by
    have hp : 0 < a := by linarith
    have hd : 0 < 1 - a := by linarith
    unfold kB
    positivity
  by_contra hn
  have hm := mul_pos hk (show 0 < blestNu C - nuB a by linarith)
  nlinarith

theorem randomized_fibre (a : I) (ha : (1 / 2 : ℝ) < a) (ha1 : (a : ℝ) < 1) (n : ℝ) :
    (∃ C : Copula 2, eta C = etaB a ∧ blestNu C = n) ↔
      n ∈ Icc (2 * etaB a - nuB a) (nuB a) := by
  constructor
  · rintro ⟨C, he, rfl⟩
    have hu := nu_le_familyB C a ha ha1 he
    have hl := nu_le_familyB C.transpose a ha ha1 ((eta_transpose C).trans he)
    rw [nu_transpose, he] at hl
    exact ⟨by linarith, hu⟩
  · intro hn
    let B := familyB a ha.le
    have hb : blestNu B = nuB a := nu_familyB a ha.le
    have he : eta B = etaB a := eta_familyB a ha.le
    have hc : Continuous (fun t : I => blestNu (B.mix B.transpose t)) := by
      simp_rw [blest_mix]
      fun_prop
    obtain ⟨t, ht⟩ := Verification.exists_unitInterval_eq hc (z := n)
      (by simp only [blest_mix]; norm_num; rw [nu_transpose, hb, he]; exact hn.1)
      (by simp only [blest_mix]; norm_num; rw [hb]; exact hn.2)
    refine ⟨B.mix B.transpose t, ?_, ht⟩
    rw [eta_mix, eta_transpose, he]
    ring

#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_potentialsB
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomized_support
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_le_familyB
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomized_fibre

theorem etaB_factor (a : ℝ) (ha : a ≠ 0) :
    etaB a = -1 + (1 - a) ^ 3 * (2 + 5 * (1 / a) + (1 / a) ^ 2) / 8 := by
  unfold etaB
  field_simp

theorem randomized_parameter_strictAnti : StrictAntiOn etaB (Icc (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hi : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hxy.le
  have hs : (1 / y) ^ 2 ≤ (1 / x) ^ 2 := by
    gcongr
  have hh : 2 + 5 * (1 / y) + (1 / y) ^ 2 ≤ 2 + 5 * (1 / x) + (1 / x) ^ 2 := by linarith
  have hpos : 0 < 2 + 5 * (1 / x) + (1 / x) ^ 2 := by positivity
  have hp : (1 - y) ^ 3 < (1 - x) ^ 3 := by
    gcongr
    linarith [hy.2]
  have hnon : 0 ≤ (1 - y) ^ 3 := pow_nonneg (by linarith [hy.2]) 3
  have hmul := mul_le_mul_of_nonneg_left hh hnon
  have hstrict := mul_lt_mul_of_pos_right hp hpos
  rw [etaB_factor x hx0.ne', etaB_factor y hy0.ne']
  linarith

theorem randomized_parameter_exists_unique (e : ℝ) (he : e ∈ Icc (-1 : ℝ) (-3 / 4)) :
    ∃! a : I, (1 / 2 : ℝ) ≤ a ∧ etaB a = e := by
  have hc : Continuous (fun t : I => -etaB ((1 + (t : ℝ)) / 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have ht : 0 < 1 + (t : ℝ) := by linarith [t.property.1]
    unfold etaB
    fun_prop (disch := positivity)
  obtain ⟨t, ht⟩ := Verification.exists_unitInterval_eq hc (z := -e)
    (by norm_num [etaB]; linarith [he.2]) (by norm_num [etaB]; linarith [he.1])
  let a : I := ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
  have ha : (1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith [t.property.1]
  have hv : etaB a = e := by change etaB ((1 + (t : ℝ)) / 2) = e; linarith
  refine ⟨a, ⟨ha, hv⟩, ?_⟩
  intro b hb
  apply Subtype.ext
  apply randomized_parameter_strictAnti.injOn ⟨hb.1, b.property.2⟩ ⟨ha, a.property.2⟩
  exact hb.2.trans hv.symm

theorem randomized_parameter_exists_open (e : ℝ) (he : e ∈ Ioo (-1 : ℝ) (-3 / 4)) :
    ∃ a : I, (1 / 2 : ℝ) < a ∧ (a : ℝ) < 1 ∧ etaB a = e := by
  obtain ⟨a, ha, _⟩ := randomized_parameter_exists_unique e ⟨he.1.le, he.2.le⟩
  have hl : (1 / 2 : ℝ) < a := by
    by_contra h
    have heq : (a : ℝ) = 1 / 2 := by linarith [ha.1]
    rw [heq] at ha
    norm_num [etaB] at ha
    linarith [he.2]
  have hu : (a : ℝ) < 1 := by
    by_contra h
    have heq : (a : ℝ) = 1 := by linarith [a.property.2]
    rw [heq] at ha
    norm_num [etaB] at ha
    linarith [he.1]
  exact ⟨a, hl, hu, ha.2⟩

#assert_standard_axioms Papers.Rockel2026ExactBlest.etaB_factor
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomized_parameter_strictAnti
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomized_parameter_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomized_parameter_exists_open

theorem eta_bottom_fibre (n : ℝ) :
    (∃ C : Copula 2, eta C = -1 ∧ blestNu C = n) ↔ n = -1 := by
  constructor
  · rintro ⟨C, he, rfl⟩
    have hc := (blest_mem_Icc C).1
    have ht := (blest_mem_Icc C.transpose).1
    dsimp [eta] at he
    linarith
  · rintro rfl
    refine ⟨familyA 1, ?_, ?_⟩
    · rw [eta_familyA]; norm_num
    · rw [nu_familyA]; norm_num

/-- An exact parameterization of the complete attainable eta/nu region. -/
def etaRegion (e n : ℝ) : Prop :=
  (∃ w : I, (w : ℝ) ≤ 1 / 2 ∧ e = eta (familyA w) ∧
    n ∈ Icc (2 * eta (familyA w) - blestNu (familyA w)) (blestNu (familyA w))) ∨
  (∃ a : I, (1 / 2 : ℝ) < a ∧ (a : ℝ) < 1 ∧ e = etaB a ∧
    n ∈ Icc (2 * etaB a - nuB a) (nuB a)) ∨
  (e = -1 ∧ n = -1)

theorem eta_fibre_complete (e n : ℝ) :
    (∃ C : Copula 2, eta C = e ∧ blestNu C = n) ↔ etaRegion e n := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    have he := eta_mem_Icc C
    by_cases hg : -3 / 4 ≤ eta C
    · obtain ⟨w, hw, _⟩ := graph_parameter_exists_unique (eta C) ⟨hg, he.2⟩
      exact Or.inl ⟨w, hw.1, hw.2.symm, (graph_fibre w hw.1 _).mp ⟨C, hw.2.symm, rfl⟩⟩
    · by_cases hb : eta C = -1
      · exact Or.inr (Or.inr ⟨hb, (eta_bottom_fibre _).mp ⟨C, hb, rfl⟩⟩)
      · have ho : eta C ∈ Ioo (-1 : ℝ) (-3 / 4) := ⟨lt_of_le_of_ne he.1 (Ne.symm hb), by linarith⟩
        obtain ⟨a, ha, ha1, hav⟩ := randomized_parameter_exists_open (eta C) ho
        exact Or.inr (Or.inl ⟨a, ha, ha1, hav.symm,
          (randomized_fibre a ha ha1 _).mp ⟨C, hav.symm, rfl⟩⟩)
  · rintro (⟨w, hw, rfl, hn⟩ | ⟨a, ha, ha1, rfl, hn⟩ | ⟨rfl, rfl⟩)
    · exact (graph_fibre w hw n).mpr hn
    · exact (randomized_fibre a ha ha1 n).mpr hn
    · exact (eta_bottom_fibre (-1)).mpr rfl

/-- Full set equality, in the two natural parameters; boundary uniqueness is separate. -/
theorem eta_nu_region_parametric :
    Set.range (fun C : Copula 2 => (eta C, blestNu C)) =
      {p : ℝ × ℝ | etaRegion p.1 p.2} := by
  ext ⟨e, n⟩
  simpa only [Set.mem_range, Set.mem_ofPred_eq, Prod.mk.injEq] using eta_fibre_complete e n

#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_bottom_fibre
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_fibre_complete
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_nu_region_parametric

end
end Papers.Rockel2026ExactBlest
