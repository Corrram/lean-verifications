import Papers.Rockel2026ExactBlest.Source.Bridge

/-! # Results the article states without a compiled proof

Theorem 1.1, Lemmas 2.2 and 3.1, the displayed formulas and the
well-definedness of every definition, proved through `Bridge` from the
companion Lean development of the paper. These are the premises that the
proof of Corollary 3.2 cites (`Steps.lean`). -/

namespace Papers.Rockel2026ExactBlest.Source.Proofs
open Papers.Rockel2026ExactBlest.Source Papers.Rockel2026ExactBlest.Source.Bridge
open Proofread MeasureTheory ProbabilityTheory
open Papers.Rockel2026ExactBlest (paperD paperD_values paperD_on_boundary paperD_strictMono
  paperD_parameter_exists_unique paper_rho_upper_unique paper_rho_lower_unique rho_fibre_complete
  rhoBoundary rhoBoundary_neg nu_survival eta_survival quadraticRank quadraticRank_uniform paperZeta_formula)
open scoped unitInterval

/-! ## Facts about article copulas -/

theorem copulas_transpose {F : I → I → ℝ} (hF : copulas F) : copulas (transpose F) := by
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  rw [transpose_cdfOf]; exact copulas_cdfOf _

theorem copulas_survival {F : I → I → ℝ} (hF : copulas F) : copulas (survival F) := by
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  rw [survival_cdfOf]; exact copulas_cdfOf _

theorem copulas_reflection {F : I → I → ℝ} (hF : copulas F) : copulas (reflection F) := by
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  rw [reflection_cdfOf]; exact copulas_cdfOf _

theorem probMeasure2_gamma {f : I → I} (hf : Measurable f) : UnitSquare.probMeasure2 (gamma f) := by
  refine ⟨(volume : Measure I).map (fun t => (t, f t)), inferInstance, fun A hA => ?_⟩
  rw [Measure.map_apply (by fun_prop : Measurable (fun t : I => (t, f t))) hA]
  rfl

theorem leb_le_one (A : I → Prop) : Prelude.leb A ≤ 1 := by
  unfold Prelude.leb
  have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := (volume : Measure I)) (s := {x | A x}))
  simpa using this

/-! ## Well-definedness of the definitions -/

theorem defined0 : wellDefined0 := trivial
theorem defined3 : wellDefined3 := trivial
theorem defined10 : wellDefined10 := trivial

theorem defined1 : wellDefined1 := by
  intro F hF
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  have hc : Continuous (fun p : I × I => (1 - (p.1 : ℝ)) * cdfOf K p.1 p.2) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul (continuous_cdfOf K)
  exact ⟨integrable_section hc, integrable_integral hc⟩

theorem defined2 : wellDefined2 := by
  intro F hF
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  exact ⟨integrable_section (continuous_cdfOf K), integrable_integral (continuous_cdfOf K)⟩

theorem defined4 : wellDefined4 := by
  intro F _ u v
  exact ⟨⟨by linarith [u.2.2], by linarith [u.2.1]⟩, by linarith [v.2.2], by linarith [v.2.1]⟩

theorem defined5 : wellDefined5 := by
  intro F hF
  exact ⟨⟨hF, hF, copulas_transpose hF, hF⟩, by norm_num⟩

theorem defined6 : wellDefined6 := by
  intro x hx
  refine ⟨fun h1 => ⟨⟨by norm_num, by linarith [h1.1], by norm_num⟩,
      fun h2 => ⟨⟨by norm_num, by linarith [h2.2], by norm_num⟩, ?_⟩⟩,
    fun h1 => ⟨fun h2 => ⟨by norm_num, by linarith [h2.2], by norm_num⟩, fun h2 _ => ?_⟩⟩
  · have : x = 0 := le_antisymm h1.2 h2.1
    subst this; norm_num
  · apply h2
    by_contra hn
    apply h1
    constructor
    · exact hx.1
    · by_contra hp; exact hn ⟨le_of_lt (lt_of_not_ge hp), hx.2⟩

theorem defined9 : wellDefined9 := by
  intro _ _ u v
  exact (measurableSet_le (f := fun p : I × I => 1 - (p.1 : ℝ)) (g := fun _ => (u : ℝ)) (by fun_prop)
    measurable_const).inter
    (measurableSet_le (f := fun p : I × I => 1 - (p.2 : ℝ)) (g := fun _ => (v : ℝ)) (by fun_prop)
      measurable_const)

theorem defined11 : wellDefined11 := by
  intro F _ _ v
  exact ⟨by linarith [v.2.2], by linarith [v.2.1]⟩

theorem defined12 : wellDefined12 := by
  intro f hf A hA
  exact hA.preimage (measurable_id.prodMk hf)

theorem defined14 : wellDefined14 := by
  intro F _ f hf u v
  exact (measurableSet_le measurable_subtype_coe measurable_const).inter
    (measurableSet_le (measurable_subtype_coe.comp hf) measurable_const)

theorem defined15 : wellDefined15 := by
  intro c x
  refine ⟨measurableSet_le (f := fun t : I => |(t : ℝ) + c - 1|) (g := fun _ => |(x : ℝ) + c - 1|)
    (by fun_prop) measurable_const, ENNReal.toReal_nonneg, leb_le_one _⟩

theorem defined16 : wellDefined16 := by
  intro c
  have hm := measurable_zeta c
  refine ⟨hm, ⟨probMeasure2_gamma hm, fun u => ?_, fun v => ?_⟩, hm⟩
  · change ((volume : Measure I) {t | t ≤ u}).toReal = u
    rw [show {t : I | t ≤ u} = Set.Iic u from rfl, unitInterval.volume_Iic, ENNReal.toReal_ofReal u.2.1]
  · change ((volume : Measure I) {t | zeta c t ≤ v}).toReal = v
    rw [zeta_eq, show {t : I | quadraticRank (σ c) t ≤ v} = quadraticRank (σ c) ⁻¹' Set.Iic v from rfl,
      (quadraticRank_uniform _).measure_preimage measurableSet_Iic.nullMeasurableSet,
      unitInterval.volume_Iic, ENNReal.toReal_ofReal v.2.1]

theorem defined17 : wellDefined17 := by
  intro x
  have h0 := x.2.1
  have h1 := x.2.2
  refine ⟨le_min (by linarith) (by linarith), ?_⟩
  rcases le_total (x : ℝ) (1 / 2) with h | h
  · exact min_le_of_left_le (by linarith)
  · exact min_le_of_right_le (by linarith)

/-! ## Claims stated without a compiled proof -/

theorem proof0 : obligation0 := by
  refine ⟨fun F hF => ?_, fun F hF => ?_⟩
  · obtain ⟨K, rfl⟩ := exists_of_copulas hF
    have hc : Continuous (fun p : I × I => (2 - (p.1 : ℝ) - p.2) * cdfOf K p.1 p.2) :=
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).sub
        (continuous_subtype_val.comp continuous_snd)).mul (continuous_cdfOf K)
    exact ⟨⟨⟨hF, hF, copulas_transpose hF, hF⟩, by norm_num⟩, integrable_section hc, integrable_integral hc⟩
  · obtain ⟨K, rfl⟩ := exists_of_copulas hF
    set G := cdfOf K
    have hG := continuous_cdfOf K
    have c1 : Continuous (fun p : I × I => (1 - (p.1 : ℝ)) * G p.1 p.2) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hG
    have c2 : Continuous (fun p : I × I => (1 - (p.2 : ℝ)) * G p.1 p.2) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul hG
    have hin : ∀ v : I, ∫ u : I, (2 - (u : ℝ) - v) * G u v =
        (∫ u : I, (1 - (u : ℝ)) * G u v) + ∫ u : I, (1 - (v : ℝ)) * G u v := by
      intro v
      rw [← integral_add (integrable_section (h := fun u v => (1 - (u : ℝ)) * G u v) c1 v)
        (integrable_section (h := fun u v => (1 - (v : ℝ)) * G u v) c2 v)]
      congr 1; funext u; ring
    have hout : (∫ v : I, ∫ u : I, (2 - (u : ℝ) - v) * G u v) =
        (∫ v : I, ∫ u : I, (1 - (u : ℝ)) * G u v) + ∫ v : I, ∫ u : I, (1 - (v : ℝ)) * G u v := by
      simp_rw [hin]
      exact integral_add (integrable_integral (h := fun u v => (1 - (u : ℝ)) * G u v) c1)
        (integrable_integral (h := fun u v => (1 - (v : ℝ)) * G u v) c2)
    have hswap : (∫ a : I, ∫ b : I, (1 - (b : ℝ)) * G a b) = ∫ v : I, ∫ u : I, (1 - (v : ℝ)) * G u v := by
      apply integral_integral_swap
      exact (c2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    have hnuT : nu (transpose G) = 24 * (∫ a : I, ∫ b : I, (1 - (b : ℝ)) * G a b) - 2 := rfl
    have hnu : nu G = 24 * (∫ v : I, ∫ u : I, (1 - (u : ℝ)) * G u v) - 2 := rfl
    change (nu G + nu (transpose G)) / 2 = 12 * (∫ v : I, ∫ u : I, (2 - (u : ℝ) - v) * G u v) - 2
    rw [hnu, hnuT, hswap, hout]
    ring

theorem proof1 : obligation1 := by
  refine ⟨fun x hx => hx, fun r hr => ?_⟩
  rw [Phi_eq r hr]
  obtain ⟨c, hc, -⟩ := paperD_parameter_exists_unique r ⟨hr.1, hr.2⟩
  have := Papers.Rockel2026XiBlest.blest_mem_Icc (paperD c)
  rw [paperD_on_boundary, hc] at this
  exact this

theorem proof2 : obligation2 := by
  refine ⟨fun x hx => ⟨hx, by linarith [hx.2], by linarith [hx.1]⟩, fun x hx => ?_⟩
  rw [Phi_eq x hx, Phi_eq (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩]
  rcases le_total 0 x with h | h
  · rw [rhoBoundary_neg x h]; ring
  · have := rhoBoundary_neg (-x) (by linarith)
    rw [neg_neg] at this
    rw [this]; ring

theorem proof3 : obligation3 := by
  refine ⟨by unfold meaningful3; definedness [], fun r s => ⟨?_, ?_⟩⟩
  · rintro ⟨F, hF, hr, hs⟩
    obtain ⟨K, rfl⟩ := exists_of_copulas hF
    rw [rho_cdfOf] at hr
    rw [nu_cdfOf] at hs
    obtain ⟨hr', hs'⟩ := (rho_fibre_complete r s).1 ⟨K, hr, hs⟩
    have hb := Papers.Rockel2026XiBlest.blest_mem_Icc K
    rw [hs] at hb
    rw [Phi_eq r ⟨hr'.1, hr'.2⟩]
    exact ⟨⟨⟨hr'.1, hr'.2⟩, hb.1, hb.2⟩, hs'.1, hs'.2⟩
  · rintro ⟨⟨hr, -⟩, h1, h2⟩
    rw [Phi_eq r hr] at h1 h2
    obtain ⟨K, hK1, hK2⟩ := (rho_fibre_complete r s).2 ⟨⟨hr.1, hr.2⟩, h1, h2⟩
    exact ⟨cdfOf K, copulas_cdfOf K, by rw [rho_cdfOf, hK1], by rw [nu_cdfOf, hK2]⟩

theorem proof4 : obligation4 := by
  refine ⟨by unfold meaningful4; definedness [copulas_survival (by assumption)], fun r hr => ?_⟩
  obtain ⟨c, hc, -⟩ := paperD_parameter_exists_unique r ⟨hr.1, hr.2⟩
  refine ⟨cdfOf (paperD c), copulas_cdfOf _, by rw [rho_cdfOf, hc],
    by rw [nu_cdfOf, paperD_on_boundary, hc, Phi_eq r hr], ?_, ?_⟩
  · intro F hF h1 h2
    obtain ⟨K, rfl⟩ := exists_of_copulas hF
    rw [rho_cdfOf] at h1
    rw [nu_cdfOf, Phi_eq r hr] at h2
    rw [paper_rho_upper_unique c K (by rw [h1, hc]) (by rw [h2, h1])]
  · rw [survival_cdfOf]
    refine ⟨copulas_cdfOf _, by rw [rho_cdfOf, Copula.spearmanRho_survivalCopula, hc],
      by rw [nu_cdfOf, nu_survival, paperD_on_boundary, hc, Phi_eq r hr], ?_⟩
    rintro F hF ⟨h1, h2⟩
    obtain ⟨K, rfl⟩ := exists_of_copulas hF
    rw [rho_cdfOf] at h1
    rw [nu_cdfOf, Phi_eq r hr] at h2
    rw [paper_rho_lower_unique c K (by rw [h1, hc]) (by rw [h2, h1])]

theorem proof8 : obligation8 := by
  refine ⟨by unfold meaningful8; definedness [copulas_survival (by assumption)], fun F hF => ?_⟩
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  rw [survival_cdfOf, rho_cdfOf, rho_cdfOf, nu_cdfOf, nu_cdfOf, eta_cdfOf, eta_cdfOf,
    Copula.spearmanRho_survivalCopula, nu_survival, eta_survival]
  exact ⟨rfl, rfl, rfl⟩

theorem proof9 : obligation9 := by
  refine ⟨by unfold meaningful9; definedness [copulas_reflection (by assumption)], fun F hF => ?_⟩
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  rw [reflection_cdfOf, rho_cdfOf, rho_cdfOf, nu_cdfOf, nu_cdfOf, Copula.spearmanRho_reflect_second,
    Papers.Rockel2026XiBlest.blest_reflect_second]
  exact ⟨rfl, rfl⟩

theorem proof10 : obligation10 := by
  refine ⟨fun c v => ⟨measurableSet_le (f := fun t : I => |(t : ℝ) + c - 1|)
    (g := fun _ => |(v : ℝ) + c - 1|) (by fun_prop) measurable_const, ?_, ?_⟩, fun c v => ?_⟩
  · intro h1
    have hc0 := c.2.1; have hc1 := c.2.2; have hv0 := v.2.1; have hv1 := v.2.2
    refine ⟨fun h2 => ?_, fun h3 => by linarith⟩
    rw [abs_of_nonpos (by linarith)] at h2 ⊢
    have : min (c : ℝ) (1 - c) ≤ c := min_le_left _ _
    linarith
  · intro h1
    have hc0 := c.2.1; have hc1 := c.2.2; have hv0 := v.2.1; have hv1 := v.2.2
    refine ⟨fun h2 h3 => ?_, fun h2 h3 _ => ?_⟩
    · rw [abs_of_nonneg (by linarith)] at h2 ⊢
      have : min (c : ℝ) (1 - c) ≤ 1 - c := min_le_right _ _
      linarith
    · apply h2
      rcases le_total (c : ℝ) (1 - c) with hm | hm
      · rw [min_eq_left hm, abs_le]; constructor <;> linarith
      · rw [min_eq_right hm, abs_le]; constructor <;> linarith
  · have hc0 := c.2.1; have hc1 := c.2.2; have hv0 := v.2.1; have hv1 := v.2.2
    rw [leb_rank, paperZeta_formula c v]
    by_cases h1 : (v : ℝ) ≤ 1 - 2 * c
    · rw [ite_eq_left h1]
      have hneg : (v : ℝ) + c - 1 ≤ 0 := by linarith
      have hm : min (c : ℝ) (1 - c) = c := min_eq_left (by linarith)
      rw [hm, abs_of_nonpos hneg]
      by_cases h2 : -((v : ℝ) + c - 1) ≤ c
      · rw [ite_eq_left h2]; linarith
      · rw [ite_eq_right h2, ite_eq_right (by linarith)]
    · rw [ite_eq_right h1]
      by_cases h2 : |(v : ℝ) + c - 1| ≤ min (c : ℝ) (1 - c)
      · rw [ite_eq_left h2, ite_eq_left h2]
      · rw [ite_eq_right h2, ite_eq_right h2]
        by_cases h3 : 2 - 2 * (c : ℝ) ≤ v
        · rw [ite_eq_left h3, ite_eq_left h3]
        · exfalso
          apply h2
          rcases le_total (c : ℝ) (1 - c) with hm | hm
          · rw [min_eq_left hm, abs_le]; constructor <;> linarith
          · rw [min_eq_right hm, abs_le]; constructor <;> linarith

theorem proof11 : obligation11 := by
  refine ⟨fun c => ⟨⟨copulas_D c, by norm_num, fun h1 h2 => ?_, fun h1 => ⟨by norm_num, fun h2 _ => ?_⟩⟩,
    fun _ => ⟨copulas_D c, by norm_num, fun h1 h2 => ?_, fun h1 => ⟨by norm_num, fun h2 _ => ?_⟩⟩⟩,
    fun c => ?_⟩
  · have : (c : ℝ) = 1 / 2 := le_antisymm h1 h2
    rw [this]; norm_num
  · exact h2 (le_of_lt (lt_of_not_ge h1))
  · have : (c : ℝ) = 1 / 2 := le_antisymm h1 h2
    rw [this]; norm_num
  · exact h2 (le_of_lt (lt_of_not_ge h1))
  · obtain ⟨h1, h2⟩ := paperD_values c
    rw [D_eq, rho_cdfOf, nu_cdfOf, h1, h2]
    by_cases h : (c : ℝ) ≤ 1 / 2
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, ite_eq_left h]; exact ⟨rfl, rfl⟩
    · have h' : (1 / 2 : ℝ) ≤ c := le_of_lt (lt_of_not_ge h)
      rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, ite_eq_right h, ite_eq_left h', ite_eq_left h']; exact ⟨rfl, rfl⟩

theorem proof12 : obligation12 := by
  refine ⟨⟨fun _ c => copulas_D c, fun _ => ⟨fun _ _ _ => ⟨fun c => copulas_D c, fun c => copulas_D c⟩,
    fun _ _ _ _ c => copulas_D c⟩⟩, ?_, ?_, ?_⟩
  · intro c
    rw [D_eq, rho_cdfOf]
    exact Copula.spearmanRho_mem_Icc _
  · intro c d h
    rw [D_eq, D_eq, rho_cdfOf, rho_cdfOf]
    exact paperD_strictMono (Subtype.coe_lt_coe.mp h)
  · intro r hr
    obtain ⟨c, hc, -⟩ := paperD_parameter_exists_unique r ⟨hr.1, hr.2⟩
    exact ⟨c, by rw [D_eq, rho_cdfOf, hc]⟩

theorem proof13 : obligation13 := by
  have hr : ∀ c : I, -1 ≤ rho (D c) ∧ rho (D c) ≤ 1 := fun c => by
    rw [D_eq, rho_cdfOf]; exact Copula.spearmanRho_mem_Icc _
  refine ⟨fun c => ⟨copulas_D c, copulas_D c, hr c, copulas_D c⟩, fun c => ?_⟩
  rw [Phi_eq _ (hr c), D_eq, nu_cdfOf, rho_cdfOf, paperD_on_boundary]

end Papers.Rockel2026ExactBlest.Source.Proofs
