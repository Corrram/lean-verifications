import Papers.Rockel2026ExactBlest.Source.Companion
import Papers.Rockel2026ExactBlest.Source.Families

/-! # Theorem 1.2, Lemma 4.1 and Corollaries 4.5 and 4.6

The claims of the article about the `(η, ν)` region, the families `A_w` and
`B_b`, the asymmetry `ν - η`, and the `(ν(C), ν(Cᵀ))` region, together with the
well-definedness of the definitions they use (`e_b`, `Υ`, `γ^T`, `T_w`, `A_w`,
`z_b`, `R_b`, `B_b`, `n_b`, `Λ`), proved through `Bridge` and `Families` from the
companion development. None of these results has a compiled proof in the text,
so the citation audit does not restrict these proofs. -/

namespace Papers.Rockel2026ExactBlest.Source.Proofs
open Papers.Rockel2026ExactBlest.Source Papers.Rockel2026ExactBlest.Source.Bridge
open Proofread MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026ExactBlest (paperA paperB paperEtaB paperUpsB etaGap etaGap_mem eta_fibre_displayed
  paper_eta_graph_extremizers paper_eta_random_extremizers eta_bottom_unique paperA_zero eta_paperA nu_paperA
  paperA_gap paperB_gap eta_paperB nu_paperB paperEtaB_strictMonoOn eta_paperA_strictMono paperA_eta_range
  paperEtaB_range paperEtaB_endpoints cube_root_spec threeQuarter paperA_threeQuarter_values
  paper_asymmetry_eq_iff etaGap_paperEtaB nu_transpose_fibre_gap gap_band_iff LambdaInv LambdaInv_mem
  Lambda_LambdaInv Lambda_strictMonoOn Lambda_mapsTo)

/-! ## Facts about the families -/

theorem eta_transpose_art {F : I → I → ℝ} (hF : copulas F) : eta (transpose F) = eta F := by
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  rw [transpose_cdfOf, eta_cdfOf, eta_cdfOf, Papers.Rockel2026ExactBlest.eta_transpose]

theorem copulas_B (b : ℝ) (h0 : 0 < b) (h1 : b ≤ 1 / 2) : copulas (B b) := by
  rcases lt_or_eq_of_le h1 with h | h
  · rw [B_eq b h0 h]; exact copulas_cdfOf _
  · subst h; rw [B_half_eq]; exact copulas_cdfOf _

theorem eta_B (b : ℝ) (h0 : 0 < b) (h1 : b ≤ 1 / 2) : eta (B b) = paperEtaB b := by
  rcases lt_or_eq_of_le h1 with h | h
  · rw [B_eq b h0 h, eta_cdfOf]; exact eta_paperB _ _
  · subst h; rw [B_half_eq, eta_cdfOf, eta_paperA]; norm_num [half, paperEtaB]

theorem nu_B (b : ℝ) (h0 : 0 < b) (h1 : b ≤ 1 / 2) : nu (B b) = -1 + (2 - b) * b ^ 3 / (1 - b) := by
  rcases lt_or_eq_of_le h1 with h | h
  · rw [B_eq b h0 h, nu_cdfOf]; exact nu_paperB _ _
  · subst h; rw [B_half_eq, nu_cdfOf, nu_paperA]; norm_num [half]

theorem e_mem (b : ℝ) (h0 : 0 < b) (h1 : b ≤ 1 / 2) : -1 ≤ e b ∧ e b ≤ 1 := by
  have h : paperEtaB b ∈ Icc (-1 : ℝ) (-3 / 4) := paperEtaB_range (unitOf b h0 h1) h1
  rw [e_eq]
  exact ⟨h.1, by linarith [h.2]⟩

theorem e_gt (b : ℝ) (h0 : 0 < b) (h1 : b ≤ 1 / 2) : -1 < e b := by
  have h := paperEtaB_strictMonoOn (show (0 : ℝ) ∈ Icc 0 (1 / 2) by norm_num) ⟨h0.le, h1⟩ h0
  rw [paperEtaB_endpoints.2.1] at h
  exact h

theorem e_half : e (1 / 2) = -(3 / 4) := by norm_num [e]

/-! ## Definitions -/

theorem defined7 : wellDefined7 := by
  intro x hx
  have : (0 : ℝ) < 1 - x := by linarith [hx.2]
  positivity

theorem eight_sq_ne {b : ℝ} (hb : b < 1 / 2) : ¬8 * (1 - b) ^ 2 = 0 := by
  have h : (0 : ℝ) < 1 - b := by linarith
  exact ne_of_gt (mul_pos (by norm_num) (pow_pos h 2))

theorem eight_sq_ne_le {b : ℝ} (hb : b ≤ 1 / 2) : ¬8 * (1 - b) ^ 2 = 0 := by
  have h : (0 : ℝ) < 1 - b := by linarith
  exact ne_of_gt (mul_pos (by norm_num) (pow_pos h 2))

theorem upsilon_exu (x : ℝ) (h : -1 < x ∧ x < -(3 / 4)) :
    ∃ y, (∃ b, (0 < b ∧ b < 1 / 2) ∧ e b = x ∧ y = b ^ 3 * (6 * b ^ 2 - 15 * b + 8) / (8 * (1 - b) ^ 2)) ∧
      ∀ y', (∃ b, (0 < b ∧ b < 1 / 2) ∧ e b = x ∧ y' = b ^ 3 * (6 * b ^ 2 - 15 * b + 8) / (8 * (1 - b) ^ 2)) →
        y' = y := by
  obtain ⟨b, hb, hb0, hpe, -⟩ := paper_eta_random_extremizers x ⟨h.1, by linarith [h.2]⟩
  refine ⟨_, ⟨b, ⟨hb0, hb⟩, hpe, rfl⟩, ?_⟩
  rintro y ⟨c, hc, hce, rfl⟩
  have : c = b := paperEtaB_injOn hc ⟨hb0, hb⟩ (hce.trans hpe.symm)
  subst this
  rfl

theorem defined8 : wellDefined8 := by
  unfold wellDefined8
  definedness [upsilon_exu _ ⟨‹_›, ‹_›⟩, eight_sq_ne ‹_›]

theorem defined13 : wellDefined13 := by
  intro f hf A hA
  exact hA.preimage (hf.prodMk measurable_id)

theorem defined18 : wellDefined18 := by
  intro w u
  have hu0 := u.2.1
  have hu1 := u.2.2
  have hw0 := w.2.1
  have hw1 := w.2.2
  refine ⟨⟨fun h1 h2 => by linarith [h1.2, h2.1], fun h1 h2 => ?_⟩, ?_, ?_⟩
  · exfalso
    by_cases h : (u : ℝ) ≤ 1 - w
    · exact h1 ⟨hu0, h⟩
    · exact h2 ⟨lt_of_not_ge h, hu1⟩
  · split_ifs <;> linarith
  · split_ifs <;> linarith

theorem defined19 : wellDefined19 := by
  intro w
  have hm := measurable_T w
  refine ⟨hm, ⟨probMeasure2_gamma hm, fun u => ?_, fun v => ?_⟩, hm⟩
  · change ((volume : Measure I) {t | t ≤ u}).toReal = u
    rw [show {t : I | t ≤ u} = Set.Iic u from rfl, unitInterval.volume_Iic, ENNReal.toReal_ofReal u.2.1]
  · change ((volume : Measure I) {t | T w t ≤ v}).toReal = v
    rw [show {t : I | T w t ≤ v} = T w ⁻¹' Set.Iic v from rfl, ← Measure.map_apply hm measurableSet_Iic,
      map_volume_T, unitInterval.volume_Iic, ENNReal.toReal_ofReal v.2.1]

theorem defined20 : wellDefined20 := by
  intro x hx
  have : (0 : ℝ) < 1 - x := by linarith [hx.2]
  positivity

theorem defined21 : wellDefined21 := by
  unfold wellDefined21
  intro b hb t
  have ht0 := t.2.1
  have ht1 := t.2.2
  have h2 : (0 : ℝ) < 2 * (1 - b) := by linarith [hb.2]
  have h1b : (1 : ℝ) - b ≠ 0 := by linarith [hb.2]
  have hzb : 2 * (1 - b) * z b = b := by rw [z]; field_simp
  have hzle : z b ≤ b := by nlinarith [hb.1, hb.2]
  have hG : (∀ x : ℝ, 0 < x → ¬(2 : ℝ) = 0) ∧ 0 < b ∧ b ≤ 1 / 2 := ⟨fun _ _ => two_ne_zero, hb⟩
  -- on the middle piece `z_b < t ≤ b`, necessarily `b < 1/2`
  have hmid : z b < t → (t : ℝ) ≤ b → 0 < 1 - 2 * b := by
    intro h1 h2'
    have := mul_lt_mul_of_pos_left (h1.trans_le h2') h2
    nlinarith [hb.1]
  refine ⟨⟨fun _ => hG, fun h1 => ⟨fun h2' => absurd h2'.1 (not_lt.mpr h1.2),
      fun h3 => absurd (h1.2.trans hzle) (not_le.mpr h3.1)⟩,
    fun h1 => ⟨hG, fun h2' => ⟨(hmid h2'.1 h2'.2).ne', fun h3 => absurd h2'.2 (not_le.mpr h3.1)⟩,
      fun h2' h3 _ => ?_⟩⟩, ?_, ?_⟩
  · by_cases ha : (t : ℝ) ≤ z b
    · exact h1 ⟨ht0, ha⟩
    · by_cases hb' : (t : ℝ) ≤ b
      · exact h2' ⟨lt_of_not_ge ha, hb'⟩
      · exact h3 ⟨lt_of_not_ge hb', ht1⟩
  · split_ifs with c1 c2 c3
    · nlinarith [hb.2]
    · have hp := hmid c2.1 c2.2
      apply div_nonneg _ hp.le
      apply mul_nonneg <;> linarith [hb.2, c2.2]
    · linarith
    · exact le_refl _
  · split_ifs with c1 c2 c3
    · have := mul_le_mul_of_nonneg_left c1.2 h2.le
      linarith
    · have hp := hmid c2.1 c2.2
      rw [div_le_one hp]
      have := mul_lt_mul_of_pos_left c2.1 h2
      nlinarith
    · linarith [c3.1, hb.1]
    · norm_num

theorem map_volume_R (b : ℝ) (h0 : 0 < b) (h1 : b ≤ 1 / 2) : (volume : Measure I).map (R b) = volume := by
  rcases lt_or_eq_of_le h1 with h | h
  · exact map_volume_R_lt b h0 h
  · subst h; exact map_volume_R_half

theorem probMeasure2_gammaUpper {f : I → I} (hf : Measurable f) : UnitSquare.probMeasure2 (gammaUpper f) := by
  refine ⟨(volume : Measure I).map (fun t => (f t, t)), inferInstance, fun A hA => ?_⟩
  rw [Measure.map_apply (by fun_prop : Measurable (fun t : I => (f t, t))) hA]
  rfl

theorem defined22 : wellDefined22 := by
  unfold wellDefined22
  intro b hb
  have hm := measurable_R b
  have hd : ((∀ x : ℝ, 0 < x → ¬(2 : ℝ) = 0) ∧ 0 < b ∧ b ≤ 1 / 2) := ⟨fun _ _ => two_ne_zero, hb⟩
  refine ⟨⟨hd, hm, hd⟩, ⟨probMeasure2_gammaUpper hm, fun u => ?_, fun v => ?_⟩, hd, hm, hd⟩
  · change ((volume : Measure I) {t | R b t ≤ u}).toReal = u
    rw [show {t : I | R b t ≤ u} = R b ⁻¹' Set.Iic u from rfl, ← Measure.map_apply hm measurableSet_Iic,
      map_volume_R b hb.1 hb.2, unitInterval.volume_Iic, ENNReal.toReal_ofReal u.2.1]
  · change ((volume : Measure I) {t | t ≤ v}).toReal = v
    rw [show {t : I | t ≤ v} = Set.Iic v from rfl, unitInterval.volume_Iic, ENNReal.toReal_ofReal v.2.1]

theorem defined23 : wellDefined23 := by
  intro x hx
  have : (0 : ℝ) < 1 - x := by linarith [hx.2]
  positivity

theorem lambda_exu (x : ℝ) (h : -1 < x ∧ x < -(7 / 8)) :
    ∃ y, (∃ b, (0 < b ∧ b < 1 / 2) ∧ n b = x ∧ y = -1 + (2 - b) * b ^ 3 / (1 - b)) ∧
      ∀ y', (∃ b, (0 < b ∧ b < 1 / 2) ∧ n b = x ∧ y' = -1 + (2 - b) * b ^ 3 / (1 - b)) → y' = y := by
  obtain ⟨hmono, hbij⟩ := Papers.Rockel2026ExactBlest.paperNB_bijOn
  obtain ⟨b, hb, hbx⟩ := hbij.surjOn ⟨h.1, by linarith [h.2]⟩
  refine ⟨_, ⟨b, hb, hbx, rfl⟩, ?_⟩
  rintro y ⟨c, hc, hcx, rfl⟩
  have : c = b := hmono.injOn hc hb (hcx.trans hbx.symm)
  subst this
  rfl

theorem defined24 : wellDefined24 := by
  unfold wellDefined24
  definedness [lambda_exu _ ⟨‹_›, ‹_›⟩]

/-! ## Theorem 1.2 -/

theorem proof5 : obligation5 := by
  refine ⟨by unfold meaningful5; definedness [], fun x hx => ?_⟩
  rw [Upsilon_eq x hx]
  have h := etaGap_mem x ⟨hx.1, hx.2⟩
  exact ⟨h.1, h.2⟩

theorem proof6 : obligation6 := by
  refine ⟨by unfold meaningful6; definedness [], fun e n => ⟨?_, ?_⟩⟩
  · rintro ⟨F, hF, he, hn⟩
    obtain ⟨K, rfl⟩ := exists_of_copulas hF
    rw [eta_cdfOf] at he
    rw [nu_cdfOf] at hn
    obtain ⟨hmem, hgap⟩ := (eta_fibre_displayed e n).1 ⟨K, he, hn⟩
    refine ⟨⟨hmem.1, hmem.2⟩, ?_⟩
    rw [Upsilon_eq e ⟨hmem.1, hmem.2⟩]
    exact hgap
  · rintro ⟨he, hn⟩
    rw [Upsilon_eq e he] at hn
    obtain ⟨K, hK1, hK2⟩ := (eta_fibre_displayed e n).2 ⟨⟨he.1, he.2⟩, hn⟩
    exact ⟨cdfOf K, copulas_cdfOf K, by rw [eta_cdfOf, hK1], by rw [nu_cdfOf, hK2]⟩

/-- The extremizers of Theorem 1.2 at `η = e`, from a library copula and its uniqueness. -/
theorem extremizers_of (e : ℝ) (he : -1 ≤ e ∧ e ≤ 1) (K : Copula 2)
    (h1 : Papers.Rockel2026ExactBlest.eta K = e)
    (h2 : Papers.Rockel2026XiBlest.blestNu K = e + etaGap e)
    (hu : ∀ C : Copula 2, Papers.Rockel2026ExactBlest.eta C = e →
      Papers.Rockel2026XiBlest.blestNu C = e + etaGap e → C = K)
    (hl : ∀ C : Copula 2, Papers.Rockel2026ExactBlest.eta C = e →
      Papers.Rockel2026XiBlest.blestNu C = e - etaGap e → C = K.transpose) :
    ∃ F, copulas F ∧ eta F = e ∧ nu F = e + Upsilon e ∧
      (∀ G, copulas G → eta G = e → nu G = e + Upsilon e → G = F) ∧
      copulas (transpose F) ∧ eta (transpose F) = e ∧ nu (transpose F) = e - Upsilon e ∧
      ∀ G, copulas G → eta G = e ∧ nu G = e - Upsilon e → G = transpose F := by
  rw [Upsilon_eq e he]
  refine ⟨cdfOf K, copulas_cdfOf K, by rw [eta_cdfOf, h1], by rw [nu_cdfOf, h2], ?_, ?_, ?_, ?_, ?_⟩
  · intro G hG hGe hGn
    obtain ⟨L, rfl⟩ := exists_of_copulas hG
    rw [eta_cdfOf] at hGe
    rw [nu_cdfOf] at hGn
    rw [hu L hGe hGn]
  · rw [transpose_cdfOf]; exact copulas_cdfOf _
  · rw [transpose_cdfOf, eta_cdfOf, Papers.Rockel2026ExactBlest.eta_transpose, h1]
  · rw [transpose_cdfOf, nu_cdfOf, Papers.Rockel2026ExactBlest.nu_transpose, h1, h2]; ring
  · rintro G hG ⟨hGe, hGn⟩
    obtain ⟨L, rfl⟩ := exists_of_copulas hG
    rw [eta_cdfOf] at hGe
    rw [nu_cdfOf] at hGn
    rw [hl L hGe hGn, transpose_cdfOf]

theorem proof7 : obligation7 := by
  refine ⟨by unfold meaningful7; definedness [copulas_transpose (by assumption)], fun e he => ?_⟩
  by_cases hg : -(3 / 4) ≤ e
  · obtain ⟨w, -, -, h1, h2, hu, hl⟩ := paper_eta_graph_extremizers e ⟨by linarith, he.2⟩
    exact extremizers_of e he _ h1 h2 hu hl
  · by_cases hb : e = -1
    · subst hb
      have h1 : Papers.Rockel2026ExactBlest.eta (paperA 0) = -1 := by rw [eta_paperA]; norm_num
      have h1t : Papers.Rockel2026ExactBlest.eta (paperA 0).transpose = -1 := by
        rw [Papers.Rockel2026ExactBlest.eta_transpose, h1]
      refine extremizers_of (-1) he (paperA 0) h1 ?_ ?_ ?_
      · rw [nu_paperA, Papers.Rockel2026ExactBlest.etaGap_bottom]; norm_num
      · intro C hC _; exact eta_bottom_unique C _ hC h1
      · intro C hC _; exact eta_bottom_unique C _ hC h1t
    · obtain ⟨b, hb', -, -, h1, h2, hu, hl⟩ :=
        paper_eta_random_extremizers e ⟨lt_of_le_of_ne he.1 (Ne.symm hb), by linarith⟩
      exact extremizers_of e he _ h1 h2 hu hl

/-! ## Lemma 4.1 -/

theorem proof29 : obligation29 := by
  refine ⟨by unfold meaningful29; definedness [], fun b hb => ?_⟩
  have h1 : (0 : ℝ) < 2 * (1 - b) := by linarith [hb.2]
  constructor
  · exact div_pos hb.1 h1
  · rw [z, div_le_iff₀ h1]; linarith [hb.2]

theorem proof30 : obligation30 := by
  refine ⟨by unfold meaningful30; definedness [copulas_A _, copulas_B _ ‹_› ‹_›, eight_sq_ne_le ‹_›],
    fun w b hb => ?_⟩
  refine ⟨by rw [A_eq, eta_cdfOf, eta_paperA], by rw [A_eq, nu_cdfOf, nu_paperA], ⟨?_, rfl⟩, nu_B b hb.1 hb.2⟩
  rw [eta_B b hb.1 hb.2]; rfl

theorem proof31 : obligation31 := by
  refine ⟨by unfold meaningful31; definedness [copulas_A _], fun w => ?_⟩
  rw [A_eq, nu_cdfOf, eta_cdfOf]
  exact paperA_gap w

theorem proof32 : obligation32 := by
  refine ⟨by unfold meaningful32; definedness [copulas_B _ ‹_› ‹_›, (e_mem _ ‹_› ‹_›).1, (e_mem _ ‹_› ‹_›).2],
    fun b hb => ?_⟩
  rw [Upsilon_eq (e b) (e_mem b hb.1 hb.2)]
  rcases lt_or_eq_of_le hb.2 with h | h
  · rw [B_eq b hb.1 h, nu_cdfOf, eta_cdfOf, e_eq, etaGap_paperEtaB b hb.1 h]
    exact paperB_gap _ _
  · subst h
    rw [B_half_eq, nu_cdfOf, eta_cdfOf, paperA_gap, e_half]
    unfold etaGap Papers.Rockel2026ExactBlest.graphGap
    rw [ite_eq_right (by norm_num)]
    have h4 : ((1 : ℝ) + -(3 / 4)) ^ (4 / 3 : ℝ) = 2 ^ (-(8 / 3) : ℝ) := by
      rw [show (1 : ℝ) + -(3 / 4) = 2 ^ (-2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h4, ← Real.rpow_add (by norm_num)]
    norm_num [half]

theorem proof33 : obligation33 := by
  refine ⟨by unfold meaningful33; definedness [copulas_A _, copulas_B _ ‹_› ‹_›], ?_, ?_⟩
  · intro v w hvw
    rw [A_eq, A_eq, eta_cdfOf, eta_cdfOf]
    exact eta_paperA_strictMono hvw
  · intro b c hb hc hbc
    rw [eta_B b hb.1 hb.2, eta_B c hc.1 hc.2]
    exact paperEtaB_strictMonoOn ⟨hb.1.le, hb.2⟩ ⟨hc.1.le, hc.2⟩ hbc

theorem proof34 : obligation34 := by
  refine ⟨by unfold meaningful34; definedness [copulas_A _], ?_, ?_⟩
  · intro x hx
    have h := paperA_eta_range (Set.projIcc (0 : ℝ) 1 zero_le_one x)
      (by rw [coe_projIcc_of_mem (by linarith [hx.1]) hx.2]; exact hx.1)
    rw [A_eq, eta_cdfOf]
    exact ⟨by linarith [h.1], h.2⟩
  · intro y hy
    obtain ⟨hl, hu, hcube⟩ := cube_root_spec y ⟨by linarith [hy.1], hy.2⟩
    refine ⟨((1 + y) / 2) ^ (1 / 3 : ℝ), ⟨hl, hu⟩, ?_⟩
    rw [A_eq, eta_cdfOf, eta_paperA, coe_projIcc_of_mem (by linarith) hu, hcube]
    ring

theorem proof35 : obligation35 := by
  refine ⟨by unfold meaningful35; definedness [copulas_B _ ‹_› ‹_›], ?_, ?_⟩
  · intro b hb
    rw [eta_B b hb.1 hb.2]
    have h : paperEtaB b ≤ -3 / 4 := (paperEtaB_range (unitOf b hb.1 hb.2) hb.2).2
    exact ⟨e_gt b hb.1 hb.2, by linarith⟩
  · intro y hy
    rcases lt_or_eq_of_le hy.2 with h | h
    · obtain ⟨b, hb, hb0, hpe, -⟩ := paper_eta_random_extremizers y ⟨hy.1, by linarith⟩
      exact ⟨b, ⟨hb0, hb.le⟩, by rw [eta_B b hb0 hb.le]; exact hpe⟩
    · refine ⟨1 / 2, ⟨by norm_num, le_refl _⟩, ?_⟩
      rw [eta_B _ (by norm_num) (le_refl _), h]
      norm_num [paperEtaB]

/-! ## Corollary 4.5 -/

theorem gap_le (F : I → I → ℝ) (hF : copulas F) : |nu F - eta F| ≤ 27 / 128 := by
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  rw [nu_cdfOf, eta_cdfOf]
  have h := (eta_fibre_displayed _ _).1 ⟨K, rfl, rfl⟩
  exact h.2.trans (etaGap_mem _ h.1).2

theorem nu_sub_nu_transpose (F : I → I → ℝ) (hF : copulas F) :
    nu F - nu (transpose F) = 2 * (nu F - eta F) := by
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  rw [transpose_cdfOf, nu_cdfOf, nu_cdfOf, eta_cdfOf, Papers.Rockel2026ExactBlest.nu_transpose]
  ring

theorem proof36 : obligation36 := by
  refine ⟨by unfold meaningful36; definedness [copulas_transpose (by assumption)], fun F hF => ?_⟩
  refine ⟨gap_le F hF, ?_⟩
  rw [nu_sub_nu_transpose F hF, abs_mul, abs_two]
  constructor <;> intro h <;> linarith

theorem threeQuarter_eq : Set.projIcc (0 : ℝ) 1 zero_le_one (3 / 4) = threeQuarter := by
  apply Subtype.ext
  rw [coe_projIcc_of_mem (by norm_num) (by norm_num)]
  rfl

theorem asymmetry_cases (F : I → I → ℝ) (hF : copulas F) (h : |nu F - eta F| = 27 / 128) :
    F = A threeQuarter ∨ F = transpose (A threeQuarter) := by
  obtain ⟨K, rfl⟩ := exists_of_copulas hF
  rw [nu_cdfOf, eta_cdfOf] at h
  rw [A_eq, transpose_cdfOf]
  rcases (paper_asymmetry_eq_iff K).1 h with h' | h'
  · exact Or.inl (by rw [h'])
  · exact Or.inr (by rw [h'])

theorem gap_A34 : nu (A threeQuarter) - eta (A threeQuarter) = 27 / 128 := by
  rw [A_eq, nu_cdfOf, eta_cdfOf, paperA_threeQuarter_values.1, paperA_threeQuarter_values.2]
  norm_num

theorem gap_A34_transpose :
    nu (transpose (A threeQuarter)) - eta (transpose (A threeQuarter)) = -(27 / 128) := by
  have h1 := nu_sub_nu_transpose (A threeQuarter) (copulas_A _)
  rw [eta_transpose_art (copulas_A _)]
  linarith [gap_A34]

theorem proof37 : obligation37 := by
  refine ⟨by unfold meaningful37; definedness [copulas_A _], ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro F hF; exact (abs_le.mp (gap_le F hF)).2
  · rw [threeQuarter_eq]; exact ⟨copulas_A _, gap_A34⟩
  · intro F hF h
    rw [threeQuarter_eq]
    rcases asymmetry_cases F hF (by rw [h]; norm_num) with h' | h'
    · exact h'
    · subst h'; linarith [gap_A34_transpose]
  · rw [threeQuarter_eq, A_eq, eta_cdfOf, paperA_threeQuarter_values.1]; norm_num
  · rw [threeQuarter_eq, A_eq, nu_cdfOf, paperA_threeQuarter_values.2]

theorem proof38 : obligation38 := by
  refine ⟨by unfold meaningful38; definedness [copulas_A _, copulas_transpose (copulas_A _)], ?_, ⟨?_, ?_⟩, ?_⟩
  · intro F hF; exact (abs_le.mp (gap_le F hF)).1
  · rw [threeQuarter_eq]; exact copulas_transpose (copulas_A _)
  · rw [threeQuarter_eq]; exact gap_A34_transpose
  · intro F hF h
    rw [threeQuarter_eq]
    rcases asymmetry_cases F hF (by rw [h]; norm_num) with h' | h'
    · subst h'; linarith [gap_A34]
    · exact h'

/-! ## Corollary 4.6 -/

theorem proof39 : obligation39 := by
  refine ⟨by unfold meaningful39; definedness [], fun x hx => ?_⟩
  rw [Lambda_eq x hx]
  exact Lambda_mapsTo ⟨hx.1, hx.2⟩

theorem mid_mem {x s : ℝ} (hx : -1 ≤ x ∧ x ≤ 1) (hs : -1 ≤ s ∧ s ≤ 1) :
    -1 ≤ (x + s) / 2 ∧ (x + s) / 2 ≤ 1 :=
  ⟨by linarith [hx.1, hs.1], by linarith [hx.2, hs.2]⟩

/-- The inverse `Λ⁻¹(n)` written in the article is `LambdaInv n`. -/
theorem LambdaInv_art (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) :
    (Classical.epsilon fun y : ℝ => (-1 ≤ y ∧ y ≤ 1) ∧ Lambda y = x) = LambdaInv x := by
  have hm := LambdaInv_mem x ⟨hx.1, hx.2⟩
  apply epsilon_eq_of_unique ⟨⟨hm.1, hm.2⟩, by rw [Lambda_eq _ ⟨hm.1, hm.2⟩, Lambda_LambdaInv x ⟨hx.1, hx.2⟩]⟩
  rintro y ⟨hy, hyx⟩
  rw [Lambda_eq y hy] at hyx
  exact Lambda_strictMonoOn.injOn ⟨hy.1, hy.2⟩ hm (hyx.trans (Lambda_LambdaInv x ⟨hx.1, hx.2⟩).symm)

theorem lambda_inv_exu (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) :
    ∃ y, ((-1 ≤ y ∧ y ≤ 1) ∧ Lambda y = x) ∧ ∀ y', (-1 ≤ y' ∧ y' ≤ 1) ∧ Lambda y' = x → y' = y := by
  have hm := LambdaInv_mem x ⟨hx.1, hx.2⟩
  refine ⟨LambdaInv x, ⟨⟨hm.1, hm.2⟩, by rw [Lambda_eq _ ⟨hm.1, hm.2⟩, Lambda_LambdaInv x ⟨hx.1, hx.2⟩]⟩, ?_⟩
  rintro y ⟨hy, hyx⟩
  rw [Lambda_eq y hy] at hyx
  exact Lambda_strictMonoOn.injOn ⟨hy.1, hy.2⟩ hm (hyx.trans (Lambda_LambdaInv x ⟨hx.1, hx.2⟩).symm)

theorem proof40 : obligation40 := by
  refine ⟨by unfold meaningful40; definedness [copulas_transpose ‹_›, lambda_inv_exu _ ⟨‹_›, ‹_›⟩], ?_, ?_⟩
  · intro x s
    constructor
    · rintro ⟨F, hF, hx, hs⟩
      obtain ⟨K, rfl⟩ := exists_of_copulas hF
      rw [nu_cdfOf] at hx
      rw [transpose_cdfOf, nu_cdfOf] at hs
      obtain ⟨h1, h2, h3⟩ := (nu_transpose_fibre_gap x s).1 ⟨K, hx, hs⟩
      refine ⟨⟨⟨h1.1, h1.2⟩, h2.1, h2.2⟩, ?_⟩
      rw [Upsilon_eq _ (mid_mem ⟨h1.1, h1.2⟩ ⟨h2.1, h2.2⟩)]
      exact h3
    · rintro ⟨⟨hx, hs⟩, h⟩
      rw [Upsilon_eq _ (mid_mem hx hs)] at h
      obtain ⟨K, h1, h2⟩ := (nu_transpose_fibre_gap x s).2 ⟨⟨hx.1, hx.2⟩, ⟨hs.1, hs.2⟩, h⟩
      exact ⟨cdfOf K, copulas_cdfOf K, by rw [nu_cdfOf, h1], by rw [transpose_cdfOf, nu_cdfOf, h2]⟩
  · intro x s
    constructor
    · rintro ⟨⟨hx, hs⟩, h⟩
      refine ⟨⟨hx, hs⟩, ?_⟩
      rw [Upsilon_eq _ (mid_mem hx hs)] at h
      rw [LambdaInv_art x hx, Lambda_eq x hx]
      exact (gap_band_iff x s ⟨hx.1, hx.2⟩ ⟨hs.1, hs.2⟩).1 h
    · rintro ⟨⟨hx, hs⟩, h⟩
      refine ⟨⟨hx, hs⟩, ?_⟩
      rw [LambdaInv_art x hx, Lambda_eq x hx] at h
      rw [Upsilon_eq _ (mid_mem hx hs)]
      exact (gap_band_iff x s ⟨hx.1, hx.2⟩ ⟨hs.1, hs.2⟩).2 h

theorem proof41 : obligation41 := by
  refine ⟨by unfold meaningful41; definedness [copulas_transpose ‹_›, lambda_inv_exu _ ⟨‹_›, ‹_›⟩],
    fun n hn => ?_⟩
  have hn' : n ∈ Icc (-1 : ℝ) 1 := ⟨hn.1, hn.2⟩
  rw [Lambda_eq n hn, LambdaInv_art n hn]
  refine ⟨⟨fun F hF hFn => ?_, ?_⟩, ⟨fun F hF hFn => ?_, ?_⟩⟩
  · obtain ⟨K, rfl⟩ := exists_of_copulas hF
    rw [nu_cdfOf] at hFn
    rw [transpose_cdfOf, nu_cdfOf]
    exact (Papers.Rockel2026ExactBlest.nu_transpose_isGreatest n hn').2 ⟨K, hFn, rfl⟩
  · obtain ⟨K, ⟨hK1, hK2⟩, hu⟩ := Papers.Rockel2026ExactBlest.nu_transpose_max_exists_unique n hn'
    refine ⟨cdfOf K, copulas_cdfOf K, by rw [nu_cdfOf, hK1], by rw [transpose_cdfOf, nu_cdfOf, hK2],
      fun G hG hGn hGm => ?_⟩
    obtain ⟨L, rfl⟩ := exists_of_copulas hG
    rw [nu_cdfOf] at hGn
    rw [transpose_cdfOf, nu_cdfOf] at hGm
    rw [hu L ⟨hGn, hGm⟩]
  · obtain ⟨K, rfl⟩ := exists_of_copulas hF
    rw [nu_cdfOf] at hFn
    rw [transpose_cdfOf, nu_cdfOf]
    exact (Papers.Rockel2026ExactBlest.nu_transpose_isLeast n hn').2 ⟨K, hFn, rfl⟩
  · obtain ⟨K, ⟨hK1, hK2⟩, hu⟩ := Papers.Rockel2026ExactBlest.nu_transpose_min_exists_unique n hn'
    refine ⟨cdfOf K, copulas_cdfOf K, by rw [nu_cdfOf, hK1], by rw [transpose_cdfOf, nu_cdfOf, hK2],
      fun G hG hGn hGm => ?_⟩
    obtain ⟨L, rfl⟩ := exists_of_copulas hG
    rw [nu_cdfOf] at hGn
    rw [transpose_cdfOf, nu_cdfOf] at hGm
    rw [hu L ⟨hGn, hGm⟩]

end Papers.Rockel2026ExactBlest.Source.Proofs
