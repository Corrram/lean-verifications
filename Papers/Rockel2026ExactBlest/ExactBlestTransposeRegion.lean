import Papers.Rockel2026ExactBlest.ExactBlestTranspose

/-!
# The exact region of `(ν(C), ν(Cᵀ))`

The corollary on Blest's coefficient and its transpose in exact-blest-regions.tex: both
displayed descriptions of the region (through `Υ` and through `Λ`), the two boundary curves,
unique maximizers and minimizers in every fibre, their identification with the extremal
families, the closed-form bound stated in the introduction, and continuity of `Υ`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval Topology
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest

noncomputable section
set_option maxHeartbeats 4000000

/-! ## Elementary properties of `Υ` -/

theorem etaGap_nonneg (e : ℝ) (he : e ∈ Icc (-1 : ℝ) 1) : 0 ≤ etaGap e := by
  obtain ⟨C, hc, _⟩ := eta_upper_exists_unique e he
  have h := (eta_fibre_displayed e (blestNu C)).mp ⟨C, hc.1, rfl⟩
  exact le_trans (abs_nonneg _) h.2

theorem upper_curve_mem (e : ℝ) (he : e ∈ Icc (-1 : ℝ) 1) :
    e + etaGap e ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨C, hc, _⟩ := eta_upper_exists_unique e he
  rw [← hc.2]
  exact blest_mem_Icc C

theorem lower_curve_mem (e : ℝ) (he : e ∈ Icc (-1 : ℝ) 1) :
    e - etaGap e ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨C, hc, _⟩ := eta_lower_exists_unique e he
  rw [← hc.2]
  exact blest_mem_Icc C

theorem etaGap_top : etaGap 1 = 0 := by
  have h := etaGap_graph 0 (by norm_num)
  rw [eta_familyA, nu_familyA] at h
  norm_num at h
  exact h

/-- `Υ` maps `[-1,1]` into `[0,27/128]`, as stated where `Υ` is defined. -/
theorem etaGap_mem (e : ℝ) (he : e ∈ Icc (-1 : ℝ) 1) : etaGap e ∈ Icc (0 : ℝ) (27 / 128) := by
  refine ⟨etaGap_nonneg e he, ?_⟩
  obtain ⟨C, hc, _⟩ := eta_upper_exists_unique e he
  have h := nu_eta_upper C
  rw [hc.1, hc.2] at h
  linarith

/-! ## The boundary function `Λ` along the boundary of the `(η,ν)`-region -/

theorem Lambda_transposeParam (a : I) (ha : (1 / 2 : ℝ) < a) (ha1 : (a : ℝ) < 1) :
    Lambda (transposeParam a) = nuB a := by
  rw [Lambda_param_branch _ (transposeParam_open a ha ha1), lambdaParameter_value a ha.le]

theorem Lambda_familyA (w : I) (hw : (w : ℝ) ≤ 1 / 2) :
    Lambda (blestNu (familyA w).transpose) = blestNu (familyA w) := by
  have hs0 : 0 ≤ 1 - (w : ℝ) := sub_nonneg.mpr w.property.2
  have hs : (1 / 2 : ℝ) ≤ 1 - w := by linarith
  have h4 : (1 / 2 : ℝ) ^ 4 ≤ (1 - (w : ℝ)) ^ 4 := pow_le_pow_left₀ (by norm_num) hs 4
  norm_num at h4
  rw [nu_transpose_familyA, Lambda_closed_branch _ (by linarith), lambdaClosed_param _ hs0,
    nu_familyA]
  ring

/-- `L` maps the lower boundary curve of the `(η,ν)`-region onto the graph of `Λ`. -/
theorem Lambda_curve (e : ℝ) (he : e ∈ Icc (-1 : ℝ) 1) :
    Lambda (e - etaGap e) = e + etaGap e := by
  by_cases hg : -3 / 4 ≤ e
  · obtain ⟨w, hw, _⟩ := graph_parameter_exists_unique e ⟨hg, he.2⟩
    have h1 : e - etaGap e = blestNu (familyA w).transpose := by
      rw [← hw.2, etaGap_graph w hw.1, nu_transpose]; ring
    have h2 : e + etaGap e = blestNu (familyA w) := by
      rw [← hw.2, etaGap_graph w hw.1]; ring
    rw [h1, h2, Lambda_familyA w hw.1]
  · by_cases hb : e = -1
    · subst e
      rw [etaGap_bottom, sub_zero, add_zero, Lambda_neg_one]
    · obtain ⟨a, ha, ha1, hav⟩ := randomized_parameter_exists_open e
        ⟨lt_of_le_of_ne he.1 (Ne.symm hb), by linarith⟩
      have h0 : (a : ℝ) ≠ 0 := by linarith
      have h1 : e - etaGap e = transposeParam a := by
        rw [← hav, etaGap_randomized a ha, transposeParam_eq _ h0]; ring
      have h2 : e + etaGap e = nuB a := by
        rw [← hav, etaGap_randomized a ha]; ring
      rw [h1, h2, Lambda_transposeParam a ha ha1]

/-- Both coordinates of the boundary curves are strictly increasing in `e`. -/
theorem lowerCurve_strictMonoOn :
    StrictMonoOn (fun e => e - etaGap e) (Icc (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  show x - etaGap x < y - etaGap y
  by_contra h
  push Not at h
  have hl := Lambda_strictMonoOn.monotoneOn (lower_curve_mem y hy) (lower_curve_mem x hx) h
  rw [Lambda_curve y hy, Lambda_curve x hx] at hl
  linarith

theorem upperCurve_strictMonoOn :
    StrictMonoOn (fun e => e + etaGap e) (Icc (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  show x + etaGap x < y + etaGap y
  rw [← Lambda_curve x hx, ← Lambda_curve y hy]
  exact Lambda_strictMonoOn (lower_curve_mem x hx) (lower_curve_mem y hy)
    (lowerCurve_strictMonoOn hx hy hxy)

/-! ## The inverse `Λ⁻¹` -/

/-- The inverse of `Λ` on `[-1,1]`. -/
def LambdaInv : ℝ → ℝ := Function.invFunOn Lambda (Icc (-1 : ℝ) 1)

theorem LambdaInv_mem (n : ℝ) (hn : n ∈ Icc (-1 : ℝ) 1) : LambdaInv n ∈ Icc (-1 : ℝ) 1 :=
  Function.invFunOn_mem (Lambda_surjOn hn)

theorem Lambda_LambdaInv (n : ℝ) (hn : n ∈ Icc (-1 : ℝ) 1) : Lambda (LambdaInv n) = n :=
  Function.invFunOn_eq (Lambda_surjOn hn)

theorem LambdaInv_Lambda (m : ℝ) (hm : m ∈ Icc (-1 : ℝ) 1) : LambdaInv (Lambda m) = m :=
  Lambda_strictMonoOn.injOn (LambdaInv_mem _ (Lambda_mapsTo hm)) hm
    (Lambda_LambdaInv _ (Lambda_mapsTo hm))

theorem LambdaInv_le_iff (n m : ℝ) (hn : n ∈ Icc (-1 : ℝ) 1) (hm : m ∈ Icc (-1 : ℝ) 1) :
    LambdaInv n ≤ m ↔ n ≤ Lambda m := by
  rw [← Lambda_strictMonoOn.le_iff_le (LambdaInv_mem n hn) hm, Lambda_LambdaInv n hn]

theorem LambdaInv_bijOn : BijOn LambdaInv (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) :=
  Lambda_bijOn.symm Lambda_bijOn.invOn_invFunOn.symm

theorem LambdaInv_strictMonoOn : StrictMonoOn LambdaInv (Icc (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  by_contra h
  push Not at h
  have := Lambda_strictMonoOn.monotoneOn (LambdaInv_mem y hy) (LambdaInv_mem x hx) h
  rw [Lambda_LambdaInv y hy, Lambda_LambdaInv x hx] at this
  linarith

theorem LambdaInv_le_self (n : ℝ) (hn : n ∈ Icc (-1 : ℝ) 1) : LambdaInv n ≤ n := by
  rw [LambdaInv_le_iff n n hn hn]
  exact Lambda_ge_self n hn

theorem LambdaInv_neg_one : LambdaInv (-1) = -1 := by
  have h := LambdaInv_Lambda (-1) (by norm_num)
  rwa [Lambda_neg_one] at h

/-! ## The two descriptions of the region -/

/-- The first displayed description: `|n - m| ≤ 2 Υ((n+m)/2)`. -/
theorem nu_transpose_fibre_gap (n m : ℝ) :
    (∃ C : Copula 2, blestNu C = n ∧ blestNu C.transpose = m) ↔
      n ∈ Icc (-1 : ℝ) 1 ∧ m ∈ Icc (-1 : ℝ) 1 ∧ |n - m| ≤ 2 * etaGap ((n + m) / 2) := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    refine ⟨blest_mem_Icc C, blest_mem_Icc _, ?_⟩
    have h := (eta_fibre_displayed (eta C) (blestNu C)).mp ⟨C, rfl, rfl⟩
    have he : (blestNu C + blestNu C.transpose) / 2 = eta C := rfl
    have hd : blestNu C - blestNu C.transpose = 2 * (blestNu C - eta C) := by
      rw [nu_transpose]; ring
    rw [he, hd, abs_mul, abs_two]
    linarith [h.2]
  · rintro ⟨hn, hm, hg⟩
    have he : (n + m) / 2 ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hn.1, hm.1], by linarith [hn.2, hm.2]⟩
    have hd : |n - (n + m) / 2| ≤ etaGap ((n + m) / 2) := by
      have h2 : n - (n + m) / 2 = (n - m) / 2 := by ring
      rw [h2, abs_div, abs_two]
      linarith
    obtain ⟨C, hc, hv⟩ := (eta_fibre_displayed _ n).mpr ⟨he, hd⟩
    refine ⟨C, hv, ?_⟩
    rw [nu_transpose, hc, hv]
    ring

theorem nu_transpose_region_gap :
    Set.range (fun C : Copula 2 => (blestNu C, blestNu C.transpose)) =
      {p : ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2 ∈ Icc (-1 : ℝ) 1 ∧
        |p.1 - p.2| ≤ 2 * etaGap ((p.1 + p.2) / 2)} := by
  ext ⟨n, m⟩
  simpa only [Set.mem_range, Set.mem_ofPred_eq, Prod.mk.injEq] using nu_transpose_fibre_gap n m

/-- The band between the graphs of `Λ⁻¹` and `Λ` is the band `|n - m| ≤ 2 Υ((n+m)/2)`. -/
theorem gap_band_iff (n m : ℝ) (hn : n ∈ Icc (-1 : ℝ) 1) (hm : m ∈ Icc (-1 : ℝ) 1) :
    |n - m| ≤ 2 * etaGap ((n + m) / 2) ↔ LambdaInv n ≤ m ∧ m ≤ Lambda n := by
  have he : (n + m) / 2 ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hn.1, hm.1], by linarith [hn.2, hm.2]⟩
  have hlo := lower_curve_mem _ he
  have hcurve := Lambda_curve _ he
  rw [LambdaInv_le_iff n m hn hm]
  constructor
  · intro h
    have h' := abs_le.mp h
    constructor
    · have hm' : (n + m) / 2 - etaGap ((n + m) / 2) ≤ m := by linarith [h'.2]
      have hmono := Lambda_strictMonoOn.monotoneOn hlo hm hm'
      rw [hcurve] at hmono
      linarith [h'.2]
    · have hn' : (n + m) / 2 - etaGap ((n + m) / 2) ≤ n := by linarith [h'.1]
      have hmono := Lambda_strictMonoOn.monotoneOn hlo hn hn'
      rw [hcurve] at hmono
      linarith [h'.1]
  · rintro ⟨h1, h2⟩
    rw [abs_le]
    constructor
    · by_contra hc
      push Not at hc
      have hn' : n < (n + m) / 2 - etaGap ((n + m) / 2) := by linarith
      have hlt := Lambda_strictMonoOn hn hlo hn'
      rw [hcurve] at hlt
      linarith
    · by_contra hc
      push Not at hc
      have hm' : m < (n + m) / 2 - etaGap ((n + m) / 2) := by linarith
      have hlt := Lambda_strictMonoOn hm hlo hm'
      rw [hcurve] at hlt
      linarith

/-- The second displayed description: `Λ⁻¹(n) ≤ m ≤ Λ(n)`. -/
theorem nu_transpose_fibre (n m : ℝ) :
    (∃ C : Copula 2, blestNu C = n ∧ blestNu C.transpose = m) ↔
      n ∈ Icc (-1 : ℝ) 1 ∧ m ∈ Icc (-1 : ℝ) 1 ∧ LambdaInv n ≤ m ∧ m ≤ Lambda n := by
  rw [nu_transpose_fibre_gap]
  constructor
  · rintro ⟨hn, hm, h⟩
    exact ⟨hn, hm, (gap_band_iff n m hn hm).mp h⟩
  · rintro ⟨hn, hm, h⟩
    exact ⟨hn, hm, (gap_band_iff n m hn hm).mpr h⟩

theorem nu_transpose_region :
    Set.range (fun C : Copula 2 => (blestNu C, blestNu C.transpose)) =
      {p : ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2 ∈ Icc (-1 : ℝ) 1 ∧
        LambdaInv p.1 ≤ p.2 ∧ p.2 ≤ Lambda p.1} := by
  ext ⟨n, m⟩
  simpa only [Set.mem_range, Set.mem_ofPred_eq, Prod.mk.injEq] using nu_transpose_fibre n m

/-- The fibre above `n` is the interval `[Λ⁻¹(n), Λ(n)]`. -/
theorem nu_transpose_fibre_eq (n : ℝ) (hn : n ∈ Icc (-1 : ℝ) 1) :
    {m | ∃ C : Copula 2, blestNu C = n ∧ blestNu C.transpose = m} =
      Icc (LambdaInv n) (Lambda n) := by
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  rw [nu_transpose_fibre]
  constructor
  · rintro ⟨_, _, h⟩
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨hn, ⟨le_trans (LambdaInv_mem n hn).1 h1, le_trans h2 (Lambda_mapsTo hn).2⟩, h1, h2⟩

/-- The `(η,ν)`-region is the image of the `(ν,νᵀ)`-region under `(n,m) ↦ ((n+m)/2, n)`. -/
theorem eta_nu_region_linear_image :
    Set.range (fun C : Copula 2 => (eta C, blestNu C)) =
      (fun p : ℝ × ℝ => ((p.1 + p.2) / 2, p.1)) ''
        Set.range (fun C : Copula 2 => (blestNu C, blestNu C.transpose)) := by
  ext q
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨(blestNu C, blestNu C.transpose), ⟨C, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨C, rfl⟩, rfl⟩
    exact ⟨C, rfl⟩

/-! ## Boundary curves -/

theorem nu_transpose_max_lower (C : Copula 2)
    (hC : blestNu C.transpose = Lambda (blestNu C)) :
    blestNu C = eta C - etaGap (eta C) := by
  have hn := blest_mem_Icc C
  have he := eta_mem_Icc C
  have h := (eta_fibre_displayed (eta C) (blestNu C)).mp ⟨C, rfl, rfl⟩
  have hab := abs_le.mp h.2
  have hlo := lower_curve_mem _ he
  have hcurve := Lambda_curve _ he
  have hsum : blestNu C.transpose = 2 * eta C - blestNu C := nu_transpose C
  by_contra hne
  have hlt : eta C - etaGap (eta C) < blestNu C :=
    lt_of_le_of_ne (by linarith [hab.1]) (Ne.symm hne)
  have hmono := Lambda_strictMonoOn hlo hn hlt
  rw [hcurve, ← hC, hsum] at hmono
  linarith

theorem nu_transpose_min_upper (C : Copula 2)
    (hC : blestNu C.transpose = LambdaInv (blestNu C)) :
    blestNu C = eta C + etaGap (eta C) := by
  have hn := blest_mem_Icc C
  have hm := blest_mem_Icc C.transpose
  have he := eta_mem_Icc C
  have h := (eta_fibre_displayed (eta C) (blestNu C)).mp ⟨C, rfl, rfl⟩
  have hab := abs_le.mp h.2
  have hlo := lower_curve_mem _ he
  have hcurve := Lambda_curve _ he
  have hsum : blestNu C.transpose = 2 * eta C - blestNu C := nu_transpose C
  have hL : Lambda (blestNu C.transpose) = blestNu C := by
    rw [hC, Lambda_LambdaInv _ hn]
  by_contra hne
  have hlt : blestNu C < eta C + etaGap (eta C) :=
    lt_of_le_of_ne (by linarith [hab.2]) hne
  have hgt : eta C - etaGap (eta C) < blestNu C.transpose := by rw [hsum]; linarith
  have hmono := Lambda_strictMonoOn hlo hm hgt
  rw [hcurve, hL] at hmono
  linarith

/-- The image of the lower boundary curve under `L` is the graph of `Λ`. -/
theorem upper_boundary_curve :
    (fun e => (e - etaGap e, e + etaGap e)) '' Icc (-1 : ℝ) 1 =
      {p : ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2 = Lambda p.1} := by
  ext ⟨n, m⟩
  constructor
  · rintro ⟨e, he, hp⟩
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨lower_curve_mem e he, (Lambda_curve e he).symm⟩
  · rintro ⟨hn, hm⟩
    change n ∈ Icc (-1 : ℝ) 1 at hn
    change m = Lambda n at hm
    have hle : LambdaInv n ≤ Lambda n := le_trans (LambdaInv_le_self n hn) (Lambda_ge_self n hn)
    obtain ⟨C, hc, hct⟩ := (nu_transpose_fibre n (Lambda n)).mpr
      ⟨hn, Lambda_mapsTo hn, hle, le_rfl⟩
    have hlow := nu_transpose_max_lower C (by rw [hc, hct])
    refine ⟨eta C, eta_mem_Icc C, ?_⟩
    simp only [Prod.mk.injEq]
    constructor
    · rw [← hlow, hc]
    · rw [hm, ← hct, nu_transpose, hlow]; ring

/-- The image of the upper boundary curve under `L` is the graph of `Λ⁻¹`. -/
theorem lower_boundary_curve :
    (fun e => (e + etaGap e, e - etaGap e)) '' Icc (-1 : ℝ) 1 =
      {p : ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2 = LambdaInv p.1} := by
  ext ⟨n, m⟩
  constructor
  · rintro ⟨e, he, hp⟩
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    refine ⟨upper_curve_mem e he, ?_⟩
    change e - etaGap e = LambdaInv (e + etaGap e)
    rw [← Lambda_curve e he, LambdaInv_Lambda _ (lower_curve_mem e he)]
  · rintro ⟨hn, hm⟩
    change n ∈ Icc (-1 : ℝ) 1 at hn
    change m = LambdaInv n at hm
    obtain ⟨C, hc, hct⟩ := (nu_transpose_fibre n (LambdaInv n)).mpr
      ⟨hn, LambdaInv_mem n hn, le_rfl,
        le_trans (LambdaInv_le_self n hn) (Lambda_ge_self n hn)⟩
    have hup := nu_transpose_min_upper C (by rw [hc, hct])
    refine ⟨eta C, eta_mem_Icc C, ?_⟩
    simp only [Prod.mk.injEq]
    constructor
    · rw [← hup, hc]
    · rw [hm, ← hct, nu_transpose, hup]; ring

theorem lowerCurve_image :
    (fun e => e - etaGap e) '' Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) 1 := by
  ext n
  constructor
  · rintro ⟨e, he, rfl⟩
    exact lower_curve_mem e he
  · intro hn
    have hp : (n, Lambda n) ∈ (fun e => (e - etaGap e, e + etaGap e)) '' Icc (-1 : ℝ) 1 := by
      rw [upper_boundary_curve]
      exact ⟨hn, rfl⟩
    obtain ⟨e, he, hq⟩ := hp
    exact ⟨e, he, congrArg Prod.fst hq⟩

/-! ## Maximum and minimum of `ν(Cᵀ)` at fixed `ν(C)` -/

theorem nu_transpose_isGreatest (n : ℝ) (hn : n ∈ Icc (-1 : ℝ) 1) :
    IsGreatest {m | ∃ C : Copula 2, blestNu C = n ∧ blestNu C.transpose = m} (Lambda n) := by
  rw [nu_transpose_fibre_eq n hn]
  exact isGreatest_Icc (le_trans (LambdaInv_le_self n hn) (Lambda_ge_self n hn))

theorem nu_transpose_isLeast (n : ℝ) (hn : n ∈ Icc (-1 : ℝ) 1) :
    IsLeast {m | ∃ C : Copula 2, blestNu C = n ∧ blestNu C.transpose = m} (LambdaInv n) := by
  rw [nu_transpose_fibre_eq n hn]
  exact isLeast_Icc (le_trans (LambdaInv_le_self n hn) (Lambda_ge_self n hn))

theorem nu_transpose_max_exists_unique (n : ℝ) (hn : n ∈ Icc (-1 : ℝ) 1) :
    ∃! C : Copula 2, blestNu C = n ∧ blestNu C.transpose = Lambda n := by
  obtain ⟨C, hc, hm⟩ := (nu_transpose_isGreatest n hn).1
  refine ⟨C, ⟨hc, hm⟩, ?_⟩
  rintro D ⟨hd, hdm⟩
  have heq : eta D = eta C := by
    unfold eta
    rw [hd, hdm, hc, hm]
  apply eta_lower_unique D C heq
  · exact nu_transpose_max_lower D (by rw [hd]; exact hdm)
  · exact nu_transpose_max_lower C (by rw [hc]; exact hm)

theorem nu_transpose_min_exists_unique (n : ℝ) (hn : n ∈ Icc (-1 : ℝ) 1) :
    ∃! C : Copula 2, blestNu C = n ∧ blestNu C.transpose = LambdaInv n := by
  obtain ⟨C, hc, hm⟩ := (nu_transpose_isLeast n hn).1
  refine ⟨C, ⟨hc, hm⟩, ?_⟩
  rintro D ⟨hd, hdm⟩
  have heq : eta D = eta C := by
    unfold eta
    rw [hd, hdm, hc, hm]
  apply eta_upper_unique D C heq
  · exact nu_transpose_min_upper D (by rw [hd]; exact hdm)
  · exact nu_transpose_min_upper C (by rw [hc]; exact hm)

/-- Every upper extremizer of the `(η,ν)`-region is `A_w`, `B_a`, or `W`. -/
theorem upper_extremizer_cases (C : Copula 2)
    (hC : blestNu C = eta C + etaGap (eta C)) :
    (∃ w : I, (w : ℝ) ≤ 1 / 2 ∧ C = familyA w) ∨
      (∃ a : I, ∃ ha : (1 / 2 : ℝ) < a, (a : ℝ) < 1 ∧ C = familyB a ha.le) ∨
      C = Copula.countermonotonic := by
  by_cases hg : -3 / 4 ≤ eta C
  · obtain ⟨w, hw, _⟩ := graph_parameter_exists_unique (eta C) ⟨hg, (eta_mem_Icc C).2⟩
    have hn : blestNu C = blestNu (familyA w) := by
      rw [hC, ← hw.2, etaGap_graph w hw.1]; ring
    exact Or.inl ⟨w, hw.1, graph_upper_unique C w hw.1 hw.2.symm hn⟩
  · by_cases hb : eta C = -1
    · right; right
      have h1 : eta (familyA 1) = -1 := by rw [eta_familyA]; norm_num
      rw [eta_bottom_unique C (familyA 1) hb h1, familyA_one]
    · obtain ⟨a, ha, ha1, hav⟩ := randomized_parameter_exists_open (eta C)
        ⟨lt_of_le_of_ne (eta_mem_Icc C).1 (Ne.symm hb), by linarith⟩
      have hn : blestNu C = nuB a := by rw [hC, ← hav, etaGap_randomized a ha]; ring
      exact Or.inr (Or.inl ⟨a, ha, ha1, randomized_upper_unique C a ha ha1 hav.symm hn⟩)

/-- The maximizer is the transpose of an upper extremizer of the `(η,ν)`-region. -/
theorem nu_transpose_max_transpose_upper (C : Copula 2)
    (hC : blestNu C.transpose = Lambda (blestNu C)) :
    blestNu C.transpose = eta C.transpose + etaGap (eta C.transpose) := by
  rw [eta_transpose, nu_transpose, nu_transpose_max_lower C hC]
  ring

/-- For `n = -1`, the only copula in the fibre is `W`. -/
theorem nu_transpose_extremizer_neg_one (C : Copula 2) (hC : blestNu C = -1) :
    C = Copula.countermonotonic :=
  blest_min_unique C Copula.countermonotonic hC blest_countermonotonic

theorem nu_transpose_neg_one_values :
    Lambda (-1) = -1 ∧ LambdaInv (-1) = -1 ∧
      blestNu Copula.countermonotonic.transpose = -1 := by
  refine ⟨Lambda_neg_one, LambdaInv_neg_one, ?_⟩
  rw [← familyA_one, nu_transpose_familyA]
  norm_num

/-- For `n ∈ [-7/8,1]`, the maximizer is `A_wᵀ` with `w = 1 - ((1+n)/2)^(1/4)`. -/
theorem nu_transpose_max_familyA (n : ℝ) (hn : n ∈ Icc (-7 / 8 : ℝ) 1) :
    ∃ w : I, (w : ℝ) = 1 - ((1 + n) / 2) ^ (1 / 4 : ℝ) ∧ (w : ℝ) ≤ 1 / 2 ∧
      blestNu (familyA w).transpose = n ∧ blestNu (familyA w) = Lambda n ∧
      ∀ C : Copula 2, blestNu C = n → blestNu C.transpose = Lambda n →
        C = (familyA w).transpose := by
  obtain ⟨hl, hu⟩ := root_bounds n hn
  obtain ⟨hs0, hs⟩ := closed_root n (by linarith [hn.1])
  set s := ((1 + n) / 2) ^ (1 / 4 : ℝ) with hsdef
  let w : I := ⟨1 - s, by constructor <;> linarith⟩
  have hw : (w : ℝ) = 1 - s := rfl
  have h1w : 1 - (w : ℝ) = s := by rw [hw]; ring
  have hT : blestNu (familyA w).transpose = n := by
    rw [nu_transpose_familyA, h1w, hs]
  have hN : blestNu (familyA w) = Lambda n := by
    rw [nu_familyA, Lambda_closed_branch _ hn.1, lambdaClosed_root n (by linarith [hn.1]),
      ← hsdef, hw]
    ring
  refine ⟨w, hw, by rw [hw]; linarith, hT, hN, ?_⟩
  intro C hc hct
  have hnI : n ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hn.1], hn.2⟩
  obtain ⟨D, _, hD⟩ := nu_transpose_max_exists_unique n hnI
  have hA : blestNu ((familyA w).transpose).transpose = Lambda n := by
    rw [Copula.transpose_transpose, hN]
  exact (hD C ⟨hc, hct⟩).trans (hD _ ⟨hT, hA⟩).symm

/-- For `n ∈ (-1,-7/8)`, the maximizer is `B_aᵀ` with `n_a = n`. -/
theorem nu_transpose_max_familyB (n : ℝ) (hn : n ∈ Ioo (-1 : ℝ) (-7 / 8)) :
    ∃ a : I, ∃ ha : (1 / 2 : ℝ) < a, (a : ℝ) < 1 ∧ transposeParam a = n ∧
      blestNu (familyB a ha.le).transpose = n ∧ blestNu (familyB a ha.le) = Lambda n ∧
      ∀ C : Copula 2, blestNu C = n → blestNu C.transpose = Lambda n →
        C = (familyB a ha.le).transpose := by
  obtain ⟨ha, ha1⟩ := lambdaParameter_open n hn
  have hv := (lambdaParameter_spec n ⟨hn.1.le, hn.2.le⟩).2
  have hT : blestNu (familyB (lambdaParameter n) ha.le).transpose = n := by
    rw [nu_transpose_familyB_param _ ha.le, hv]
  have hN : blestNu (familyB (lambdaParameter n) ha.le) = Lambda n := by
    rw [nu_familyB, Lambda_param_branch n hn]
  refine ⟨lambdaParameter n, ha, ha1, hv, hT, hN, ?_⟩
  intro C hc hct
  have hnI : n ∈ Icc (-1 : ℝ) 1 := ⟨hn.1.le, by linarith [hn.2]⟩
  obtain ⟨D, _, hD⟩ := nu_transpose_max_exists_unique n hnI
  have hB : blestNu ((familyB (lambdaParameter n) ha.le).transpose).transpose = Lambda n := by
    rw [Copula.transpose_transpose, hN]
  exact (hD C ⟨hc, hct⟩).trans (hD _ ⟨hT, hB⟩).symm

/-- For `n ∈ (-1,1]`, the minimizer is an upper extremizer `A_w` or `B_a` itself. -/
theorem nu_transpose_min_cases (C : Copula 2) (hn : -1 < blestNu C)
    (hC : blestNu C.transpose = LambdaInv (blestNu C)) :
    (∃ w : I, (w : ℝ) ≤ 1 / 2 ∧ C = familyA w) ∨
      (∃ a : I, ∃ ha : (1 / 2 : ℝ) < a, (a : ℝ) < 1 ∧ C = familyB a ha.le) := by
  rcases upper_extremizer_cases C (nu_transpose_min_upper C hC) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rw [h, blest_countermonotonic] at hn
    norm_num at hn

/-- For `n ∈ (-1,1]`, the maximizer is the transpose of `A_w` or `B_a`. -/
theorem nu_transpose_max_cases (C : Copula 2) (hn : -1 < blestNu C)
    (hC : blestNu C.transpose = Lambda (blestNu C)) :
    (∃ w : I, (w : ℝ) ≤ 1 / 2 ∧ C = (familyA w).transpose) ∨
      (∃ a : I, ∃ ha : (1 / 2 : ℝ) < a, (a : ℝ) < 1 ∧ C = (familyB a ha.le).transpose) := by
  rcases upper_extremizer_cases C.transpose (nu_transpose_max_transpose_upper C hC)
    with ⟨w, hw, h⟩ | ⟨a, ha, ha1, h⟩ | h
  · left
    refine ⟨w, hw, ?_⟩
    rw [← h, Copula.transpose_transpose]
  · right
    refine ⟨a, ha, ha1, ?_⟩
    rw [← h, Copula.transpose_transpose]
  · exfalso
    have hW : blestNu C.transpose = -1 := by rw [h, blest_countermonotonic]
    have hge := Lambda_ge_self _ (blest_mem_Icc C)
    rw [hC] at hW
    linarith

/-! ## The closed-form bound stated in the introduction -/

theorem nu_transpose_closed_bound (C : Copula 2) (hn : -7 / 8 ≤ blestNu C) :
    blestNu C.transpose ≤ 4 * ((1 + blestNu C) / 2) ^ (3 / 4 : ℝ) - blestNu C - 2 := by
  have h := (nu_transpose_fibre _ _).mp ⟨C, rfl, rfl⟩
  have hL := h.2.2.2
  rw [Lambda_closed_branch _ hn] at hL
  exact hL

theorem nu_transpose_closed_bound_unique (n : ℝ) (hn : n ∈ Icc (-7 / 8 : ℝ) 1) :
    ∃! C : Copula 2, blestNu C = n ∧
      blestNu C.transpose = 4 * ((1 + n) / 2) ^ (3 / 4 : ℝ) - n - 2 := by
  have h := nu_transpose_max_exists_unique n ⟨by linarith [hn.1], hn.2⟩
  rw [Lambda_closed_branch _ hn.1] at h
  exact h

/-! ## Continuity of `Υ` -/

theorem etaGap_le_one_add (e : ℝ) (he : e ∈ Icc (-1 : ℝ) 1) : etaGap e ≤ 1 + e := by
  linarith [(lower_curve_mem e he).1]

theorem etaGap_le_one_sub (e : ℝ) (he : e ∈ Icc (-1 : ℝ) 1) : etaGap e ≤ 1 - e := by
  linarith [(upper_curve_mem e he).2]

theorem lowerCurve_continuousAt (e : ℝ) (he : e ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt (fun e => e - etaGap e) e := by
  apply continuousAt_of_monotoneOn_of_image_mem_nhds lowerCurve_strictMonoOn.monotoneOn
    (Icc_mem_nhds he.1 he.2)
  rw [lowerCurve_image]
  have hl := lowerCurve_strictMonoOn (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
    ⟨he.1.le, he.2.le⟩ he.1
  have hu := lowerCurve_strictMonoOn ⟨he.1.le, he.2.le⟩
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) he.2
  dsimp only at hl hu
  rw [etaGap_bottom] at hl
  rw [etaGap_top] at hu
  exact Icc_mem_nhds (by linarith) (by linarith)

theorem etaGap_continuousAt (e : ℝ) (he : e ∈ Ioo (-1 : ℝ) 1) : ContinuousAt etaGap e := by
  have h : etaGap = fun x => x - (x - etaGap x) := by
    funext x
    ring
  rw [h]
  exact continuousAt_id.sub (lowerCurve_continuousAt e he)

/-- `Υ` is continuous on `[-1,1]`, in particular at the regime change `-3/4`. -/
theorem etaGap_continuousOn : ContinuousOn etaGap (Icc (-1 : ℝ) 1) := by
  intro e he
  by_cases hb : e = -1
  · subst e
    unfold ContinuousWithinAt
    rw [etaGap_bottom]
    have h0 : Tendsto (fun x : ℝ => 1 + x) (𝓝[Icc (-1 : ℝ) 1] (-1)) (𝓝 0) := by
      have h := ((continuous_const.add continuous_id).tendsto (-1 : ℝ) :
        Tendsto (fun x : ℝ => 1 + id x) (𝓝 (-1)) (𝓝 (1 + id (-1))))
      norm_num at h
      exact h.mono_left nhdsWithin_le_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact etaGap_nonneg x hx
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact etaGap_le_one_add x hx
  · by_cases ht : e = 1
    · subst e
      unfold ContinuousWithinAt
      rw [etaGap_top]
      have h0 : Tendsto (fun x : ℝ => 1 - x) (𝓝[Icc (-1 : ℝ) 1] 1) (𝓝 0) := by
        have h := ((continuous_const.sub continuous_id).tendsto (1 : ℝ) :
          Tendsto (fun x : ℝ => 1 - id x) (𝓝 1) (𝓝 (1 - id 1)))
        norm_num at h
        exact h.mono_left nhdsWithin_le_nhds
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact etaGap_nonneg x hx
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact etaGap_le_one_sub x hx
    · exact (etaGap_continuousAt e ⟨lt_of_le_of_ne he.1 (Ne.symm hb),
        lt_of_le_of_ne he.2 ht⟩).continuousWithinAt

theorem etaGap_continuousAt_join : ContinuousAt etaGap (-3 / 4) :=
  etaGap_continuousAt _ (by norm_num)

#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_nonneg
#assert_standard_axioms Papers.Rockel2026ExactBlest.upper_curve_mem
#assert_standard_axioms Papers.Rockel2026ExactBlest.lower_curve_mem
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_top
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_mem
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_transposeParam
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_familyA
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_curve
#assert_standard_axioms Papers.Rockel2026ExactBlest.lowerCurve_strictMonoOn
#assert_standard_axioms Papers.Rockel2026ExactBlest.upperCurve_strictMonoOn
#assert_standard_axioms Papers.Rockel2026ExactBlest.LambdaInv_mem
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_LambdaInv
#assert_standard_axioms Papers.Rockel2026ExactBlest.LambdaInv_Lambda
#assert_standard_axioms Papers.Rockel2026ExactBlest.LambdaInv_le_iff
#assert_standard_axioms Papers.Rockel2026ExactBlest.LambdaInv_bijOn
#assert_standard_axioms Papers.Rockel2026ExactBlest.LambdaInv_strictMonoOn
#assert_standard_axioms Papers.Rockel2026ExactBlest.LambdaInv_le_self
#assert_standard_axioms Papers.Rockel2026ExactBlest.LambdaInv_neg_one
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_fibre_gap
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_region_gap
#assert_standard_axioms Papers.Rockel2026ExactBlest.gap_band_iff
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_fibre
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_region
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_fibre_eq
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_nu_region_linear_image
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_max_lower
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_min_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.upper_boundary_curve
#assert_standard_axioms Papers.Rockel2026ExactBlest.lower_boundary_curve
#assert_standard_axioms Papers.Rockel2026ExactBlest.lowerCurve_image
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_isGreatest
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_isLeast
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_max_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_min_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.upper_extremizer_cases
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_max_transpose_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_extremizer_neg_one
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_neg_one_values
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_max_familyA
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_max_familyB
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_min_cases
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_max_cases
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_closed_bound
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_closed_bound_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_le_one_add
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_le_one_sub
#assert_standard_axioms Papers.Rockel2026ExactBlest.lowerCurve_continuousAt
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_continuousAt
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_continuousOn
#assert_standard_axioms Papers.Rockel2026ExactBlest.etaGap_continuousAt_join

end
end Papers.Rockel2026ExactBlest
