import Papers.OrendayLaresRockel2026XiBeta.Subclasses
import Copula.Rank.Chatterjee
import Copula.Dependence.Conditional
import Verification.StochasticBounds

/-! # Section 2 of the article (version 2): classes, reflection and interpolation

* (2.2): `1 - ξ(C) = 6 ∫∫ h (1 - h)` with `h = ∂₁C`.
* (2.3): `ξ(Č) = ξ(C)`, `β(Č) = -β(C)` for `Č(u,v) = u - C(u, 1-v)` (the library's
  `C.reflect {1}`).
* the five classes `PQD, NQD, SI, SD, RS`, their convexity, the involution `C ↦ Č`
  and the reflection (2.4) of the `(ξ, β)`-regions of the classes and their intersections.
* Lemma 2.1 (interpolation in a convex subclass).
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-! ### Equation (2.2) -/

/-- Equation (2.2), with the Markov kernel `h(u,v) = ∂₁C(u,v) = K_C(u,[0,v])`. -/
theorem one_sub_xi_eq (C : Copula 2) :
    1 - C.chatterjeeXi =
      6 * ∫ v : I, ∫ u : I, C.conditionalCDF u v * (1 - C.conditionalCDF u v) := by
  have hi (t : I) : (∫ u : I, C.conditionalCDF u t * (1 - C.conditionalCDF u t)) =
      (t : ℝ) - ∫ u : I, C.conditionalCDF u t ^ 2 := by
    have he : (fun u : I => C.conditionalCDF u t * (1 - C.conditionalCDF u t)) =
        fun u : I => C.conditionalCDF u t - C.conditionalCDF u t ^ 2 := by
      funext u; ring
    rw [he, integral_sub (C.integrable_conditionalCDF t) (C.integrable_conditionalCDF_sq t),
      C.integral_conditionalCDF]
  simp_rw [hi]
  rw [integral_sub (Copula.integrable_continuous_unit volume (by fun_prop))
    C.integrable_integral_conditionalCDF_sq, Copula.integral_unit_id]
  unfold Copula.chatterjeeXi
  ring

/-- Equation (2.2) with the classical partial derivative `∂₁C(u,v)`
(equal to the kernel for Lebesgue-a.e. `u`). -/
theorem one_sub_xi_eq_deriv (C : Copula 2) :
    1 - C.chatterjeeXi = 6 * ∫ v : I, ∫ u : I,
      deriv (C.cdfSection v) (u : ℝ) * (1 - deriv (C.cdfSection v) (u : ℝ)) := by
  rw [one_sub_xi_eq]
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun v => ?_)
  apply integral_congr_ae
  filter_upwards [C.conditionalCDF_eq_deriv v] with u hu
  simp only [hu]

/-! ### Equation (2.3): the involution `C ↦ Č` -/

/-- `Č(u,v) = u - C(u, 1 - v)`. -/
theorem check_cdf (C : Copula 2) (u v : I) :
    (C.reflect {1}).cdf ![u, v] = (u : ℝ) - C.cdf ![u, unitInterval.symm v] :=
  Copula.cdf_reflect_second C u v

/-- Equation (2.3), first part. -/
theorem xi_check (C : Copula 2) : (C.reflect {1}).chatterjeeXi = C.chatterjeeXi :=
  Verification.xi_reflect_second C

/-- Equation (2.3), second part. -/
theorem beta_check (C : Copula 2) : (C.reflect {1}).blomqvistBeta = -C.blomqvistBeta :=
  Copula.blomqvistBeta_reflect_second C

/-- The kernel of `Č`: `∂₁Č(u,v) = 1 - ∂₁C(u, 1 - v)` for a.e. `u`. -/
theorem check_kernel (C : Copula 2) (v : I) :
    (fun u => (C.reflect {1}).conditionalCDF u v) =ᵐ[volume]
      fun u => 1 - C.conditionalCDF u (unitInterval.symm v) :=
  Verification.conditionalCDF_reflect_second C v

/-! ### The five classes, convexity and the involution -/

/-- Positive quadrant dependent copulas. -/
def classPQD : Set (Copula 2) := {C | C.IsPQD}
/-- Negative quadrant dependent copulas. -/
def classNQD : Set (Copula 2) := {C | C.IsNQD}
/-- Stochastically increasing copulas. -/
def classSI : Set (Copula 2) := {C | C.IsSI}
/-- Stochastically decreasing copulas. -/
def classSD : Set (Copula 2) := {C | C.IsSD}
/-- Radially symmetric copulas. -/
def classRS : Set (Copula 2) := {C | C.IsRadiallySymmetric}

/-- A class of copulas is convex if it is closed under mixtures. -/
def IsConvexClass (A : Set (Copula 2)) : Prop :=
  ∀ C ∈ A, ∀ D ∈ A, ∀ a : I, C.mix D a ∈ A

theorem isNQD_mix {C D : Copula 2} (hC : C.IsNQD) (hD : D.IsNQD) (w : I) :
    (C.mix D w).IsNQD := by
  intro u v
  rw [Copula.cdf_mix]
  nlinarith [mul_nonneg w.property.1 (sub_nonneg.mpr (hC u v)),
    mul_nonneg (sub_nonneg.mpr w.property.2) (sub_nonneg.mpr (hD u v))]

theorem isSD_mix {C D : Copula 2} (hC : C.IsSD) (hD : D.IsSD) (w : I) :
    (C.mix D w).IsSD := by
  intro a b c v hab hbc
  simp only [Copula.cdf_mix]
  nlinarith [mul_nonneg w.property.1 (sub_nonneg.mpr (hC a b c v hab hbc)),
    mul_nonneg (sub_nonneg.mpr w.property.2) (sub_nonneg.mpr (hD a b c v hab hbc))]

theorem convex_univ : IsConvexClass (Set.univ : Set (Copula 2)) := fun _ _ _ _ _ => trivial

theorem convex_pqd : IsConvexClass classPQD := fun _ hC _ hD a => Copula.IsPQD.mix hC hD a
theorem convex_nqd : IsConvexClass classNQD := fun _ hC _ hD a => isNQD_mix hC hD a
theorem convex_si : IsConvexClass classSI := fun _ hC _ hD a => Copula.IsSI.mix hC hD a
theorem convex_sd : IsConvexClass classSD := fun _ hC _ hD a => isSD_mix hC hD a
theorem convex_rs : IsConvexClass classRS := fun _ hC _ hD a => Copula.IsRadiallySymmetric.mix hC hD a

/-- Intersections of convex classes are convex (so all intersections of the five classes are). -/
theorem IsConvexClass.inter {A B : Set (Copula 2)} (hA : IsConvexClass A) (hB : IsConvexClass B) :
    IsConvexClass (A ∩ B) :=
  fun _ hC _ hD a => ⟨hA _ hC.1 _ hD.1 a, hB _ hC.2 _ hD.2 a⟩

/-- Every SI copula is PQD. -/
theorem classSI_subset_classPQD : classSI ⊆ classPQD := fun _ h => Copula.IsSI.isPQD h

/-- Every SD copula is NQD. -/
theorem classSD_subset_classNQD : classSD ⊆ classNQD := fun _ h => Copula.IsSD.isNQD h

theorem isPQD_reflect_second_iff (C : Copula 2) : (C.reflect {1}).IsPQD ↔ C.IsNQD := by
  constructor
  · intro h u v
    have := h u (unitInterval.symm v)
    rw [Copula.cdf_reflect_second] at this
    simp only [unitInterval.coe_symm_eq, unitInterval.symm_symm] at this
    nlinarith
  · intro h u v
    have := h u (unitInterval.symm v)
    rw [Copula.cdf_reflect_second]
    simp only [unitInterval.coe_symm_eq] at this ⊢
    nlinarith

theorem isNQD_reflect_second_iff (C : Copula 2) : (C.reflect {1}).IsNQD ↔ C.IsPQD := by
  rw [← isPQD_reflect_second_iff, Copula.reflect_reflect]

theorem isRadiallySymmetric_reflect_second_iff (C : Copula 2) :
    (C.reflect {1}).IsRadiallySymmetric ↔ C.IsRadiallySymmetric := by
  rw [Copula.isRadiallySymmetric_iff, Copula.isRadiallySymmetric_iff]
  constructor
  · intro h u v
    have := h u (unitInterval.symm v)
    simp only [Copula.cdf_reflect_second, unitInterval.coe_symm_eq, unitInterval.symm_symm] at this
    nlinarith
  · intro h u v
    have := h u (unitInterval.symm v)
    simp only [Copula.cdf_reflect_second, unitInterval.coe_symm_eq, unitInterval.symm_symm]
    simp only [unitInterval.coe_symm_eq, unitInterval.symm_symm] at this
    nlinarith

/-- `Ǎ = {Č : C ∈ A}`. -/
def checkClass (A : Set (Copula 2)) : Set (Copula 2) := (fun C => C.reflect {1}) '' A

theorem mem_checkClass_iff (A : Set (Copula 2)) (D : Copula 2) :
    D ∈ checkClass A ↔ D.reflect {1} ∈ A := by
  constructor
  · rintro ⟨C, hC, rfl⟩
    simpa using hC
  · intro h
    exact ⟨D.reflect {1}, h, Copula.reflect_reflect _ _⟩

theorem checkClass_pqd : checkClass classPQD = classNQD := by
  ext D; rw [mem_checkClass_iff]; exact isPQD_reflect_second_iff D
theorem checkClass_nqd : checkClass classNQD = classPQD := by
  ext D; rw [mem_checkClass_iff]; exact isNQD_reflect_second_iff D
theorem checkClass_si : checkClass classSI = classSD := by
  ext D; rw [mem_checkClass_iff]; exact Copula.isSI_reflect_second_iff D
theorem checkClass_sd : checkClass classSD = classSI := by
  ext D; rw [mem_checkClass_iff]; exact Copula.isSD_reflect_second_iff D
theorem checkClass_rs : checkClass classRS = classRS := by
  ext D; rw [mem_checkClass_iff]; exact isRadiallySymmetric_reflect_second_iff D
theorem checkClass_univ : checkClass (Set.univ : Set (Copula 2)) = Set.univ := by
  ext D; rw [mem_checkClass_iff]; simp

theorem checkClass_inter (A B : Set (Copula 2)) :
    checkClass (A ∩ B) = checkClass A ∩ checkClass B :=
  Set.image_inter (Copula.reflect_injective {1})

/-! ### Equation (2.4) -/

/-- `R^A_{ξ,β} = {(ξ(C), β(C)) : C ∈ A}`. -/
def xiBetaRegion (A : Set (Copula 2)) : Set (ℝ × ℝ) :=
  {p | ∃ C ∈ A, C.chatterjeeXi = p.1 ∧ C.blomqvistBeta = p.2}

/-- Equation (2.4): `R^{Ǎ} = {(x, -y) : (x, y) ∈ R^A}` for every class `A`. -/
theorem xiBetaRegion_checkClass (A : Set (Copula 2)) :
    xiBetaRegion (checkClass A) = (fun p : ℝ × ℝ => (p.1, -p.2)) '' xiBetaRegion A := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨D, ⟨C, hC, rfl⟩, hx, hy⟩
    refine ⟨(C.chatterjeeXi, C.blomqvistBeta), ⟨C, hC, rfl, rfl⟩, ?_⟩
    simp only at hx hy ⊢
    rw [xi_check] at hx
    rw [beta_check] at hy
    rw [hx, hy]
  · rintro ⟨⟨x', y'⟩, ⟨C, hC, hx, hy⟩, he⟩
    simp only [Prod.mk.injEq] at he hx hy
    refine ⟨C.reflect {1}, ⟨C, hC, rfl⟩, ?_, ?_⟩
    · simp only
      rw [xi_check, hx, he.1]
    · simp only
      rw [beta_check, hy, he.2]

/-- Equation (2.4) for the five classes: the mirror image of PQD is NQD, etc. -/
theorem xiBetaRegion_nqd_eq :
    xiBetaRegion classNQD = (fun p : ℝ × ℝ => (p.1, -p.2)) '' xiBetaRegion classPQD := by
  rw [← checkClass_pqd, xiBetaRegion_checkClass]
theorem xiBetaRegion_sd_eq :
    xiBetaRegion classSD = (fun p : ℝ × ℝ => (p.1, -p.2)) '' xiBetaRegion classSI := by
  rw [← checkClass_si, xiBetaRegion_checkClass]
theorem xiBetaRegion_rs_eq :
    xiBetaRegion classRS = (fun p : ℝ × ℝ => (p.1, -p.2)) '' xiBetaRegion classRS := by
  conv_lhs => rw [← checkClass_rs]
  rw [xiBetaRegion_checkClass]

theorem xiBetaRegion_mono {A B : Set (Copula 2)} (h : A ⊆ B) : xiBetaRegion A ⊆ xiBetaRegion B :=
  fun _ ⟨C, hC, hx, hy⟩ => ⟨C, h hC, hx, hy⟩

/-! ### Lemma 2.1 (interpolation) -/

/-- Lemma 2.1. Let `A` be convex and `C₀, C₁ ∈ A` with `β(C₀) = β(C₁) = b`. For every `x`
between `ξ(C₀)` and `ξ(C₁)` there is `C ∈ A` with `ξ(C) = x` and `β(C) = b`. -/
theorem interpolation_lemma {A : Set (Copula 2)} (hA : IsConvexClass A) {C₀ C₁ : Copula 2}
    (h₀ : C₀ ∈ A) (h₁ : C₁ ∈ A) {b : ℝ} (hb₀ : C₀.blomqvistBeta = b) (hb₁ : C₁.blomqvistBeta = b)
    {x : ℝ} (hx : x ∈ Set.uIcc C₀.chatterjeeXi C₁.chatterjeeXi) :
    ∃ C ∈ A, C.chatterjeeXi = x ∧ C.blomqvistBeta = b := by
  rcases Set.mem_uIcc.mp hx with h | h
  · obtain ⟨E, hE, hxi, hbeta⟩ := fixed_beta_intermediate_in_class (· ∈ A) (fun C D hC hD a => hA C hC D hD a) C₀ C₁ h₀ h₁ hb₀ hb₁ h.1 h.2
    exact ⟨E, hE, hxi, hbeta⟩
  · obtain ⟨E, hE, hxi, hbeta⟩ := fixed_beta_intermediate_in_class (· ∈ A) (fun C D hC hD a => hA C hC D hD a) C₁ C₀ h₁ h₀ hb₁ hb₀ h.1 h.2
    exact ⟨E, hE, hxi, hbeta⟩

/-! ### Stochastic monotonicity via kernel versions -/

/-- SI means that for every `v` the kernel `u ↦ ∂₁C(u,v)` has a nonincreasing version
(equivalently, `C(·, v)` is concave). -/
theorem isSI_iff_antitone_version (C : Copula 2) :
    C.IsSI ↔ ∀ v : I, ∃ g : I → ℝ, Antitone g ∧
      (fun u => C.conditionalCDF u v) =ᵐ[volume] g := by
  constructor
  · intro h v
    obtain ⟨g, hg, -, hae⟩ := Verification.conditionalCDF_antitone_version C h v
    exact ⟨g, hg, hae⟩
  · intro h a b c v hab hbc
    obtain ⟨g, hg, hae⟩ := h v
    have hint : Integrable g := (C.integrable_conditionalCDF v).congr hae
    have hc (w : I) : C.cdf ![w, v] = ∫ t in Iic w, g t := by
      rw [Copula.cdf_eq_integral_conditionalCDF]
      exact setIntegral_congr_ae measurableSet_Iic (by
        filter_upwards [hae] with t ht _
        exact ht)
    rw [hc, hc, hc]
    exact Copula.integral_Iic_concave_of_antitone hint hg a b c hab hbc

/-- SD means that for every `v` the kernel has a nondecreasing version. -/
theorem isSD_iff_monotone_version (C : Copula 2) :
    C.IsSD ↔ ∀ v : I, ∃ g : I → ℝ, Monotone g ∧
      (fun u => C.conditionalCDF u v) =ᵐ[volume] g := by
  rw [← Copula.isSI_reflect_second_iff, isSI_iff_antitone_version]
  constructor
  · intro h v
    obtain ⟨g, hg, hae⟩ := h (unitInterval.symm v)
    refine ⟨fun u => 1 - g u, fun a b hab => by linarith [hg hab], ?_⟩
    filter_upwards [Verification.conditionalCDF_reflect_second C (unitInterval.symm v), hae]
      with u h1 h2
    simp only [unitInterval.symm_symm] at h1
    linarith
  · intro h v
    obtain ⟨g, hg, hae⟩ := h (unitInterval.symm v)
    refine ⟨fun u => 1 - g u, fun a b hab => by linarith [hg hab], ?_⟩
    filter_upwards [Verification.conditionalCDF_reflect_second C v, hae] with u h1 h2
    linarith

/-- `C^⊤` is SI iff `v ↦ C(u,v)` is concave for every `u`. -/
theorem transpose_isSI_iff_concave (C : Copula 2) :
    C.transpose.IsSI ↔ ∀ a b c u : I, a ≤ b → b ≤ c →
      ((b : ℝ) - (a : ℝ)) * C.cdf ![u, c] + ((c : ℝ) - (b : ℝ)) * C.cdf ![u, a] ≤
        ((c : ℝ) - (a : ℝ)) * C.cdf ![u, b] := by
  simp only [Copula.IsSI, Copula.cdf_transpose]

/-! ### All intersections of the five classes -/

/-- The five classes of the article. -/
inductive Cls
  | pqd | nqd | si | sd | rs
  deriving DecidableEq

/-- The class of copulas denoted by a symbol. -/
def Cls.set : Cls → Set (Copula 2)
  | .pqd => classPQD
  | .nqd => classNQD
  | .si => classSI
  | .sd => classSD
  | .rs => classRS

/-- The image of a class under `C ↦ Č`. -/
def Cls.check : Cls → Cls
  | .pqd => .nqd
  | .nqd => .pqd
  | .si => .sd
  | .sd => .si
  | .rs => .rs

/-- The intersection of the classes in `S` (the whole class of copulas for `S = ∅`). -/
def interSet (S : Finset Cls) : Set (Copula 2) := {C | ∀ c ∈ S, C ∈ c.set}

theorem checkClass_cls (c : Cls) : checkClass c.set = c.check.set := by
  cases c
  · exact checkClass_pqd
  · exact checkClass_nqd
  · exact checkClass_si
  · exact checkClass_sd
  · exact checkClass_rs

theorem convex_cls (c : Cls) : IsConvexClass c.set := by
  cases c
  · exact convex_pqd
  · exact convex_nqd
  · exact convex_si
  · exact convex_sd
  · exact convex_rs

/-- Every intersection of the five classes is convex. -/
theorem convex_interSet (S : Finset Cls) : IsConvexClass (interSet S) :=
  fun _ hC _ hD a c hc => convex_cls c _ (hC c hc) _ (hD c hc) a

/-- `Ǎ` for an intersection `A` of the five classes is the intersection of the mirrored classes. -/
theorem checkClass_interSet (S : Finset Cls) :
    checkClass (interSet S) = interSet (S.image Cls.check) := by
  ext D
  rw [mem_checkClass_iff]
  constructor
  · intro h c hc
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    have := h c' hc'
    rw [← mem_checkClass_iff, checkClass_cls] at this
    exact this
  · intro h c hc
    have := h c.check (Finset.mem_image_of_mem _ hc)
    rw [← checkClass_cls, mem_checkClass_iff] at this
    exact this

/-- Equation (2.4) for each of the five classes and each intersection of them:
`R^{Ǎ} = {(x, -y) : (x, y) ∈ R^A}`. -/
theorem xiBetaRegion_interSet_check (S : Finset Cls) :
    xiBetaRegion (interSet (S.image Cls.check)) =
      (fun p : ℝ × ℝ => (p.1, -p.2)) '' xiBetaRegion (interSet S) := by
  rw [← checkClass_interSet, xiBetaRegion_checkClass]

end Papers.OrendayLaresRockel2026XiBeta
