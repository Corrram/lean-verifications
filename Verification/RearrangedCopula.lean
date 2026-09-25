import Verification.SchurRearrangement
import Verification.XiPredictorReflection
import Copula.Rank.ConditionalCDF
import Copula.Classical.Bivariate
import Copula.Classical.Characterization
import Copula.Order.Schur
import Copula.Order.Orthant
import Copula.Dependence.Basic
import Copula.Reflection.Bivariate

/-! # Rearranged copulas and the Schur order

For a copula `E`, `E↑(u,v)=∫_0^u (∂₁E(·,v))*` is the increasing (SI) rearrangement and
`E↓(u,v)=v-E↑(1-u,v)` the decreasing one. We prove that `E↑` is a copula, CIS, Schur
equivalent to `E`, and the lower-orthant maximum of `{D : D ≤_{∂₁S} E}`; `E↓` is the
minimum. This gives Lemma 2.7 and Proposition 3.1 of Ansari–Rockel.
-/

open MeasureTheory ProbabilityTheory Set Filter Copula
open scoped unitInterval

namespace Verification

/-- The conditional section `u ↦ P(V ≤ v | U=u)`. -/
noncomputable def condSection (C : Copula 2) (v : I) : I → ℝ := fun u => C.conditionalCDF u v

theorem condSection_nonneg (C : Copula 2) (v : I) (u : I) : 0≤condSection C v u :=
  C.conditionalCDF_nonneg u v

theorem condSection_le_one (C : Copula 2) (v : I) (u : I) : condSection C v u≤1 :=
  C.conditionalCDF_le_one u v

theorem condSection_measurable (C : Copula 2) (v : I) : Measurable (condSection C v) :=
  C.measurable_conditionalCDF_left v

theorem condSection_mono (C : Copula 2) {v w : I} (h : v≤w) (u : I) :
    condSection C v u≤condSection C w u :=
  measureReal_mono (Iic_subset_Iic.mpr h)

theorem condSection_one (C : Copula 2) (u : I) : condSection C 1 u=1 := by
  unfold condSection Copula.conditionalCDF
  rw [show Iic (1:I)=univ from Iic_top]
  simp

theorem condSection_zero_ae (C : Copula 2) : condSection C 0=ᵐ[volume] fun _ => (0:ℝ) := by
  apply C.conditionalCDF_ae_eq_of_integral 0 (integrable_const 0) (fun _ => le_rfl)
  intro u
  simp only [integral_zero]
  exact (C.cdf_eq_zero_of_coord_eq_zero _ 1 rfl).symm

theorem decRearr_const_zero {s : ℝ} (hs : 0≤s) : decRearr (fun _ : I => (0:ℝ)) s=0 := by
  apply le_antisymm _ (decRearr_nonneg (fun _ => zero_le_one) hs)
  apply csInf_le (decRearr_set_bdd _ s)
  refine ⟨le_rfl,?_⟩
  unfold distFun
  simp [hs]

theorem decRearr_const_one {s : ℝ} (hs : 0≤s) (hs1 : s<1) : decRearr (fun _ : I => (1:ℝ)) s=1 := by
  apply le_antisymm (decRearr_le_one (fun _ => le_rfl) hs)
  apply le_csInf (decRearr_set_nonempty (fun _ => le_rfl) hs)
  intro c hc
  by_contra hlt
  push Not at hlt
  have : distFun (fun _ : I => (1:ℝ)) c=1 := by
    unfold distFun
    have : {u : I | c<(fun _ : I => (1:ℝ)) u}=univ := by ext u; simp [hlt]
    simp [this]
  linarith [hc.2]

/-- The increasing rearranged copula, as a CDF. -/
noncomputable def upRearrCDF (C : Copula 2) (u v : I) : ℝ :=
  ∫ s in Iic u, decRearr (condSection C v) s

theorem decRearr_condSection_nonneg (C : Copula 2) (v s : I) : 0≤decRearr (condSection C v) s :=
  decRearr_nonneg (condSection_le_one C v) s.property.1

theorem decRearr_condSection_le_one (C : Copula 2) (v s : I) : decRearr (condSection C v) s≤1 :=
  decRearr_le_one (condSection_le_one C v) s.property.1

theorem integrable_decRearr_condSection (C : Copula 2) (v : I) :
    Integrable (fun s : I => decRearr (condSection C v) s) :=
  integrable_of_unit (decRearr_condSection_nonneg C v) (decRearr_condSection_le_one C v)
    (decRearr_measurable (condSection_le_one C v)) continuous_id

theorem upRearrCDF_zero_left (C : Copula 2) (v : I) : upRearrCDF C 0 v=0 := by
  unfold upRearrCDF
  apply setIntegral_measure_zero
  rw [unitInterval.volume_Iic]
  simp

theorem upRearrCDF_zero_right (C : Copula 2) (u : I) : upRearrCDF C u 0=0 := by
  unfold upRearrCDF
  rw [decRearr_congr (condSection_zero_ae C)]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro s _
  exact decRearr_const_zero s.property.1

theorem upRearrCDF_one_left (C : Copula 2) (v : I) : upRearrCDF C 1 v=(v:ℝ) := by
  unfold upRearrCDF
  rw [show Iic (1:I)=univ from Iic_top,Measure.restrict_univ]
  have h := integral_comp_decRearr (condSection_nonneg C v) (condSection_le_one C v)
    (condSection_measurable C v) (φ := id) measurable_id
  simp only [id] at h
  rw [h]
  exact C.integral_conditionalCDF v

theorem upRearrCDF_one_right (C : Copula 2) (u : I) : upRearrCDF C u 1=(u:ℝ) := by
  unfold upRearrCDF
  have he : condSection C 1=fun _ => (1:ℝ) := funext (condSection_one C)
  rw [he]
  have hae : ∀ᵐ s : I, s≠1 := by simp [ae_iff]
  rw [setIntegral_congr_ae measurableSet_Iic (g := fun _ => (1:ℝ)) (by
    filter_upwards [hae] with s hs _
    exact decRearr_const_one s.property.1 (lt_of_le_of_ne s.property.2 (fun e => hs (Subtype.ext e))))]
  simp [measureReal_def,unitInterval.volume_Iic,ENNReal.toReal_ofReal u.property.1]

theorem decRearr_condSection_mono (C : Copula 2) {v w : I} (h : v≤w) (s : I) :
    decRearr (condSection C v) s≤decRearr (condSection C w) s :=
  decRearr_mono (condSection_le_one C w) (Eventually.of_forall (condSection_mono C h)) s.property.1

theorem upRearrCDF_rectangle (C : Copula 2) (a b c d : I) (hab : a≤b) (hcd : c≤d) :
    0≤upRearrCDF C b d-upRearrCDF C a d-upRearrCDF C b c+upRearrCDF C a c := by
  unfold upRearrCDF
  set h : I → ℝ := fun s => decRearr (condSection C d) s-decRearr (condSection C c) s
  have hi : Integrable h := (integrable_decRearr_condSection C d).sub (integrable_decRearr_condSection C c)
  have hn : ∀ s, 0≤h s := fun s => sub_nonneg.mpr (decRearr_condSection_mono C hcd s)
  have hb : (∫ s in Iic b, h s)=(∫ s in Iic b, decRearr (condSection C d) s)-
      ∫ s in Iic b, decRearr (condSection C c) s :=
    integral_sub (integrable_decRearr_condSection C d).integrableOn
      (integrable_decRearr_condSection C c).integrableOn
  have ha : (∫ s in Iic a, h s)=(∫ s in Iic a, decRearr (condSection C d) s)-
      ∫ s in Iic a, decRearr (condSection C c) s :=
    integral_sub (integrable_decRearr_condSection C d).integrableOn
      (integrable_decRearr_condSection C c).integrableOn
  have hm : (∫ s in Iic a, h s)≤∫ s in Iic b, h s :=
    setIntegral_mono_set hi.integrableOn (Eventually.of_forall hn)
      (Eventually.of_forall (Iic_subset_Iic.mpr hab))
  linarith

theorem upRearrCDF_isClassical (C : Copula 2) :
    IsClassical (fun u : Fin 2→I => upRearrCDF C (u 0) (u 1)) :=
  IsClassical.ofBivariate _ (upRearrCDF_zero_left C) (upRearrCDF_zero_right C)
    (upRearrCDF_one_left C) (upRearrCDF_one_right C) (upRearrCDF_rectangle C)

/-- The increasing rearranged copula `C↑`. -/
noncomputable def upRearr (C : Copula 2) : Copula 2 := ofClassical _ (upRearrCDF_isClassical C)

theorem upRearr_cdf (C : Copula 2) (u v : I) : (upRearr C).cdf ![u,v]=upRearrCDF C u v := by
  rw [upRearr,cdf_ofClassical]
  rfl

/-- The decreasing rearranged copula `C↓(u,v)=v-C↑(1-u,v)`. -/
noncomputable def downRearr (C : Copula 2) : Copula 2 := (upRearr C).reflect {0}

theorem downRearr_cdf (C : Copula 2) (u v : I) :
    (downRearr C).cdf ![u,v]=(v:ℝ)-(upRearr C).cdf ![unitInterval.symm u,v] :=
  cdf_reflect_first _ u v

/-- The conditional distribution of `C↑` is the decreasing rearrangement. -/
theorem upRearr_conditionalCDF (C : Copula 2) (v : I) :
    (fun u => (upRearr C).conditionalCDF u v)=ᵐ[volume] fun u => decRearr (condSection C v) u :=
  (upRearr C).conditionalCDF_ae_eq_of_integral v (integrable_decRearr_condSection C v)
    (decRearr_condSection_nonneg C v) (fun u => (upRearr_cdf C u v).symm)

/-- Lemma 2.7(ii): `C↑` is conditionally increasing (CIS). -/
theorem upRearr_isSI (C : Copula 2) : (upRearr C).IsSI := by
  intro a b c v hab hbc
  simp only [upRearr_cdf]
  unfold upRearrCDF
  set f := fun s : I => decRearr (condSection C v) s
  have hfi : Integrable f := integrable_decRearr_condSection C v
  have hanti : ∀ s t : I, s≤t → f t≤f s := fun s t hst =>
    decRearr_antitoneOn (condSection_le_one C v) s.property.1 t.property.1 hst
  -- increments over `(a,b]` and `(b,c]`
  have hdiff (x y : I) (hxy : x≤y) : (∫ s in Iic y, f s)-(∫ s in Iic x, f s)=∫ s in Ioc x y, f s := by
    rw [← Iic_sdiff_Iic,setIntegral_sdiff measurableSet_Iic hfi.integrableOn (Iic_subset_Iic.mpr hxy)]
  have hlen (x y : I) (hxy : x≤y) : volume.real (Ioc x y)=(y:ℝ)-x := by
    rw [measureReal_def,unitInterval.volume_Ioc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)
  have h1 : ((b:ℝ)-a)*f b≤∫ s in Ioc a b, f s := by
    have := setIntegral_ge_of_const_le_real (μ := volume) (s := Ioc a b) (f := f) measurableSet_Ioc
      (by rw [unitInterval.volume_Ioc]; exact ENNReal.ofReal_ne_top) (fun s hs => hanti s b hs.2)
      hfi.integrableOn
    rwa [hlen a b hab,mul_comm] at this
  have h2 : (∫ s in Ioc b c, f s)≤((c:ℝ)-b)*f b := by
    have := setIntegral_mono_on (μ := volume) (s := Ioc b c) hfi.integrableOn
      (integrableOn_const (C := f b) (by rw [unitInterval.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      measurableSet_Ioc (fun s hs => hanti b s (le_of_lt hs.1))
    rwa [setIntegral_const,smul_eq_mul,hlen b c hbc] at this
  have e1 := hdiff a b hab
  have e2 := hdiff b c hbc
  have hba : 0≤(b:ℝ)-a := sub_nonneg.mpr hab
  have hcb : 0≤(c:ℝ)-b := sub_nonneg.mpr hbc
  nlinarith [mul_le_mul_of_nonneg_left h1 hcb,mul_le_mul_of_nonneg_left h2 hba]

/-- Lemma 2.7(iv): `C↑` is Schur equivalent to `C`. -/
theorem upRearr_schur_equiv (C : Copula 2) : (upRearr C).SchurLE C ∧ C.SchurLE (upRearr C) := by
  have he (v : I) (φ : ℝ → ℝ) (hφ : Continuous φ) :
      (∫ u : I, φ ((upRearr C).conditionalCDF u v))=∫ u : I, φ (C.conditionalCDF u v) := by
    rw [integral_congr_ae (g := fun u : I => φ (decRearr (condSection C v) (u:ℝ))) (by
      filter_upwards [upRearr_conditionalCDF C v] with u hu
      exact congrArg φ hu)]
    exact integral_comp_decRearr (condSection_nonneg C v) (condSection_le_one C v)
      (condSection_measurable C v) hφ.measurable
  exact ⟨fun v φ hc _ => (he v φ hc).le,fun v φ hc _ => (he v φ hc).ge⟩

theorem downRearr_schur_equiv (C : Copula 2) : (downRearr C).SchurLE C ∧ C.SchurLE (downRearr C) := by
  have hr := schurLE_of_rearrangement (downRearr C) (upRearr C) unitInterval.measurePreserving_symm
    (conditionalCDF_reflect_first (upRearr C))
  have hu := upRearr_schur_equiv C
  exact ⟨hr.1.trans hu.1,hu.2.trans hr.2⟩

/-- Hardy–Littlewood on arbitrary measurable sets. -/
theorem integral_set_le_decRearr {f : I → ℝ} (hf0 : ∀ u, 0≤f u) (hf : ∀ u, f u≤1) (hm : Measurable f)
    (A : Set I) (hA : MeasurableSet A) (x : I) (hx : volume.real A=(x:ℝ)) :
    (∫ u in A, f u)≤∫ s in Iic x, decRearr f s := by
  rw [integral_Iic_decRearr hf0 hf hm x,integral_Iic_eq_layercake hf0 hf hm A hA]
  have hb : ∀ t, volume.real (A∩{u : I | t<f u})≤min (x:ℝ) (distFun f t) := by
    intro t
    apply le_min
    · rw [← hx]; exact measureReal_mono inter_subset_left
    · exact measureReal_mono inter_subset_right
  apply setIntegral_mono_on _ _ measurableSet_Ioc (fun t _ => hb t)
  · apply Measure.integrableOn_of_bounded (M := 1)
    · simp
    · exact (antitone_measureReal_inter A f).measurable.aestronglyMeasurable
    · exact Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
        calc volume.real (A∩{u : I | t<f u})≤volume.real (univ : Set I) := measureReal_mono (subset_univ _)
          _ = 1 := by simp
  · apply Measure.integrableOn_of_bounded (M := 1)
    · simp
    · exact (Antitone.measurable (fun a b hab => min_le_min_left _ (distFun_antitone f hab))).aestronglyMeasurable
    · exact Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs,abs_of_nonneg (le_min x.property.1 (distFun_nonneg f t))]
        exact (min_le_right _ _).trans (distFun_le_one f t)

/-- The directional Schur order of copulas in its rearrangement form, on conditional CDFs. -/
def CondRearrSchurLE (D E : Copula 2) : Prop :=
  ∀ v : I, RearrSchurLE (condSection D v) (condSection E v)

theorem condRearrSchurLE_iff (D E : Copula 2) : CondRearrSchurLE D E ↔ D.SchurLE E := by
  unfold CondRearrSchurLE
  constructor
  · intro h v φ hc hv
    exact (rearrSchurLE_iff_convex (condSection_nonneg D v) (condSection_le_one D v)
      (condSection_measurable D v) (condSection_nonneg E v) (condSection_le_one E v)
      (condSection_measurable E v)).mp (h v) φ hc hv
  · intro h v
    exact (rearrSchurLE_iff_convex (condSection_nonneg D v) (condSection_le_one D v)
      (condSection_measurable D v) (condSection_nonneg E v) (condSection_le_one E v)
      (condSection_measurable E v)).mpr (fun φ hc hv => h v φ hc hv)

/-- Lemma 2.7(i): `E↑` is the lower-orthant maximum of `{D : D ≤_{∂₁S} E}`. -/
theorem lowerOrthantLE_upRearr_of_schurLE {D E : Copula 2} (h : D.SchurLE E) :
    D.LowerOrthantLE (upRearr E) := by
  have hr := (condRearrSchurLE_iff D E).mpr h
  intro w
  have hw : w=![w 0,w 1] := by ext i; fin_cases i <;> rfl
  rw [hw,upRearr_cdf,D.cdf_eq_integral_conditionalCDF]
  set v := w 1
  calc (∫ t in Iic (w 0), D.conditionalCDF t v)≤∫ s in Iic (w 0), decRearr (condSection D v) s :=
        integral_Iic_le_decRearr (condSection_nonneg D v) (condSection_le_one D v)
          (condSection_measurable D v) (w 0)
    _ ≤ upRearrCDF E (w 0) v := (hr v).1 (w 0)

/-- Lemma 2.7(i): `E↓` is the lower-orthant minimum of `{D : D ≤_{∂₁S} E}`. -/
theorem downRearr_lowerOrthantLE_of_schurLE {D E : Copula 2} (h : D.SchurLE E) :
    (downRearr E).LowerOrthantLE D := by
  have hr := (condRearrSchurLE_iff D E).mpr h
  intro w
  have hw : w=![w 0,w 1] := by ext i; fin_cases i <;> rfl
  rw [hw,downRearr_cdf,upRearr_cdf,D.cdf_eq_integral_conditionalCDF]
  set u := w 0
  set v := w 1
  set f := condSection D v
  have hfi : Integrable f := D.integrable_conditionalCDF v
  have htot : (∫ t, f t)=(v:ℝ) := D.integral_conditionalCDF v
  have hsplit : (∫ t in Iic u, f t)=(v:ℝ)-∫ t in Ioi u, f t := by
    rw [← htot,← integral_add_compl measurableSet_Iic hfi,compl_Iic]; ring
  have hvol : volume.real (Ioi u)=((unitInterval.symm u : I):ℝ) := by
    rw [measureReal_def,unitInterval.volume_Ioi,unitInterval.coe_symm_eq]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr u.property.2)
  have hHL := integral_set_le_decRearr (condSection_nonneg D v) (condSection_le_one D v)
    (condSection_measurable D v) (Ioi u) measurableSet_Ioi (unitInterval.symm u) hvol
  have hS := (hr v).1 (unitInterval.symm u)
  change (v:ℝ)-upRearrCDF E (unitInterval.symm u) v≤∫ t in Iic u, f t
  unfold upRearrCDF
  rw [hsplit]
  linarith

theorem upRearr_mem (E : Copula 2) : (upRearr E).SchurLE E := (upRearr_schur_equiv E).1

theorem downRearr_mem (E : Copula 2) : (downRearr E).SchurLE E := (downRearr_schur_equiv E).1

/-- Proposition 3.1 (i)⇔(ii). -/
theorem schurLE_iff_upRearr (D E : Copula 2) :
    D.SchurLE E ↔ (upRearr D).LowerOrthantLE (upRearr E) := by
  rw [← condRearrSchurLE_iff]
  constructor
  · intro h w
    have hw : w=![w 0,w 1] := by ext i; fin_cases i <;> rfl
    rw [hw,upRearr_cdf,upRearr_cdf]
    exact (h (w 1)).1 (w 0)
  · intro h v
    refine ⟨fun x => ?_,?_⟩
    · have := h ![x,v]
      rwa [upRearr_cdf,upRearr_cdf] at this
    · rw [show (∫ u, condSection D v u)=(v:ℝ) from D.integral_conditionalCDF v,
        show (∫ u, condSection E v u)=(v:ℝ) from E.integral_conditionalCDF v]

/-- Proposition 3.1 (ii)⇔(iii). -/
theorem upRearr_lowerOrthant_iff_downRearr (D E : Copula 2) :
    (upRearr D).LowerOrthantLE (upRearr E) ↔ (downRearr E).LowerOrthantLE (downRearr D) := by
  constructor
  · intro h w
    have hw : w=![w 0,w 1] := by ext i; fin_cases i <;> rfl
    rw [hw,downRearr_cdf,downRearr_cdf]
    have := h ![unitInterval.symm (w 0),w 1]
    linarith
  · intro h w
    have hw : w=![w 0,w 1] := by ext i; fin_cases i <;> rfl
    have := h ![unitInterval.symm (w 0),w 1]
    rw [downRearr_cdf,downRearr_cdf,unitInterval.symm_symm] at this
    rw [hw]
    linarith

end Verification
