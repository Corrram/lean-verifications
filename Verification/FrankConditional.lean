import Verification.FrankOrder
import Copula.Rank.ConditionalDerivative
import Verification.KendallConditionalProduct

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem frank_exp_den_ne_zero {θ : ℝ} (hθ : θ≠0) : 1-Real.exp (-θ)≠0 := by
  intro h
  have he : Real.exp (-θ)=Real.exp 0 := by simpa using (sub_eq_zero.mp h).symm
  have hh := Real.exp_injective he
  exact hθ (by linarith)

theorem frankDen_ne_zero {θ : ℝ} (hθ : θ≠0) (u v : I) : frankDen θ u v≠0 := by
  have he := frank_exp_den_ne_zero hθ
  have he' : -1+Real.exp (-θ)≠0 := by intro h; apply he; linarith
  have hh := frank_log_base_pos hθ u v
  have hid : 1+(Real.exp (-θ*(u:ℝ))-1)*(Real.exp (-θ*(v:ℝ))-1)/(Real.exp (-θ)-1)=
      frankDen θ u v/(1-Real.exp (-θ)) := by
    unfold frankDen
    field_simp [he,he']
    ring_nf
    field_simp [he']
    ring
  rw [hid] at hh
  exact (div_ne_zero_iff.mp hh.ne').1

theorem frankRegularCDF_eq_real {θ : ℝ} (hθ : θ≠0) (u v : ℝ) :
    frankRegularCDF u v θ=frankRealCDF θ u v := by
  rw [frankRegularCDF_formula hθ]
  unfold frankRealCDF
  congr 2
  congr 1
  have he := frank_exp_den_ne_zero hθ
  have he' : -1+Real.exp (-θ)≠0 := by intro h; apply he; linarith
  unfold frankDen
  field_simp [he,he']
  ring_nf
  field_simp [he']
  ring

theorem frank_conditionalCDF_of_cdf (C : Copula 2) {θ : ℝ} (hθ : θ≠0)
    (hc : ∀ u v : I, C.cdf ![u,v]=frankRealCDF θ u v) (v : I) :
    (fun u => C.conditionalCDF u v) =ᵐ[volume] fun u => frankPartial θ u v := by
  filter_upwards [C.conditionalCDF_eq_deriv v,Measure.ae_ne volume (0:I),
    Measure.ae_ne volume (1:I)] with u hu hu0 hu1
  rw [hu]
  have h0 : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have h1 : (u:ℝ)<1 := lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))
  have he : cdfSection C v =ᶠ[𝓝 (u:ℝ)] fun x => frankRealCDF θ x v := by
    filter_upwards [Ioo_mem_nhds h0 h1] with x hx
    have hh := hc (⟨x,hx.1.le,hx.2.le⟩:I) v
    simpa only [cdfSection,projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩] using hh
  exact ((frank_cdf_derivative hθ (frankDen_ne_zero hθ u v)
    (frank_exp_den_ne_zero hθ)).congr_of_eventuallyEq he).deriv

theorem frank_kendallTau_integral_of_cdf (C : Copula 2) {θ : ℝ} (hθ : θ≠0)
    (hc : ∀ u v : I, C.cdf ![u,v]=frankRealCDF θ u v) :
    C.kendallTau=1-4*(∫ v : I, ∫ u : I, frankPartial θ u v*frankPartial θ v u) := by
  have hCt : C.transpose=C := by
    apply Copula.ext_cdf
    intro z
    have hz : z=![z 0,z 1] := by funext i; fin_cases i <;> rfl
    rw [hz,Copula.cdf_transpose,hc,hc]
    unfold frankRealCDF frankDen
    congr 3
    ring
  have ha : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF v u=frankPartial θ v u := by
    apply (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun u v => C.conditionalCDF v u=frankPartial θ v u)
      (measurableSet_eq_fun C.measurable_conditionalCDF (by unfold frankPartial frankDen; fun_prop))).mp
    exact Eventually.of_forall (frank_conditionalCDF_of_cdf C hθ hc)
  rw [kendallTau_conditional_product,hCt]
  congr 2
  apply integral_congr_ae
  filter_upwards [ha] with v hv
  apply integral_congr_ae
  filter_upwards [hv,frank_conditionalCDF_of_cdf C hθ hc v] with u hu hv'
  rw [hu,hv',mul_comm]

end Verification
