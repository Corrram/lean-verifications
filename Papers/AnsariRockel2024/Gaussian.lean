import Verification.GaussianRepresentation
import Verification.GaussianWedge
import Verification.GaussianTau
import Verification.GaussianRho
import Verification.GaussianConditional
import Verification.GaussianXi
import Verification.GaussianQuantileConditional
import Verification.GaussianDependence
import Verification.GaussianNormalDensity
import Verification.GaussianCopulaDensity
import Verification.GaussianTP2
import Verification.GaussianTails
import Verification.GaussianOrder

/-! # Gaussian family: admissible parameters, benchmark members and source domain check -/

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem gaussian_correlation_admissible (r : ℝ) :
    (Verification.bivariateCorrelation r).PosSemidef ↔ r∈Icc (-1) 1 :=
  Verification.bivariateCorrelation_posSemidef_iff r

theorem gaussian_zero : Verification.gaussianBivariate 0 (by norm_num)=independence 2 :=
  Verification.gaussianBivariate_zero

theorem gaussian_one : Verification.gaussianBivariate 1 (by norm_num)=comonotonic 2 :=
  Verification.gaussianBivariate_one

theorem gaussian_symmetric {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).transpose=Verification.gaussianBivariate r hr :=
  Verification.gaussianBivariate_transpose hr

theorem gaussian_zero_association :
    (Verification.gaussianBivariate 0 (by norm_num)).spearmanRho=0 ∧
    (Verification.gaussianBivariate 0 (by norm_num)).kendallTau=0 ∧
    (Verification.gaussianBivariate 0 (by norm_num)).chatterjeeXi=0 := by
  rw [gaussian_zero]
  simp

theorem gaussian_one_association :
    (Verification.gaussianBivariate 1 (by norm_num)).spearmanRho=1 ∧
    (Verification.gaussianBivariate 1 (by norm_num)).kendallTau=1 ∧
    (Verification.gaussianBivariate 1 (by norm_num)).chatterjeeXi=1 := by
  rw [gaussian_one]
  simp

theorem gaussian_printed_xi_argument_outside_domain {r : ℝ}
    (hr : r∈Ioo (-1) (-(1/2))) : 1<Verification.gaussianPrintedXiArgument r :=
  Verification.gaussianPrintedXiArgument_gt_one hr

theorem gaussian_printed_xi_argument_counterexample :
    Verification.gaussianPrintedXiArgument (-(3/4))=11/4 ∧
      Verification.gaussianPrintedXiArgument (-(3/4))∉Icc (-1) 1 :=
  Verification.gaussianPrintedXiArgument_counterexample

theorem gaussian_neg {r : ℝ} (hr : r∈Icc (-1) 1) :
    Verification.gaussianBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])=
      (Verification.gaussianBivariate r hr).reflect {1} := Verification.gaussianBivariate_neg hr

theorem gaussian_negative_one :
    Verification.gaussianBivariate (-1) (by norm_num)=countermonotonic :=
  Verification.gaussianBivariate_negative_one

theorem gaussian_negative_one_association :
    (Verification.gaussianBivariate (-1) (by norm_num)).spearmanRho= -1 ∧
    (Verification.gaussianBivariate (-1) (by norm_num)).kendallTau= -1 ∧
    (Verification.gaussianBivariate (-1) (by norm_num)).chatterjeeXi=1 := by
  rw [gaussian_negative_one]
  simp

theorem gaussian_xi_neg {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])).chatterjeeXi=
      (Verification.gaussianBivariate r hr).chatterjeeXi := Verification.gaussianBivariate_xi_neg hr

theorem gaussian_rho_neg {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])).spearmanRho=
      -(Verification.gaussianBivariate r hr).spearmanRho := Verification.gaussianBivariate_rho_neg hr

theorem gaussian_tau_neg {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])).kendallTau=
      -(Verification.gaussianBivariate r hr).kendallTau := Verification.gaussianBivariate_tau_neg hr

theorem gaussian_printed_xi_formula_false :
    ¬∀ (r : ℝ) (hr : r∈Icc (-1) 1),
      (Verification.gaussianBivariate r hr).chatterjeeXi=Verification.gaussianPrintedXi r :=
  Verification.gaussian_printed_xi_formula_false

theorem gaussian_toMeasure_independent {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).toMeasure =
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map
        (fun x => ![cdfUnit (gaussianReal 0 1) (x 0),
          cdfUnit (gaussianReal 0 1) (r*x 0+Real.sqrt (1-r^2)*x 1)]) :=
  Verification.gaussianBivariate_toMeasure_independent hr

theorem gaussian_rho_normal_integral {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).spearmanRho =
      12*(∫ x : Fin 2 → ℝ, ProbabilityTheory.cdf (gaussianReal 0 1) (x 0)*
        ProbabilityTheory.cdf (gaussianReal 0 1) (r*x 0+Real.sqrt (1-r^2)*x 1)
        ∂Measure.pi (fun _ => gaussianReal 0 1))-3 :=
  Verification.gaussianBivariate_rho_normal_integral hr

theorem gaussian_wedge_probability {a : ℝ} (ha : 0≤a) :
    (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
      (if y≤a*x then (1:ℝ) else 0) ∂gaussianReal 0 1 ∂gaussianReal 0 1)=
      Real.arctan a/(2*Real.pi) := Verification.standardGaussian_wedge ha

theorem gaussian_halfline_cdf_integral (a : ℝ) :
    (∫ x in Ioi (0:ℝ), ProbabilityTheory.cdf (gaussianReal 0 1) (a*x) ∂gaussianReal 0 1)=
      1/4+Real.arctan a/(2*Real.pi) := Verification.integral_standardGaussian_cdf a

theorem gaussian_kendallTau {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).kendallTau=2/Real.pi*Real.arcsin r :=
  Verification.gaussianBivariate_kendallTau hr

theorem gaussian_spearmanRho {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).spearmanRho=6/Real.pi*Real.arcsin (r/2) :=
  Verification.gaussianBivariate_spearmanRho hr

theorem gaussian_cdf_normal {r : ℝ} (hr : r∈Ioo (-1) 1) (a b : ℝ) :
    (Verification.gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).cdf
      ![cdfUnit (gaussianReal 0 1) a,cdfUnit (gaussianReal 0 1) b]=
      ∫ x in Iic a, ProbabilityTheory.cdf (gaussianReal 0 1)
        ((b-r*x)/Real.sqrt (1-r^2)) ∂gaussianReal 0 1 :=
  Verification.gaussianBivariate_cdf_normal hr a b

theorem gaussian_conditionalCDF_normal {r : ℝ} (hr : r∈Ioo (-1) 1) (b : ℝ) :
    (fun x => (Verification.gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).conditionalCDF
      (cdfUnit (gaussianReal 0 1) x) (cdfUnit (gaussianReal 0 1) b)) =ᵐ[gaussianReal 0 1]
      fun x => ProbabilityTheory.cdf (gaussianReal 0 1) ((b-r*x)/Real.sqrt (1-r^2)) :=
  Verification.gaussianBivariate_conditionalCDF_normal hr b

theorem gaussian_xi_normal_integral {r : ℝ} (hr : r∈Ioo (-1) 1) :
    (Verification.gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).chatterjeeXi=
      6*(∫ b, ∫ x, (ProbabilityTheory.cdf (gaussianReal 0 1)
        ((b-r*x)/Real.sqrt (1-r^2)))^2 ∂gaussianReal 0 1 ∂gaussianReal 0 1)-2 :=
  Verification.gaussianBivariate_xi_normal_integral hr

theorem gaussian_chatterjeeXi {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).chatterjeeXi=
      3/Real.pi*Real.arcsin ((1+r^2)/2)-1/2 :=
  Verification.gaussianBivariate_chatterjeeXi hr

theorem gaussian_conditionalCDF_quantile {r : ℝ} (hr : r∈Ioo (-1) 1)
    {v : I} (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    (fun u => (Verification.gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).conditionalCDF u v)=ᵐ[volume]
      Verification.gaussianQuantileConditional r v :=
  Verification.gaussianBivariate_conditionalCDF_quantile hr hv

theorem gaussian_conditional_antitoneOn {r : ℝ} (hr : 0≤r) (v : I) :
    AntitoneOn (Verification.gaussianQuantileConditional r v) {u : I | (u:ℝ)∈Ioo (0:ℝ) 1} :=
  Verification.gaussianQuantileConditional_antitoneOn hr v

theorem gaussian_conditional_monotoneOn {r : ℝ} (hr : r≤0) (v : I) :
    MonotoneOn (Verification.gaussianQuantileConditional r v) {u : I | (u:ℝ)∈Ioo (0:ℝ) 1} :=
  Verification.gaussianQuantileConditional_monotoneOn hr v

theorem gaussian_isCI_iff {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).IsCI ↔ 0≤r :=
  Verification.gaussianBivariate_isCI_iff hr

theorem gaussian_isCD_iff {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).IsCD ↔ r≤0 :=
  Verification.gaussianBivariate_isCD_iff hr

theorem gaussian_isPQD_iff {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).IsPQD ↔ 0≤r :=
  Verification.gaussianBivariate_isPQD_iff hr

theorem gaussian_isNQD_iff {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).IsNQD ↔ r≤0 :=
  Verification.gaussianBivariate_isNQD_iff hr

theorem gaussian_absolutelyContinuous_iff {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).toMeasure ≪ volume ↔ r∈Ioo (-1) 1 :=
  Verification.gaussianBivariate_absolutelyContinuous_iff hr

theorem gaussian_toMeasure_normal_density {r : ℝ} (hr : r∈Ioo (-1) 1) :
    (Verification.gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).toMeasure=
      ((volume : Measure (ℝ×ℝ)).withDensity
        (fun p => gaussianPDF 0 1 p.1*gaussianPDF (r*p.1) (1-r^2).toNNReal p.2)).map
          (fun p => ![cdfUnit (gaussianReal 0 1) p.1,cdfUnit (gaussianReal 0 1) p.2]) :=
  Verification.gaussianBivariate_toMeasure_normal_density hr

theorem gaussian_density {r : ℝ} (hr : r∈Ioo (-1) 1) :
    (Verification.gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).toMeasure=
      volume.withDensity (fun u => ENNReal.ofReal (Verification.gaussianCopulaDensity r u)) :=
  Verification.gaussianBivariate_density hr

theorem gaussian_hasMTP2Density_iff {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).HasMTP2Density ↔ 0≤r ∧ r<1 :=
  Verification.gaussianBivariate_hasMTP2Density_iff hr

theorem gaussian_radiallySymmetric {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).IsRadiallySymmetric :=
  Verification.gaussianBivariate_radiallySymmetric hr

theorem gaussian_lowerTail {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).HasLowerTailDependence (if r=1 then 1 else 0) :=
  Verification.gaussianBivariate_lowerTail hr

theorem gaussian_upperTail {r : ℝ} (hr : r∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).HasUpperTailDependence (if r=1 then 1 else 0) :=
  Verification.gaussianBivariate_upperTail hr

theorem gaussian_lowerOrthant_iff {r s : ℝ} (hr : r∈Icc (-1) 1) (hs : s∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).LowerOrthantLE (Verification.gaussianBivariate s hs) ↔ r≤s :=
  Verification.gaussianBivariate_lowerOrthant_iff hr hs

theorem gaussian_schur_iff {r s : ℝ} (hr : r∈Icc (-1) 1) (hs : s∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).SchurLE (Verification.gaussianBivariate s hs) ↔ |r|≤|s| :=
  Verification.gaussianBivariate_schur_iff hr hs

theorem gaussian_schurBoth_iff {r s : ℝ} (hr : r∈Icc (-1) 1) (hs : s∈Icc (-1) 1) :
    (Verification.gaussianBivariate r hr).SchurBothLE (Verification.gaussianBivariate s hs) ↔ |r|≤|s| :=
  Verification.gaussianBivariate_schurBoth_iff hr hs

end Papers.AnsariRockel2024
