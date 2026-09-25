import Copula.Families.Gaussian.Identities
import Copula.Rank.ChatterjeeExamples
import Copula.Rank.Benchmarks
import Copula.Reflection.Bivariate

open ProbabilityTheory MeasureTheory Set Copula

namespace Verification

def bivariateCorrelation (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1,r;r,1]

theorem bivariateCorrelation_posSemidef {r : ℝ} (hr : r∈Icc (-1) 1) :
    (bivariateCorrelation r).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [bivariateCorrelation,Matrix.conjTranspose_apply]
  · intro x
    norm_num [bivariateCorrelation,dotProduct,Matrix.mulVec,Fin.sum_univ_two]
    have h₁ := mul_nonneg (show 0≤1+r by linarith [hr.1]) (sq_nonneg (x 0+x 1))
    have h₂ := mul_nonneg (show 0≤1-r by linarith [hr.2]) (sq_nonneg (x 0-x 1))
    nlinarith

noncomputable def gaussianBivariate (r : ℝ) (hr : r∈Icc (-1) 1) : Copula 2 :=
  gaussian (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
    (by intro i; fin_cases i <;> rfl)

theorem gaussianBivariate_zero : gaussianBivariate 0 (by norm_num)=independence 2 := by
  have he : bivariateCorrelation 0=(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bivariateCorrelation]
  unfold gaussianBivariate
  simp only [he,gaussian_one]

theorem gaussianBivariate_one : gaussianBivariate 1 (by norm_num)=comonotonic 2 := by
  have he : bivariateCorrelation 1=Matrix.of (fun (_ _ : Fin 2) => (1:ℝ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  unfold gaussianBivariate
  simp only [he,gaussian_allOnes]

theorem gaussianBivariate_transpose {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).transpose=gaussianBivariate r hr := by
  unfold gaussianBivariate Copula.transpose
  rw [gaussian_reindex]
  have he : (bivariateCorrelation r).submatrix ![1,0] ![1,0]=bivariateCorrelation r := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  simp only [he]

theorem bivariateCorrelation_posSemidef_iff (r : ℝ) :
    (bivariateCorrelation r).PosSemidef ↔ r∈Icc (-1) 1 := by
  constructor
  · intro hr
    have h₁ := hr.dotProduct_mulVec_nonneg (![1,1] : Fin 2 → ℝ)
    have h₂ := hr.dotProduct_mulVec_nonneg (![1,-1] : Fin 2 → ℝ)
    norm_num [bivariateCorrelation,dotProduct,Matrix.mulVec,Fin.sum_univ_two] at h₁ h₂
    constructor <;> linarith
  · exact bivariateCorrelation_posSemidef

/-- The literal argument printed in arXiv v3 Table 6. -/
noncomputable def gaussianPrintedXiArgument (r : ℝ) : ℝ := 1/2+r^2/(1+r)

theorem gaussianPrintedXiArgument_gt_one {r : ℝ} (hr : r∈Ioo (-1) (-(1/2))) :
    1<gaussianPrintedXiArgument r := by
  have hd : 0<1+r := by linarith [hr.1]
  have hp : 0<(2*r+1)*(r-1) := mul_pos_of_neg_of_neg (by linarith [hr.2]) (by linarith [hr.2])
  have hh : (1/2:ℝ)<r^2/(1+r) := (lt_div_iff₀ hd).mpr (by nlinarith)
  unfold gaussianPrintedXiArgument
  linarith

theorem gaussianPrintedXiArgument_counterexample :
    gaussianPrintedXiArgument (-(3/4))=11/4 ∧
      gaussianPrintedXiArgument (-(3/4))∉Icc (-1) 1 := by
  norm_num [gaussianPrintedXiArgument]

end Verification
