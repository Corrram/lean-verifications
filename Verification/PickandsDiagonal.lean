import Verification.ExtremeValuePickands
import Copula.ExtremeValue.Diagonal

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Verification

theorem extremalCoefficient_eq_twice_pickands (C : Copula 2) (hC : C.IsExtremeValue) :
    C.extremalCoefficient=2*copulaPickands C unitHalf := by
  let t : I := unitNegExp (1/4) (by norm_num)
  have he : pickandsRay unitHalf=![t,t] := by
    ext i
    fin_cases i <;> norm_num [pickandsRay,unitHalf,t,unitNegExp]
  unfold copulaPickands
  rw [he]
  change C.extremalCoefficient=2*(-2*Real.log (C.diagonal t))
  rw [hC.hasPowerDiagonal t]
  change C.extremalCoefficient=2*(-2*Real.log ((Real.exp (-(1/4:ℝ)))^C.extremalCoefficient))
  rw [Real.log_rpow (Real.exp_pos _),Real.log_exp]
  ring

end Verification
