import Copula.Dependence.Frechet

/-! Compatibility names for the dependence results now proved in the pinned copula library. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

variable (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)

theorem frechet_exchangeable : (Copula.frechet a b ha hb hab).IsExchangeable :=
  Copula.frechet_exchangeable a b ha hb hab

theorem frechet_si_iff : (Copula.frechet a b ha hb hab).IsSI ↔ b = 0 :=
  Copula.frechet_si_iff a b ha hb hab

theorem frechet_sd_iff : (Copula.frechet a b ha hb hab).IsSD ↔ a = 0 :=
  Copula.frechet_sd_iff a b ha hb hab

theorem frechet_ci_iff : (Copula.frechet a b ha hb hab).IsCI ↔ b = 0 :=
  Copula.frechet_ci_iff a b ha hb hab

theorem frechet_cd_iff : (Copula.frechet a b ha hb hab).IsCD ↔ a = 0 :=
  Copula.frechet_cd_iff a b ha hb hab

theorem frechet_measure : (Copula.frechet a b ha hb hab).toMeasure =
    ENNReal.ofReal a • (Copula.comonotonic 2).toMeasure +
      ENNReal.ofReal b • Copula.countermonotonic.toMeasure +
      ENNReal.ofReal (1 - a - b) • (Copula.independence 2).toMeasure :=
  Copula.frechet_measure a b ha hb hab

theorem frechet_absolutelyContinuous_iff :
    (Copula.frechet a b ha hb hab).toMeasure ≪ (volume : Measure (Fin 2 → I)) ↔ a = 0 ∧ b = 0 :=
  Copula.frechet_absolutelyContinuous_iff a b ha hb hab

theorem frechet_density_tp2_iff :
    (Copula.frechet a b ha hb hab).HasMTP2Density ↔ a = 0 ∧ b = 0 :=
  Copula.frechet_density_tp2_iff a b ha hb hab

end Verification
