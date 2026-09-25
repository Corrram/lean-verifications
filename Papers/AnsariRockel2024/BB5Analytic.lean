import Verification.BB5Kernel

open ProbabilityTheory Real Set Copula

namespace Papers.AnsariRockel2024

theorem bb5_exponent_formula (θ δ x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    Verification.bb5TailKernel θ δ x y=(x^θ+y^θ-(x^(-δ*θ)+y^(-δ*θ))^(-1/δ))^(1/θ) :=
  Verification.bb5TailKernel_formula θ δ x y hx hy

theorem bb5_exponent_bounds (θ δ x y : ℝ) (hθ : 1≤θ) (hδ : 0<δ) (hx : 0<x) (hy : 0<y) :
    max x y ≤ Verification.bb5TailKernel θ δ x y ∧ Verification.bb5TailKernel θ δ x y ≤ x+y :=
  Verification.bb5TailKernel_bounds θ δ x y hθ hδ hx hy

theorem bb5_exponent_homogeneous (θ δ c x y : ℝ) (hθ : 1≤θ) (hδ : 0<δ)
    (hc : 0<c) (hx : 0<x) (hy : 0<y) :
    Verification.bb5TailKernel θ δ (c*x) (c*y)=c*Verification.bb5TailKernel θ δ x y :=
  Verification.bb5TailKernel_homogeneous θ δ c x y hθ hδ hc hx hy

theorem bb5_exponent_shape_one (δ x y : ℝ) :
    Verification.bb5TailKernel 1 δ x y=x+y-Verification.galambosTailKernel δ x y :=
  Verification.bb5TailKernel_shape_one δ x y

end Papers.AnsariRockel2024
