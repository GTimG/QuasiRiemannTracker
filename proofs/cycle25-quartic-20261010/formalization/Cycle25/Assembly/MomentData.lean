import OAI.NumberTheory.DirichletL.ParametersHighData
namespace Cycle25.Weighted
structure MomentData where
  N : ℕ
  ell : Fin N → ℝ
  t : ℝ
  ε : ℝ
  e : ℝ
  t_pos : 0 < t
  t_small : t ≤ 1/100000000
  slots_injective : Function.Injective ell
  slots_bounds : ∀j, 0 < ell j ∧ ell j ≤ 1
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1/1000
  e_pos : 0 < e
end Cycle25.Weighted

/- Adapted unchanged from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
