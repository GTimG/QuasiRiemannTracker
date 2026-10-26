import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersHighData
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace WeightedQRH
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
end WeightedQRH

end Record1252270103Bootstrap.PR67
