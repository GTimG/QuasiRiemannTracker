import WeightedQRH.Final

/-! The endpoints at theta = 10499/12000, stated exactly as the Comparator challenges in
`ComparatorChallenges/`: zeta and Dirichlet over Mathlib's own definitions, Hecke over the
original OpenAI definitions restated in the upstream `HeckeSevenEighths` challenge. -/
namespace OAI

theorem riemannZeta_ne_zero_of_10499_12000_lt_re
    {s : ℂ} (hs : (10499 / 12000 : ℝ) < s.re) : riemannZeta s ≠ 0 :=
  SevenEighths.WeightedHighFinalAssembly.zeta_of_fullW_input WeightedQRH.fullW_analytic_input s hs

namespace DirichletCharacter
open scoped _root_.DirichletCharacter

theorem LFunction_ne_zero_of_10499_12000_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (10499 / 12000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  WeightedQRH.dirichlet_nonzero χ s hs hpole

end DirichletCharacter

namespace SevenEighths.HeckeFamily

theorem LFunction_ne_zero_of_10499_12000_lt_re
    (χ : Character) {s : ℂ} (hs : (10499 / 12000 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) : LFunction χ s ≠ 0 :=
  WeightedQRH.hecke_nonzero χ s hs (not_and_or.mp hpole).symm

end SevenEighths.HeckeFamily

end OAI
