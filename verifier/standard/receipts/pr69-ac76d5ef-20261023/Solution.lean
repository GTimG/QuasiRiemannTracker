import Candidate.Main


namespace QRH
open scoped _root_.DirichletCharacter

theorem canonical_bound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (8747729897 / 10000000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Candidate.bound χ hs hpole

end QRH
