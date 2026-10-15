import Submissions.single_prime_29_33_20261010.ZetaZeroFree.Analytic.Final

namespace Submissions.single_prime_29_33_20261010
open scoped _root_.DirichletCharacter

theorem bound {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (29 / 33 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact ZetaZeroFree.Analytic.dirichletL_ne_zero_of_twenty_nine_thirty_thirds_lt_re χ hs hpole

end Submissions.single_prime_29_33_20261010

#print axioms Submissions.single_prime_29_33_20261010.bound
