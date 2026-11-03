import Submissions.crossnox_perturbed_boundary.OAIHighUnconditional

namespace Submissions.crossnox_perturbed_boundary

/-- Historical CrossNox parameter refinement, in the canonical tracker form. -/
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4374785349 / 5000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact OAI.SevenEighths.PerturbedZeroFree.prove_dirichlet_nonvanishing
    q (NeZero.ne q) χ s hs hpole

end Submissions.crossnox_perturbed_boundary
