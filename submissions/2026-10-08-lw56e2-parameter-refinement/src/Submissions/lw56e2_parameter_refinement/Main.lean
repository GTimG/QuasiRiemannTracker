import Submissions.lw56e2_parameter_refinement.Transport.Nonvanishing

namespace Submissions.lw56e2_parameter_refinement

/-- Historical all-Dirichlet boundary of LW56e2, submitted for independent replay. -/
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4374785349 / 5000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : DirichletCharacter.LFunction χ s ≠ 0 := by
  exact LW56e2.Transport.dirichlet_nonvanishing χ s hs hpole

end Submissions.lw56e2_parameter_refinement
