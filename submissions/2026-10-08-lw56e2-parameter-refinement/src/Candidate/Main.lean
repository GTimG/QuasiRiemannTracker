import Candidate.Provenance
import Submissions.lw56e2_parameter_refinement.Main

namespace Candidate

theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4374785349 / 5000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Submissions.lw56e2_parameter_refinement.bound χ hs hpole

end Candidate
