/- Canonical target wrapper for the locally assembled candidate, 2026-10-23.
Full analytic compilation and tracker admission checks remain pending. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Endpoint
set_option autoImplicit false
namespace Candidate
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (21869322649 / 25000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact QRH.RH20261023.Endpoint.dirichlet_nonvanishing χ hs hpole
end Candidate
#print Candidate.bound
#print axioms Candidate.bound
