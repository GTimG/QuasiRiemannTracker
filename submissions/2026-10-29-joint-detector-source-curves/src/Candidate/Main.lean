/- Copyright (c) 2026 Joseph Bebel. -/
/- Canonical Dirichlet nonvanishing theorem. Supporting notices retained. Apache-2.0. -/
import Candidate.Notices
import Candidate.Local.Qrh.JointDetector.FollowupSources.BestEndpoint

set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4369178514865427/5000000000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact _root_.Qrh.JointDetector.FollowupSources.BestEndpoint.bound χ hs hpole
end Candidate
#print axioms Candidate.bound
