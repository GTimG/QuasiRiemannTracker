/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance.
Inherited PR63 source and author notices are retained.
The two-stage proof first obtains 0.8748286 from PR63's 0.87483,
then establishes the exact rational boundary exported below.
-/
import Candidate.Notices
import Candidate.Uneven.EndpointFinal

set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter

theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (874828524351/1000000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact OAI.SevenEighths.UnevenEndpoint.Final.allDirichlet χ hs hpole

end Candidate
#print axioms Candidate.bound
