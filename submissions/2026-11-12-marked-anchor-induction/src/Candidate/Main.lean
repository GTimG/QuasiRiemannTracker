/- Copyright (c) 2026 Sil. Apache-2.0.
The candidate bound 2183367/2500000 = 0.8733468 for all Dirichlet L-functions, with the
principal pole excluded. The proof is `Qrh.MarkedAnchor.Driver.bound_unconditional`
(Submissions/marked_anchor_induction/Qrh/MarkedAnchor/Driver/Unconditional.lean). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Driver.Unconditional

set_option autoImplicit false

namespace Candidate

theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (2183367 / 2500000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  Qrh.MarkedAnchor.Driver.bound_unconditional χ hs hpole

end Candidate
