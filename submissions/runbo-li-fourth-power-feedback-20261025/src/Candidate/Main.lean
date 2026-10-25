/- Copyright (c) 2026 Runbo Li. Apache-2.0.
Tracker entry point for the fourth-power natural-tail feedback candidate.
The analytic construction builds on Sil, OpenAI, Hailey Collet and ArviFoxy.
The independent finite checker compiled; the full analytic build is pending.
-/
import Candidate.Feedback.FourthPower.RepairedUnconditionalEndpoint

set_option autoImplicit false

namespace Candidate
open scoped _root_.DirichletCharacter

/-- Dirichlet nonvanishing for Re(s) > 21867321/25000000,
with the principal pole excluded. Full tracker validation is pending. -/
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (21867321 / 25000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Feedback.FourthPower.RepairedUnconditionalEndpoint.dirichlet_nonvanishing χ hs hpole

end Candidate
