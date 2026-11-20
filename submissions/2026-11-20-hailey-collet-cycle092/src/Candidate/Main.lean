/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Canonical all-Dirichlet entrypoint at the exact Cycle092 rational threshold. -/
import Candidate.Provenance
import Candidate.C092.transport.Cycle092Record

open scoped _root_.DirichletCharacter
namespace Candidate

theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (436666397 / 500000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : DirichletCharacter.LFunction χ s ≠ 0 := by
  exact QRH.Cycle092.dirichlet_nonvanishing χ hs hpole

end Candidate
