import Candidate.Provenance
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.AssemblyExtension.PublicBoundary

/-!
Historical source: TheRealDubb/family-003-extension-xenoproof,
commit b6c98187528e036b8c60414a6961ef999caf31fb.
The imported proof is supplied for independent tracker admission; no local
Comparator or multi-kernel replay is asserted by this wrapper.
-/
namespace Candidate

theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (8749570194201 / 10000000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 :=
  BelowSevenEighthsTight.PublicResults.dirichlet_LFunction_ne_zero_of_rational_lt_re
    χ s hs hpole

end Candidate
