/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B192

set_option autoImplicit false
namespace Submissions.gao_cycle61_plane_20261013
open scoped _root_.DirichletCharacter

theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4374299 / 5000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Cycle61Verification.allDirichlet χ hs hpole

end Submissions.gao_cycle61_plane_20261013
#print axioms Submissions.gao_cycle61_plane_20261013.bound
