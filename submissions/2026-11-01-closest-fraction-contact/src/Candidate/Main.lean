/- Copyright (c) 2026 Joseph Bebel. -/
/- Canonical Dirichlet nonvanishing theorem. Supporting notices retained. Apache-2.0. -/
import Candidate.Notices
import Candidate.Local.Qrh.PositiveGap.BestEndpoint

set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (85998815445591995045617442854510650009807585671063701704698374601780521698847984717028926388909694376216330546972078422679966327876333414101682128490050144136911675882277912668432955099145414352839188/98466442785711964046619206913281608199091477292222643843194649281096400234705587949372399371143628458591882000238942756178291736362325619423768555619610991712145905506921504685975532085115807681607811 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact _root_.Qrh.PositiveGap.bound χ hs hpole
end Candidate
#print axioms Candidate.bound
