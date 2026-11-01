/- Copyright (c) 2026 Joseph Bebel. -/
/- Canonical Dirichlet nonvanishing theorem. Supporting notices retained. Apache-2.0. -/
import Candidate.Notices
import Candidate.Local.Qrh.PositiveGap.BestEndpoint

set_option autoImplicit false
namespace Candidate
open scoped _root_.DirichletCharacter
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (2804966284017490358030969257914123810640482798488248385236764587735806455694206308975383836842958115341512355256943573632654341/3211614609922119834694179379888743028634953588197852962423516288191911449231164741438582626063161096341458934143644085157872271 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact _root_.Qrh.PositiveGap.bound χ hs hpole
end Candidate
#print axioms Candidate.bound
