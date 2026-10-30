/- All-moduli Dirichlet nonvanishing for Re(s) > 43670599/50000000 = 0.87341198 (principal pole excluded):
the selected-norm leaf of the native step (R1), two lines of faces by continuous induction, and the retuned
three-window return. No density chain is used. -/
import Submissions.arvi_selected_leaf.Final
set_option autoImplicit false
namespace Candidate
theorem bound {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (43670599 / 50000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.ArviSelectedLeaf.dirichlet_nonvanishing_e5 χ hs hpole
end Candidate
