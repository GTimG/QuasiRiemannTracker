/- Copyright (c) 2026 Sil. Apache-2.0.
The field of `Obligations` (the slot restoration of the selection child) is supplied by
`Inverse.Restore.restoreChildBoundUniform_canonical`, giving the unconditional theorem. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Driver.Final
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Main

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Driver

/-- The obligations of the assembly. -/
theorem obligations : Obligations :=
  ⟨fun _ => Inverse.Restore.restoreChildBoundUniform_canonical⟩

/-- **Dirichlet nonvanishing for `Re s > 2183367/2500000`, unconditional.** -/
theorem bound_unconditional {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (2183367 / 2500000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  bound obligations χ hs hpole

end Qrh.MarkedAnchor.Driver
