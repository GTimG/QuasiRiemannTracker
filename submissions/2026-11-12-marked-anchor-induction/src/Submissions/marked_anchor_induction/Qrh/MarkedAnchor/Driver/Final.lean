/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Driver.Obligations
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Return.Final
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Driver.Parent
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Reserve.TopAnchors

/-!
# Driver.Final

The whole proof from `Driver.Obligations`:
anchors (176 stages) → `Contract.ImprovedMoments leftEnd topEnd lineG0 lineG1` →
(bridge) `Interface.ImprovedFiberMoments` → `Return.dirichlet_of_improved`.

Supplied here: the parent face of the ordinary step (`Price.pr103Face`;
`Driver.pr103_parent`), the base anchor `(311/400, 0)` (`Reserve.base_anchor_native`, from
`Inverse.base_anchor_of_reserve` and `Reserve.reserveParametricSource`), and the bridge (`Reserve.fiber_of_stages` =
`Interface.Bridge.fiber_of_improved_split` with the native `Reserve.top_anchors`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Driver
noncomputable section

open OAI OAI.SevenEighths

/-- The improved fiber moments consumed by the return (bridge `Reserve.fiber_of_stages`, base
anchor `Reserve.base_anchor_native`, parent `pr103_parent`). -/
theorem improvedFiber_of_obligations (O : Obligations)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) : Interface.ImprovedFiberMoments :=
  Reserve.fiber_of_stages hβ
    (improved_of_obligations O hβ (Reserve.reserveParametricSource hβ) (pr103_parent hβ)
      (Reserve.base_anchor_native hβ))

/-- `β ≤ 2183367/2500000` from the obligations. -/
theorem beta_le_of_obligations (O : Obligations) :
    HeckeZeroSupremum.beta ≤ (2183367/2500000 : ℝ) :=
  Return.beta_le_of_improved (fun hβ => improvedFiber_of_obligations O hβ)

/-- **Dirichlet nonvanishing for `Re s > 2183367/2500000` from the obligations.** -/
theorem bound_of_obligations (h : Obligations) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : (2183367 / 2500000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0 :=
  Return.dirichlet_of_improved (fun hβ => improvedFiber_of_obligations h hβ) χ hs hpole

/-- The same, in the exact shape of `Candidate.bound`. -/
theorem bound (h : Obligations) {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (2183367 / 2500000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  bound_of_obligations h χ hs hpole

end
end Qrh.MarkedAnchor.Driver

#print axioms Qrh.MarkedAnchor.Driver.bound_of_obligations
#print axioms Qrh.MarkedAnchor.Driver.bound
