import Submissions.arvi_selected_leaf.Tuning.CoverQ

/-!
# The count windows of the reflective return

Three windows replace the 31 windows (and the 31 files `Rows/AdmissionNN.lean`, 465 Bernstein
identities) of `arvi_density`'s merged return. Each is the rational data of a branch and a rectangle
`[dlo, dhi] × [plo, 1/2]`, chosen as a maximal rectangle on which the branch is admissible
(`research/fresh-look/`, design 2); the fifteen guards of all three are certified by one kernel check.

The count face and the physical face are the same face `G(99999/100000, 401/200, 13399/100000)`
(`Constants.lean`): the uncapped count branch `C` gives two windows and the capped physical branch `capP`
(cap `3/25`) one.
-/

set_option autoImplicit false

namespace QRH.ArviReturnTuning

open QRH.ArviDensity.Return

/-- `(branch, dlo, dhi, plo)`: the count face `C` on `[2847/8192, 8189/16384] × [0, 1/2]` and on
`[2847/8192, 9507/16384] × [3/8, 1/2]`, and the capped physical face on `[1/16384, 3273/8192] × [3/8, 1/2]`.
The order is the order in which the edge covers try the windows. -/
def winsQ : List WinQ :=
  [⟨.C, 2847 / 8192, 8189 / 16384, 0⟩,
   ⟨.C, 2847 / 8192, 9507 / 16384, 3 / 8⟩,
   ⟨.capP, 1 / 16384, 3273 / 8192, 3 / 8⟩]

/-- The bounds and the fifteen guards of every window (no subdivision needed). -/
theorem windows_ok : winsQ.all (WinQ.ok 0) = true := by decide +kernel

noncomputable section

/-- The windows of the return. -/
def returnWindows : List ReturnCountWindow := mkWindows 0 winsQ windows_ok

end

end QRH.ArviReturnTuning
