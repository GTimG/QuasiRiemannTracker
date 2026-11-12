/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The reserve-parametric seed and the two finite source lines.
Reserve-parametric composition (`source`) by Joe Richey, submission exact-contact-point
(QuasiRiemannTracker #129, commit 535397cd), Apache-2.0; inherited notices retained. -/
/- Modified by Sil (2026-11-11): `source` copied from exact-contact-point (#129)
PositiveGap/SourceComposition.lean, namespace changed to Qrh.MarkedAnchor.Reserve, composed with the
copied curves `Reserve.NativeBudget`, `Reserve.TightSelected` (slope 100/1143, so the cap at
`L = 2+10ε` is `3/20 - 1000ε/1143`); new: `rCap_end`, `reserveParametricSource`. -/
import Submissions.marked_anchor_induction.Qrh.PR98Improvement.RepairedRestrictedSource
import Submissions.marked_anchor_induction.Qrh.PR98Improvement.GapAdapters
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Reserve.NativeBudgetCurve
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Reserve.TightSelectedCurve
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Interface.Native

/-!
# Reserve.Source

PR103's source chain (seed `G(1-ε, 93/25, 3/50)`, native budget line
to `G(1-ε, 5143/2000, 1/10)`, tight selected line to `G(1-ε, 2+10ε, 3/20-1000ε/1143)`) re-run with
the reserve `ε` as a parameter, giving `Interface.Native.ReserveParametricSource` under `51/100 ≤ β`.
Nothing in the PR103 copy (`QRH.PositiveGap.*`) is changed.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Reserve
noncomputable section
open QRH.ArviSelectedLeaf QRH.Record1252270103Source OAI.SevenEighths

/-- The seed at reserve `ε`, then the native and tight source lines. -/
theorem source (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1/1000000000)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    GlobalSource (1 - ε) (2 + 10 * ε) (TightSelected.rCap (2 + 10 * ε)) := by
  have hseed : GlobalSource (1 - ε) (93/25) (3/50) :=
    Candidate.PR98.RepairedRestrictedSource.generalized_seed ε hε0 (by linarith only [hε1]) hβ
  have hnative : GlobalSource (1 - ε) (5143/2000) (1/10) :=
    NativeBudget.refined_end hε0 hε1 hβ
      (selectedRootEnergy _ (by norm_num [NativeBudget.rK])
        (by norm_num [NativeBudget.rK])) hseed
  exact TightSelected.refined_end hε0 hε1 hβ
    (selectedRootEnergy_above_half _ (by unfold TightSelected.rK; linarith only [hε0])
      (by unfold TightSelected.rK; linarith only [hε1])) hnative

/-- The cap at the end of the tight line. -/
theorem rCap_end (ε : ℝ) : TightSelected.rCap (2 + 10 * ε) = 3/20 - 1000/1143 * ε := by
  unfold TightSelected.rCap TightSelected.rGamma TightSelected.rTop
  ring

/-- **Reserve-parametric source**: global sources arbitrarily close to `(B, L, c) = (1, 2, 3/20)`. -/
theorem reserveParametricSource (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    Interface.Native.ReserveParametricSource := by
  intro η hη
  set ε : ℝ := min (η/20) (1/1000000000) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε ≤ 1/1000000000 := min_le_right _ _
  have hεη : ε ≤ η/20 := min_le_left _ _
  refine ⟨1 - ε, 2 + 10 * ε, TightSelected.rCap (2 + 10 * ε), source ε hε0 hε1 hβ,
    by linarith, by linarith, by linarith, ?_⟩
  rw [rCap_end]
  linarith

end
end Qrh.MarkedAnchor.Reserve

#print axioms Qrh.MarkedAnchor.Reserve.source
#print axioms Qrh.MarkedAnchor.Reserve.reserveParametricSource
