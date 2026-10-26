/- The source theorem of the chain's first parent.

Sil proves `GlobalSource (99999/100000) (93/25) (3/50)` from a fourth-power source moment
(`RepairedRestrictedSource.actual_global_source`, upstream PR 74, Apache-2.0). That statement assumes
`theta < beta` for the target `theta = 1749387/2000000` of PR 74, and the construction uses that only through
`51/100 ≤ beta`. The copy in `FourthPower/` states it with `51/100 ≤ beta`
(`research/combined/fork_sil.py`), so the face holds for every `beta` above `51/100`. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.Graph.StartFace
import Submissions.runbo_li_arvi_face_8746074_20261026.Graph.NaturalCap
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedRestrictedSource
set_option autoImplicit false
namespace QRH.RepeatedMarks
open OAI.SevenEighths

/-- The chain's first parent is a global source. The cap `6(2β − 1) ≤ K` is not needed here; it is
an argument so that every start face has the same interface. -/
theorem start_source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (_hk : 6*(2*HeckeZeroSupremum.beta-1) ≤ natK) : QRH.Record1252270103Graph.P start := by
  have h := Candidate.FourthPower.RepairedRestrictedSource.actual_global_source hβ
  simpa [QRH.Record1252270103Graph.P, start] using h

end QRH.RepeatedMarks
