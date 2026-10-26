/- The candidate bound 349843/400000 = 0.8746075.
The repeated-mark face family (Faceless/, Faceless/Gen/Chain.lean) starts on Sil's fourth-power
source face `GlobalSource (99999/100000) (93/25) (3/50)` (upstream PR 74, vendored in FourthPower/
with the contrary hypothesis weakened to `51/100 ≤ β`; Graph/Start.lean) at its tangency with the
continuum flow, and runs to its end; the final return (FinalReturn/) closes at 0.8746075. The natural
cost is K = 9/2, whose cap 6(2β − 1) ≤ K is the baseline's β ≤ 7/8 (Graph/NaturalCap.lean). The
source step `nf_step2` (Source/NFStep2.lean) is the repeated-mark fork of Collet's NF step. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.Endpoint
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.NFStep2

set_option autoImplicit false

namespace Candidate

theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (349843 / 400000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  apply QRH.RepeatedMarks.Graph.dirichlet_of_step QRH.RepeatedMarks.Source.nf_step2 χ s _ hpole
  convert hs using 1
  norm_num [QRH.RepeatedMarks.Return.theta, QRH.RepeatedMarks.Return.c]

end Candidate
