/- Repeated marks: fork of Record1252270103Source.Low.GlobalInitialCallbacks (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialCallbacks
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainC
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.CountWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainPaymentK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Finite.SourceValid2
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.NaturalCap
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.Low.GlobalInitialAssemblyMargins
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Callable graph closures. The sole pending analytic inlet is the literal marked
first physical norm on canonical initial data, at a fixed certified width grid. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI.SevenEighths Record1252270103Finite QRH.Record1252270103Graph
open QRH.Record1252270103Source QRH.Record1252270103Restoration

def nfWidthMargin_rm (n low : Source) (high : Option Source)
    (hv : QRH.RepeatedMarks.Finite.SourceValidC n low high) (ha : NFAccounting n) (loss : ℝ) : ℝ :=
  (nf_finite_width_cells_rm n low high hv ha loss).choose
def nfWidthDelta_rm (n low : Source) (high : Option Source)
    (hv : QRH.RepeatedMarks.Finite.SourceValidC n low high) (ha : NFAccounting n) (loss : ℝ) : ℝ :=
  (nf_finite_width_cells_rm n low high hv ha loss).choose_spec.choose
def nfWidthCell_rm (n low : Source) (high : Option Source)
    (hv : QRH.RepeatedMarks.Finite.SourceValidC n low high) (ha : NFAccounting n) (loss : ℝ) : ℝ→ℝ :=
  upperWidthCell (crossing n low) n.cap (nfWidthDelta_rm n low high hv ha loss)

theorem nf_width_certificate_rm (n low : Source) (high : Option Source)
    (hv : QRH.RepeatedMarks.Finite.SourceValidC n low high) (ha : NFAccounting n) (loss : ℝ) :
    0<nfWidthMargin_rm n low high hv ha loss ∧ 0<nfWidthDelta_rm n low high hv ha loss ∧
    nfWidthDelta_rm n low high hv ha loss≤1 ∧
    |loss| *nfWidthDelta_rm n low high hv ha loss≤(n.allowance:ℝ) ∧
    2*(|loss| *nfWidthDelta_rm n low high hv ha loss)≤nfWidthMargin_rm n low high hv ha loss ∧
    FiniteReferenceCells (crossing n low) n.cap QRH.RepeatedMarks.natK (nfWidthDelta_rm n low high hv ha loss)
      (nfWidthCell_rm n low high hv ha loss) ∧
    ∀s∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),∀ν∈Set.Icc (n.q:ℝ) (3/4),
      (∀j,nfWidthMargin_rm n low high hv ha loss/2≤sourceScalarReal (9/2) n low
        (nfWidthCell_rm n low high hv ha loss s) j-|loss| *nfWidthDelta_rm n low high hv ha loss) ∧
      0≤sourceWeakReal n low (nfWidthCell_rm n low high hv ha loss s) ∧
      ∀j,QRH.RepeatedMarks.Finite.KeptGate high j →
        nfWidthMargin_rm n low high hv ha loss/2≤sourceDensityWidthReal n low high
        (nfWidthCell_rm n low high hv ha loss s) ν j-|loss| *nfWidthDelta_rm n low high hv ha loss :=
  (nf_finite_width_cells_rm n low high hv ha loss).choose_spec.choose_spec

end
end QRH.Record1252270103Low
