/- Repeated marks: fork of Record1252270103Source.HighScalar.SingletonLoss (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.HighScalar.SingletonLoss
import Submissions.arvi_repeated_marks_20261024.Source.GainC
import Submissions.arvi_repeated_marks_20261024.Source.CountWrappersK
import Submissions.arvi_repeated_marks_20261024.Source.GainPaymentK
import Submissions.arvi_repeated_marks_20261024.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_20261024.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_20261024.Finite.SourceValid2
import Submissions.arvi_repeated_marks_20261024.Fork.Record1252270103Source.HighScalar.LabelPayment
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Deleting equality-block slots keeps the exact corresponding volume loss. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.HighScalar
noncomputable section
open OAI OAI.SevenEighths Record12518109Natural.JointHigh Cycle61InitialMass
open Record1252270103Finite

theorem full_singleton_subset_payment_rm (high : Option Source) (hp : GainParameters high)
    {ν small full forced : ℝ} (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hwidth : small≤full)
    (x : Fin 4→ℝ) :
    retainedHighExponent ν (gainAt_rm high ν small)
      (lostWidthCoordinates x (forced+full-small))≤
      retainedHighExponent ν (gainAt_rm high ν full) x-ν*forced := by
  rw [retained_exponent_lost_width]
  have hm:=gainAt_weighted_width_mono_rm high hp hν0 hν1 hwidth (Q:=x 2)
  dsimp only [retainedHighExponent]
  nlinarith

end
end QRH.Record1252270103Source.HighScalar
