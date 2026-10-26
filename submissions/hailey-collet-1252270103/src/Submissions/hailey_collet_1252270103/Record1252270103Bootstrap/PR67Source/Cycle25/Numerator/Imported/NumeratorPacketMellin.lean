import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.NumeratorMassDamping
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Numerator.Imported.NumeratorPolynomialMass
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Weighted.WeightedQRH.MellinReconstruction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-! Mellin inversion of the actual numerator with the complete error packet. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators NNReal Classical ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

instance correctionIndex_countable (S : Finset (Ideal O)) (u : FreeRow) :
    Countable (WeightedQRH.Numerator.CorrectionIndex S u) := by unfold WeightedQRH.Numerator.CorrectionIndex WeightedQRH.Numerator.EulerIndex; infer_instance
instance errorPacketIndex_countable (S : Finset (Ideal O)) (u : FreeRow)
    (T : Finset HeckeInverseAmplification.PrimeIdeal) : Countable (WeightedQRH.Numerator.ErrorPacketIndex S u T) := by
  unfold WeightedQRH.Numerator.ErrorPacketIndex
  infer_instance

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
end Record1252270103Bootstrap.PR67
