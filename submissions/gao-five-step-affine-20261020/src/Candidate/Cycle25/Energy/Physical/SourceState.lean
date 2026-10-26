import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Candidate.Cycle25.Assembly.SourceData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.MomentNaturalFixedRaySourceFixedIdeal
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open UniqueFactorizationMonoid CenteredMomentDetectorEnergyInitialState
open CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {D : WeightedQRH.MomentData}

lemma weighted_source_keep_iff (F:OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D)(η:Character)(u:FreeRow):
    initialKeep η (internalQ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceFixedIdeal F) η) u.val↔¬OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.weighted_sourceExceptional F η u:=by
  exact and_iff_right u.property.1

end SevenEighths.Cycle25WeightedNumeratorPhysical

end

end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/
