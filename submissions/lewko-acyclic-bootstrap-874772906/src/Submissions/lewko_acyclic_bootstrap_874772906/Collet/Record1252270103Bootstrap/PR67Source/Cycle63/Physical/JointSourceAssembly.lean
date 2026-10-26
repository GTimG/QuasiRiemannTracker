import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstReferenceSource
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-! The actual first-source labels stay in the Hilbert index. This bridge
does not supply an analytic energy estimate; it transports jointly proved
estimates to the original physical mass without a label-cardinality loss. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace OAI.SevenEighths.Cycle63JointSource
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceSource CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstSourceReduction
open CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentExceptionalAmplitudePair

local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev SourceCoordinate (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) :=
  (p : Labels s R seed) ×
    (E : ↥(inactiveSubsets p.val.1 p.val.2)) ×
      SourceBlocks s R seed K Z ξ p E.val

end OAI.SevenEighths.Cycle63JointSource

end
end Record1252270103Bootstrap.PR67
