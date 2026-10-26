import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondHighBins
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry

/-- The actual high-source exponent coordinates: outside scalar, missing
radical, retained frequency cap, and remaining raw volume. -/
def actualHighCoordinates (reflected left second : Bool) (l : FirstSourceLabel)
    (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂))
    (Z M A a ξ reserve ε : ℝ) : Fin 4→ℝ :=
  let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
  let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
  let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
  let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
  let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
  let g₂ := Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))
  let t₂ := Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)
  let ω := frequencyLoss Z 32 ξ+reserve
  ![-a+(2*A-c-d+R+E-M+max (d-c) 0+6*a+ω-(A-c))+(g₂-t₂-b₂),
    Real.logb Z ((firstSourceMissing left l).absNorm:ℝ),
    M-R-max (c-d) 0+Lc-6*a-ω+ε,A-c-b₂]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
