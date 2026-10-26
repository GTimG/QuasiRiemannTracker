import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalCapacity.Capacity
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63FinalCapacity
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorExtraction CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentSourceLiveColumn CenteredMomentAllocatedNaturalSource
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open CompletedGauss CanonicalQuadraticSieve CenteredMomentEnergyBands
open CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The nominal width from the genuine second transform. Its common
 frequency/unit shift is kept literal. -/
def secondNominal (M Z amp omega : ℝ) (C₁ D₁ C₂ D₂ : Ideal O)
    (U : Finset (CommonIndex C₂ D₂)) : ℝ :=
  M-max (Real.logb Z (C₁.absNorm:ℝ)-Real.logb Z (D₁.absNorm:ℝ)) 0-6*amp-omega-
    Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)

/-- This support error is fixed before the original live input, both
 common allocations, the residual selection, and every frequency/height. -/
def supportPadding (N : ℕ) (b b₁ b₂ Z : ℝ) : ℝ :=
  2*(N:ℝ)*Real.logb Z b+Real.logb Z (max 1 b₁*max 1 b₂)

end
end OAI.SevenEighths.Cycle63FinalCapacity

end Record1252270103Bootstrap.PR67
