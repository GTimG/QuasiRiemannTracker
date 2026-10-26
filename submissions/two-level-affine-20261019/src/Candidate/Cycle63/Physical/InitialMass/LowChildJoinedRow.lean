/- The row facts of the joined bound of the selected low columns: the norm of the own second ideal of a label, and the
exponent of the weight of a returned row read from the coordinates of the row. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.LowChildSelectedFacts
import Candidate.Cycle63.Physical.InitialMass.LowChildJoinedTotal

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle63FinalNatural Cycle63Moment.LowBranch
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

/-- The norm of the own second ideal of a supported label is positive. -/
theorem second_norm_pos (second : Bool) {l : FirstSourceLabel} (hC : Supported l.1.1) (hD : Supported l.1.2) :
    (0 : ℝ) < ((if second then l.1.2 else l.1.1).absNorm : ℝ) := by
  cases second
  · exact CenteredMomentFirstScale.norm_pos l.1.1 hC.1
  · exact CenteredMomentFirstScale.norm_pos l.1.2 hD.1

/-- The norm of the own second ideal of a label is at most `x` when the norms of both ideals of the label are. -/
theorem second_norm_le (second : Bool) {l : FirstSourceLabel} {x : ℝ} (hC : (l.1.1.absNorm : ℝ) ≤ x)
    (hD : (l.1.2.absNorm : ℝ) ≤ x) : ((if second then l.1.2 else l.1.1).absNorm : ℝ) ≤ x := by
  cases second
  · exact hC
  · exact hD

/-- The exponent of the weight of a returned row, from the coordinates of the row: the exponent of the old payment of
the row (the exponent `lowGeometryExponent` of its first label, the error `errorBase = common + pad`, the nominal width
of its second label and the common part `common` of the exponents) divided by the norm of its own second ideal, times
the factor of the returned part, is the exponent `E₀` of the target plus the first coordinate of the row. -/
theorem returned_row_exponent (reflected second left : Bool) (l lab : FirstSourceLabel)
    (Z Mrow A amp ξ reserve ε unit errorBase common pad loss εv BN εshell dcard qdel E₀ a Xold : ℝ)
    (ha : a = lowGeometryExponent reflected Z A l + errorBase + (unit - Mrow) + εv + BN * εshell)
    (hXold : Xold = secondNominal unit Z amp (frequencyLoss Z 32 ξ + reserve)
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2) lab.1.1 lab.1.2 lab.2.val +
      amp + common)
    (herr : errorBase = common + pad) (hE₀ : E₀ = loss + amp + εv + BN * εshell + pad + dcard) :
    loss + amp + a - Xold - Real.logb Z ((if second then lab.1.2 else lab.1.1).absNorm : ℝ) + (dcard + qdel) =
      E₀ + actualHighCoordinates reflected left second l lab.1.1 lab.1.2 lab.2.val Z Mrow A amp ξ reserve ε 0 +
        qdel := by
  have h := max_sub_swap (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm : ℝ))
    (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm : ℝ))
  rw [ha, hXold, herr, hE₀]
  simp only [lowGeometryExponent, secondNominal, actualHighCoordinates, Matrix.cons_val_zero]
  linarith only [h]

end
end OAI.SevenEighths.Cycle63InitialMass
