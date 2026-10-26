/- The literal ROOT selected row returns the SAME physical source/output.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootSelectedPhysicalRaw
import Candidate.Research.RecursiveAffine.NativeSelectedOldActual
import Candidate.Research.RecursiveAffine.NativeSelectedOldLedgerPrice
import Candidate.Research.RecursiveAffine.NativeRootPhysicalThreshold
import Candidate.Research.RecursiveAffine.NativePhysicalPoolAliases
import Candidate.Research.RecursiveAffine.NativeSourceSide
import Candidate.Research.RecursiveAffine.NativeRootPaidRowsResidual
import Candidate.Research.RecursiveAffine.NativeRootAnalyticFee
import Candidate.Research.RecursiveAffine.NativeRawOldExponent
import Candidate.Research.RecursiveAffine.NativeRootResidualNormalization
import Candidate.Research.RecursiveAffine.NativeRootPaidRowsReceiptWithLoss
import Candidate.Research.RecursiveAffine.NativeRootSelectedPaidGateAtBin
import Candidate.Research.RecursiveAffine.NativeRootSelectedFamilyPrefix

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily CanonicalQuadraticSieve
open CenteredMomentNaturalFixedRaySource CenteredMomentAllocatedRayDictionary
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentEnergyBands CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity
open LocalMoment ConcretePrimeRowBridge CenteredMomentSecondHeightFamily Cycle153CanonicalLow
open Cycle153Reachable Cycle153RegionalLow Cycle153ContinuationUnit Cycle153SourceSchedule Cycle153SourceUniform
open Cycle153HighProvider Cycle153ReachableGeometry Cycle153AnalyticPrimitive Cycle153.RegionalSchedule
open CenteredMomentFirstDiscardedEnergy CenteredMomentOriginalCommonHarmonic CenteredMomentNaturalRowSource
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M ≤ H)
noncomputable local instance rootAnalyticReturnConstantLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
open CenteredMomentEnergyState CenteredMomentFirstAmplificationChoice
open Cycle153RootStep Cycle153JointCount Cycle153ActualRootSourceGates Cycle153ActualSourceGates
open CenteredMomentSecondCanonicalScalar CenteredMomentCommonPairedSource
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSecondEnergySplit
open CenteredMomentSecondInputCapacitySource
attribute [local irreducible] NativeColumnOutputTrace nodeOfNativeContinuation
private theorem actual_root_column_constant_nonneg
    (n : ℕ)(Cs Cpay Kterminal Kchild Kcol Cdirect C0 C1 Kdirect : ℝ)
    (hCs : 1≤Cs)(hCpay : 1≤Cpay)(hCdirect : 1≤Cdirect)
    (hKt : 0≤Kterminal)(hchild : 0≤Kchild)(hKcol : 0≤Kcol)
    (hC0 : 0≤C0)(hC1 : 0≤C1)(hKdirect : 0≤Kdirect) :
    0≤nativeColumnSourceConstant n Cs Cpay Kterminal Kchild Kcol Cdirect C0 C1 Kdirect:=by
  have hdiag:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
  have hcs0:=zero_le_one.trans hCs
  have hcp0:=zero_le_one.trans hCpay
  have hcd0:=zero_le_one.trans hCdirect
  unfold nativeColumnSourceConstant
  exact mul_nonneg (mul_nonneg (by positivity) hdiag)
    (add_nonneg (mul_nonneg (mul_nonneg hKcol (pow_nonneg hcp0 _)) (add_nonneg hKt hchild))
      (mul_nonneg (mul_nonneg hKdirect (pow_nonneg hcd0 _)) (add_nonneg hC0 hC1)))

attribute [local irreducible] nativeSharedColumnFixed nativeColumnSourceConstant
attribute [local irreducible] actualRootSelectedRowsPaidVector

/-- This literal return coefficient is fixed before the source base,
heights, bin, masks, selected rows or returned forest. -/
def actualRootAnalyticReturnCoefficient (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ)(e : ℝ)
    (Cs Cpay Kterminal Kchild Kcol Cdirect C0 C1 Kdirect : ℝ)(D : ℕ) : ℝ:=
  ((1/lowerFactor Nrow 1 (1/4))*
    ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(Fintype.card (BufferIndex e):ℝ)))*2*
    actualRootPhysicalConstant (alpha:=alpha) hH Bnorm hB budget Nrow*
    nativeColumnSourceConstant Nrow Cs Cpay Kterminal Kchild Kcol Cdirect C0 C1 Kdirect*
    (2+4*Real.pi)^D

theorem actualRootAnalyticReturnCoefficient_nonneg (Bnorm : ℝ)(hB : 0≤Bnorm)(budget Nrow : ℕ)(e : ℝ)
    (Cs Cpay Kterminal Kchild Kcol Cdirect C0 C1 Kdirect : ℝ)(D : ℕ)
    (hCs : 1≤Cs)(hCpay : 1≤Cpay)(hCdirect : 1≤Cdirect)(hKt : 0≤Kterminal)(hchild : 0≤Kchild)
    (hKcol : 0≤Kcol)(hC0 : 0≤C0)(hC1 : 0≤C1)(hKdirect : 0≤Kdirect) :
    0≤actualRootAnalyticReturnCoefficient (alpha:=alpha) hH Bnorm hB budget Nrow e Cs Cpay Kterminal Kchild Kcol Cdirect C0 C1 Kdirect D:=by
  have hCg:=actual_root_column_constant_nonneg Nrow Cs Cpay Kterminal Kchild Kcol Cdirect C0 C1 Kdirect
    hCs hCpay hCdirect hKt hchild hKcol hC0 hC1 hKdirect
  have hCu:=(actualRootPhysicalConstant_pos (alpha:=alpha) hH Bnorm hB budget Nrow).le
  have hlow:=(lowerFactor_pos Nrow 1 (1/4) (by norm_num) (by norm_num)).le
  dsimp only [actualRootAnalyticReturnCoefficient]
  positivity
end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualRootAnalyticReturnCoefficient_nonneg
