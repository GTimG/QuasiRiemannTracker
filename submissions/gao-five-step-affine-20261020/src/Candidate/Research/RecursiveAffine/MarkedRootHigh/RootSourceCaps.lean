/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.MarkedRootHigh.BindingLemmas
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainLowPayment
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RootHigh
open Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
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
open Cycle63Moment LocalMoment
open CenteredMomentSecondInputCapacitySource
open CenteredMomentChildRows CenteredMomentSecondCanonical CenteredMomentSecondEnergySplit
open CenteredMomentNaturalRowSource
open Cycle63InitialSource
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable [L : Cycle63.AffineLedger]
set_option linter.defProp false in
/-- Literal physical source gates with the caller's affine ledger. -/
def GeometryAffineMainLowSourceSpec
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Cs Z : ℝ) : Prop :=
  ∀(θ : α→RayQuotient.Characters M H)(η₀ : Character)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (tplain X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
    (∀i,0≤w i) → Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) tplain X₁ X₂ hX₁ hX₂
    GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z

/-- Only the card field uses the ambient cap in the saved affine source record. -/
theorem geometry_affine_source_gates_actual_card {ι : Type*} [Fintype ι]
    (s : Input ι)(p : Profiles (1/4) (9/4))(N : ℕ)(Cs Z : ℝ)
    (caps : GeometryAffineExceptionalSourceGates s p N Cs Z) :
    GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z where
  card := le_rfl
  controls := caps.controls
  lower := caps.lower
  lo := caps.lo
  hi := caps.hi
  endpoints := caps.endpoints
  scales := caps.scales
  profile₁ := caps.profile₁
  profile₂ := caps.profile₂
  zero₁ := caps.zero₁
  zero₂ := caps.zero₂
  support₁ := caps.support₁
  support₂ := caps.support₂
  volume := caps.volume
  volumeLog := caps.volumeLog
  sourcePositive := caps.sourcePositive
  sourceCap := caps.sourceCap
  poolCap := caps.poolCap
  plain₁ := caps.plain₁
  plain₂ := caps.plain₂
  plain₃ := caps.plain₃
  plain₄ := caps.plain₄


end
end OAI.SevenEighths.Cycle153RootHigh
