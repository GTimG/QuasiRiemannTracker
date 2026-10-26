/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalChain

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153CanonicalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open ActualEisensteinCubic ConcretePrimeRowBridge LocalMoment
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonPairedSource CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonLinearNormalization CenteredMomentEnergyBands
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSourceLiveColumn CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyState
open CenteredMomentNaturalFixedRaySource CenteredMomentSourceInputReindex
open Cycle63Moment Cycle63Moment.LowBranch Cycle63FinalLow Cycle63FinalNatural Cycle63InitialMass
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The actual frozen native geometry constructors provide the canonical
source frame. The slot equivalence is literally the identity; no physical
source label or counting coordinate is added. -/
def actual_canonical_source_frame
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp xi reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
    (firstIndex : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (secondIndex : GeometryLowSecondIndex reflected s R seed Z Mrow amp xi reserve b t N hZ key firstIndex)
    (second : Bool) :
    let datum := geometryLowSecondDatum reflected s R seed Z Mrow amp xi reserve b t N hZ key
      firstIndex hz1 hz2 secondIndex
    let childSrc := geometryLowFirstChild reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t firstIndex
    let firstIdeal := geometryColumnIdeal reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstIndex.1.val
    ∀(B₂ : actualAllocations childSrc.pools (if second then datum.D else datum.C))
      (rwitness : secondLiveRows (fun _:Unit=>datum.block))
      (hf₁ : frozenCoefficient firstIndex.2.val firstIdeal R s.ν s.W s.P≠0)
      (hf₂ : frozenCoefficient B₂.val (if second then datum.D else datum.C) datum.R
        childSrc.ν childSrc.W childSrc.P≠0),
    let chain := geometryLowActualChain reflected s R seed Z Mrow amp xi reserve b t N hZ key
      firstIndex hz1 hz2 secondIndex second B₂
    let geom := geometryLowActualGeometry reflected s R seed Z Mrow amp xi reserve b t N hZ key
      firstIndex hz1 hz2 secondIndex second B₂ rwitness hf₁ hf₂
    CanonicalSourceFrame s chain geom datum second := by
  intro datum childSrc firstIdeal B₂ rwitness hf₁ hf₂ chain geom
  exact {slots:=Equiv.refl _, first_eq:=rfl, datum_eq:=rfl, puncture_eq:=rfl, own_eq:=rfl}

end
end OAI.SevenEighths.Cycle153CanonicalLow
#print axioms OAI.SevenEighths.Cycle153CanonicalLow.actual_canonical_source_frame
