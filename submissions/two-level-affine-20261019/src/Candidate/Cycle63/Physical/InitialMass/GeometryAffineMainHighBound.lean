/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainSelectedPartition
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineScheduleData
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowQuantitativePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainSelectedRowEmbedding
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceInternal

set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands
local instance affineMainHighBoundSumDecidable {α : Type} : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local irreducible] Finset.univ mainLowPhysicalCompleteCost

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance affineMainHighBoundFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger] in
/-- The high rows of the second transform at a parent `s` with first-stage puncture `R`, seed `seed` and radial scale
`Z^Mrow`, on the canonical selector of the shared schedule `g`, have normalized cost at most `CH` times the weight of the two
inner Mellin heights. -/
def GeometryAffineMainCanonicalHighBound
    (g : GeometryAffineLowSchedule) (η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (Z : ℝ) (hZ : 1<Z) (hT : 2<Z^g.τ) (ap bp : ℝ)
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (Mrow amp baseHeight : ℝ)
    (key : ℤ×(Fin 5→ℤ)) (Ψ : 𝓢(ℝ,ℂ)) (χ₀ : RayCharacter)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (CH : ℝ) (dh : ℕ) : Prop :=
  ∀(second : Bool)(t₀ u : ℝ),
    let hKfirst:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
    let rows:=firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z (g.μ/64) hKfirst key) (fun _=>logAnnulus)
    let ideal:=fun j : rows=>geometryColumnIdeal reflected s R seed (Z^Mrow) Z (g.μ/64) hKfirst key j.val
    let mass:=fun j : rows=>geometryFirstHighMass reflected s R seed Ψ Mrow Z (g.μ/64) g.δ hKfirst key j.val
    ∀{Label : Type}[Fintype Label](column : Label → rows),
      Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^Mrow) Z (g.μ/64) hKfirst key (column j).val,
        (column j).val.2.1.val)) →
    ∀alloc : (j : Label)→actualAllocations s.pools (ideal (column j)),
      (∀j,frozenCoefficient (alloc j).val (ideal (column j)) R s.ν s.W s.P≠0) →
    let firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (g.μ/64) hKfirst key:=
      fun j=>⟨column j,alloc j⟩
    let selected:=mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) bp
      baseHeight (Fintype.card α) hZ key hz₁ hz₂ firstIndex
    let raw:=fun r : selected=>mainLowSelectedDatum reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) bp
      baseHeight (Fintype.card α) hZ key hz₁ hz₂ firstIndex r
    let datum:=fun r : selected=>ordinarySecondDatum (raw r) χ₀ (internalQ Q η₀) fixedBadMask
    let coefficient:=fun r : selected=>mass (column r.val.1)/volume
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z (g.μ/64) hKfirst key baseHeight (firstIndex r.val.1))
    ∀(hP : ∀r,(raw r).R*(if second then (raw r).D else (raw r).C)≠0)
      (hPN : ∀r,((((raw r).R*(if second then (raw r).D else (raw r).C)).absNorm:ℝ))≤Z^(28:ℝ)),
    let canonical:=fun (r : selected)(χ ψ : RayCharacter)=>mainLowCanonicalSelector M H hH
      (raw r) χ₀ χ ψ (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero
      (dvd_mul_right _ _) (dvd_mul_left _ _) Z 28 hZ second (hP r) (hPN r) η₀
      (inf_le_left.trans hQM) inf_le_right g.e (Z^g.τ) g.e_pos hT hβlo hβhi
    (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(datum l).block)=>
      ((1+Cycle63.AffineLedger.q)/2)≤bufferValue g.e (mainPhysicalFamilySelector second datum canonical r)),
      (coefficient r.val.1*((datum r.val.1).K/lowerFactor (Fintype.card α) 1 ap)*
        normalizer (datum r.val.1).C (datum r.val.1).D (datum r.val.1).inactive)*
      highNormalizedRowCost second datum r
        ((datum r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((datum r.val.1).block.divisors.filter Squarefree))≤
      (CH*(1+‖t₀‖)^dh)*(1+‖u‖)^dh

end
end OAI.SevenEighths.Cycle63InitialMass
