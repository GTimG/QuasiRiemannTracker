/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Raw.DaughterData
import Submissions.hailey_collet_1252270103.Record12518109Raw.FixedParentChain

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentNaturalRowSource CenteredMomentChildRows CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentAllocatedRayDictionary CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

section Actual
variable {α : Type*}[Fintype α][DecidableEq α]
variable (reflected second : Bool)(s : Input α)(R seed : Ideal O)
  (Z Mrow amp ξ reserve b t : ℝ)(N : ℕ)(hZ : 1<Z)(bin : ℤ×(Fin 5→ℤ))
  (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
  (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
  (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q)
local notation "datum" => geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
local notation "Kpos" => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
local notation "firstLabel" => geometryFirstLabel s R seed (Z^Mrow) Z ξ Kpos bin q.1.val
local notation "baseRay" => geometryDictionaryRay reflected s R seed (Z^Mrow) Z ξ Kpos bin q.1.val
variable (d : PhysicalDaughter
  (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n) second)

def daughterChain : Cycle61FinalLow.Chain s :=
  geometryLowChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second d.common


def daughterSlotSet : Finset α :=
  (daughterChain reflected second s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n d).indices
    d.projector d.residual

def daughterRawKey :=
  fixedParentRawKey reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n d.row second

local notation "chain" => daughterChain reflected second s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n d
local notation "rawKey" => daughterRawKey reflected second s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n d
local notation "slots" => daughterSlotSet reflected second s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n d

theorem daughter_value_eq (ψ : RayCharacter)(v : ℝ) :
    d.value ψ v=Cycle61.Physical.sourcePositiveRow ((chain).final ((datum).τ ψ) v).toSource
      d.rectangle d.projector d.residual
      (if second then -d.row.val.2.2.2.val else d.row.val.2.2.2.val) := rfl

theorem daughter_scale_eq (ψ : RayCharacter)(v : ℝ)(j : Fin 2) :
    d.scale j=Cycle61.Physical.sourcePlainScales ((chain).final ((datum).τ ψ) v).toSource
      d.rectangle j/(selectedPlain d.projector d.residual j).absNorm := by
  dsimp only [PhysicalDaughter.scale]
  cases h:d.rectangle <;> fin_cases j <;> rfl

theorem daughter_first_eq : (rawKey).val.1=firstLabel := by cases second <;> rfl

theorem daughter_supported :
    Supported (rawKey).val.1.1.1 ∧ Supported (rawKey).val.1.1.2 ∧
    Supported (rawKey).val.2.1.1 ∧ Supported (rawKey).val.2.1.2 ∧
    CompletedGauss.primeSupport (rawKey).val.1.1.1=CompletedGauss.primeSupport (rawKey).val.1.1.2 ∧
    CompletedGauss.primeSupport (rawKey).val.2.1.1=CompletedGauss.primeSupport (rawKey).val.2.1.2 := by
  let src:=geometryFirstSource s R seed (Z^Mrow) Z ξ Kpos bin q.1.val.1
  cases second <;> exact ⟨src.hC,src.hD,(datum).hC,(datum).hD,src.sameSupport,(datum).sameSupport⟩

/-- Actual positive daughter to its canonical raw-row common-profile product.
The parent and relative slot characters are independent. -/
theorem daughter_value_le_common
    (hR : R≠0)(η₀ : Character)
    (rayModulus : Ideal O)[NeZero rayModulus](Hray : Subgroup (O⧸rayModulus)ˣ)
    (hH : RayOrthogonality.globalUnits rayModulus≤Hray)
    (θ : α→RayQuotient.Characters rayModulus Hray)(w σ freq : α→ℝ)
    (W : ℝ→ℂ)(bslot : ℝ)(hm : Matches rayModulus Hray hH s η₀ θ w σ freq W bslot Z)
    (ap bp : ℝ)(hap : 0<ap)(p : Profiles ap bp)(hp₁ : s.W₁=p.profile 0)(hp₂ : s.W₂=p.profile 1)
    (ψ : RayCharacter)(v : ℝ) :
    let Fraw:=naturalRow (secondFixedDictionary s.η (baseRay,ψ))
      (nonzeroJointSourceRow (rawKey)).val (nonzeroJointSourceRow (rawKey)).property
    let mask:=geometryRawFixedMask s R*firstSourceMissing (!reflected) firstLabel
    ‖d.value ψ v‖^2≤
      ‖HeckeDyadic.polynomial (excluded Fraw.character mask) false
          (CenteredMomentLattice.normPowerProfile (p.profile 0) ap bp hap (p.support 0)
            ((p.profile 0).smooth ⊤) v) (d.scale 0) 0 0*
        HeckeDyadic.polynomial (excluded Fraw.character mask) false
          (CenteredMomentLattice.normPowerProfile (p.profile 1) ap bp hap (p.support 1)
            ((p.profile 1).smooth ⊤) v) (d.scale 1) 0 0*
        ∏i∈(slots),CenteredMomentCommonMaskExpansion.naturalSlot (excluded Fraw.character mask)
          (primePool rayModulus Hray bslot (Z^(w i)))
          (CenteredMomentCommonMaskEnergy.heightCoefficient
            (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
              HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) v) (Z^(w i))‖^2 := by
  have hh:=actual_fixed_parent_chain_common_profile reflected s R seed Z Mrow amp ξ reserve b t N hZ bin
    q hw₁ hw₂ n hR η₀ rayModulus Hray hH θ w σ freq W bslot hm ap bp hap p hp₁ hp₂
    d.row second d.rectangle ψ v d.common d.projector d.residual
  rw [daughter_value_eq reflected second s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n d ψ v,
    daughter_scale_eq reflected second s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n d ψ v 0,
    daughter_scale_eq reflected second s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n d ψ v 1]
  dsimp only [daughterChain,daughterRawKey,daughterSlotSet]
  rw [←Finset.prod_coe_sort]
  exact hh

theorem daughter_ordinary_keep
    (hR : R≠0)(χ₀ ψ : RayCharacter)(Q : Ideal O)(hQ : Q≤Ideal.span {(72:O)})
    (m : O)(hm : m≠0)(hml : goodLambda∣m)(hm2 : (2:O)∣m)
    (hord : d.row.val.2.2.2.val∈CenteredMomentSecondEnergySplit.partRows false
      (datum).input.η χ₀ Q m (datum).C (datum).D (datum).inactive (datum).radius) :
    CenteredMomentDetectorEnergyInitialState.initialKeep (secondFixedDictionary s.η (baseRay,ψ)) Q
      (nonzeroJointSourceRow (rawKey)).val :=
  actual_fixed_parent_ordinary_keep reflected s R seed Z Mrow amp ξ reserve b t N hZ bin
    q hw₁ hw₂ n hR d.row second χ₀ ψ Q hQ m hm hml hm2 hord

end Actual
end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.daughter_value_le_common
#print axioms OAI.SevenEighths.Record12518109Raw.daughter_ordinary_keep
