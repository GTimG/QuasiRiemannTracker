/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.ChainProduct

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option quotPrecheck false

namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic ConcreteTraceCRT
open ConcretePrimeRowBridge
open Cycle61FinalLow CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentRetainedEnergy CenteredMomentAllocatedRayDictionary
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredExceptionalProfile
open CenteredMomentDetectorEnergyInitialState Cycle61InitialMass
local notation "O" => HeckeFamily.O

section Actual
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (reflected : Bool) (η₀ : Character) (u₀ : O)
  (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) (hu₀ : u₀ ≠ 0)
  (s : Input α) (R seed : Ideal O)
  (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1 < Z) (bin : ℤ × (Fin 5 → ℤ))
  (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
  (hw₁ : s.W₁ 0 = 0) (hw₂ : s.W₂ 0 = 0)
  (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q)
local notation "datum" => geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
local notation "Kpos" => (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow)
local notation "firstLabel" => geometryFirstLabel s R seed (Z^Mrow) Z ξ Kpos bin q.1.val
local notation "unitMap" => (fun l => (firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l : O))
local notation "baseRay" => geometryDictionaryRay reflected s R seed (Z^Mrow) Z ξ Kpos bin q.1.val

local notation "rawKey" => geometryLowRawKey reflected η₀ u₀ F₀ R₀ hu₀ s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n

/-- The literal two-allocation chain attached to the actual second datum. -/
def geometryLowChain (second : Bool)
    (B₂ : actualAllocations (datum).input.pools (if second then (datum).D else (datum).C)) : Chain s where
  C₁ := geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ Kpos bin q.1.val
  R₁ := R
  B₁ := q.2
  η₁ := geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ Kpos bin q.1.val
  t₁ := t
  E₂ := if second then (datum).D else (datum).C
  R₂ := (datum).R
  B₂ := B₂

/-- Actual physical residual-allocation rows inherit one original slot set
and one common profile pair. The moving common mask is derived from the
geometry constructor; no dictionary equality is assumed. -/
theorem actual_geometry_chain_common_profile
    (hη : s.η=excluded F₀.character R₀) (hR : R≠0)
    (rayModulus : Ideal O) [NeZero rayModulus]
    (Hray : Subgroup (O⧸rayModulus)ˣ)
    (hH : RayOrthogonality.globalUnits rayModulus≤Hray)
    (θ : α→RayQuotient.Characters rayModulus Hray) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot : ℝ)
    (hm : Matches rayModulus Hray hH s η₀ θ w σ freq W bslot Z)
    (ap bp : ℝ) (hap : 0<ap) (p : Profiles ap bp)
    (hp₁ : s.W₁=p.profile 0) (hp₂ : s.W₂=p.profile 1)
    (r : secondLiveRows (fun _ : Unit=>(datum).block)) (second rectangle : Bool)
    (ψ : RayCharacter) (v : ℝ)
    (B₂ : actualAllocations (datum).input.pools (if second then (datum).D else (datum).C))
    (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2))) :
    let chain:=geometryLowChain reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n second B₂
    let src:=chain.final ((datum).τ ψ) v
    let J:=chain.indices L alloc
    let X₁:=Cycle61.Physical.sourcePlainScales src.toSource rectangle 0/(selectedPlain L alloc 0).absNorm
    let X₂:=Cycle61.Physical.sourcePlainScales src.toSource rectangle 1/(selectedPlain L alloc 1).absNorm
    let key:=rawKey r second
    let Fraw:=naturalRow (secondFixedDictionary η₀ (baseRay,ψ))
      (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property
    let mask:=geometryRawFixedMask s R*firstSourceMissing (!reflected) firstLabel
    ‖Cycle61.Physical.sourcePositiveRow src.toSource rectangle L alloc
        (if second then -r.val.2.2.2.val else r.val.2.2.2.val)‖^2 ≤
      ‖HeckeDyadic.polynomial (excluded Fraw.character mask) false
          (CenteredMomentLattice.normPowerProfile (p.profile 0) ap bp hap (p.support 0)
            ((p.profile 0).smooth ⊤) v) X₁ 0 0*
        HeckeDyadic.polynomial (excluded Fraw.character mask) false
          (CenteredMomentLattice.normPowerProfile (p.profile 1) ap bp hap (p.support 1)
            ((p.profile 1).smooth ⊤) v) X₂ 0 0*
        ∏i:J,CenteredMomentCommonMaskExpansion.naturalSlot (excluded Fraw.character mask)
          (primePool rayModulus Hray bslot (Z^(w i)))
          (CenteredMomentCommonMaskEnergy.heightCoefficient
            (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
              HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) v) (Z^(w i))‖^2 := by
  intro chain src J X₁ X₂ key Fraw mask
  have hrow := actual_chain_positive_row_original rayModulus Hray hH s η₀ θ w σ freq
    W bslot Z hm chain ((datum).τ ψ) v rectangle L alloc
      (if second then -r.val.2.2.2.val else r.val.2.2.2.val)
  change Cycle61.Physical.sourcePositiveRow src.toSource rectangle L alloc
      (if second then -r.val.2.2.2.val else r.val.2.2.2.val)=_ at hrow
  rw [hrow,hp₁,hp₂]
  have hnorm (j : Fin 2) : (0:ℝ)<(selectedPlain L alloc j).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ alloc (Sum.inr j)))
  have hX (j : Fin 2) : 0<Cycle61.Physical.sourcePlainScales src.toSource rectangle j := by
    cases rectangle <;> fin_cases j
    · exact src.X₁_pos
    · exact src.X₂_pos
    · exact src.Y₁_pos
    · exact src.Y₂_pos
  exact actual_geometry_low_retained_common_profile reflected η₀ u₀ F₀ R₀ hu₀ s R seed
    Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n hη hR r second ψ
    (p.profile 0) (p.profile 1) ap bp hap (p.support 0) (p.support 1)
    (fun i:J=>primePool rayModulus Hray bslot (Z^(w i)))
    (fun (i:J) I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
    (fun i:J=>Z^(w i)) (fun _=>Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    v X₁ X₂ (div_pos (hX 0) (hnorm 0)) (div_pos (hX 1) (hnorm 1))

end Actual
end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.actual_geometry_chain_common_profile
