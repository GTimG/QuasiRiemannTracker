/- The HIGH rows of all nonzero second-stage blocks of a parent at a first height, with their canonical selector, their
keys and their compensated coordinates, as named objects. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineHighPayment

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
attribute [local instance] geometryAffineHighPaymentSumDecidable

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

open CenteredMomentCommonPairedSource CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow FourierBridge

open CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
open CenteredMomentSecondInputCapacitySource

open Cycle63FinalNatural CenteredMomentSourceRow CenteredMomentSecondEnergySplit
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The ordinary second data of the nonzero second-stage blocks of a parent at the first height `t`. -/
abbrev affineHighOrdinary (reflected : Bool) (s : Input α) (R seed : Ideal O) (Z Mrow amp μ t : ℝ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (χ₀ : RayCharacter) (Q : Ideal O) (m : O) :
    geometryMainNonzeroBlocks reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t (Fintype.card α) hZ bin hz₁ hz₂ →
      SecondInputDatum α :=
  fun j=>ordinarySecondDatum (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j) χ₀ Q m

/-- The live rows of the nonzero second-stage blocks of a parent at the first height `t`. -/
abbrev AffineHighRows (reflected : Bool) (s : Input α) (R seed : Ideal O) (Z Mrow amp μ t : ℝ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (χ₀ : RayCharacter) (Q : Ideal O) (m : O) :=
  secondLiveRows (fun j=>(affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m j).block)

variable [Cycle63.AffineLedger] in
/-- The canonical selector on the live rows of the nonzero second-stage blocks of a parent at the first height `t`. -/
def affineHighUniversalSelector (η₀ : Character) (second : Bool) (reflected : Bool) (s : Input α) (R seed : Ideal O) (Z Mrow amp μ t : ℝ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (χ₀ : RayCharacter) (Q : Ideal O) (m : O)
    (hQ72 : Q≤Ideal.span {(72:O)}) (hm₀ : m≠0) (hml : goodLambda∣m) (hm₂ : (2:O)∣m) (hQM : Q≤M)
    (hQη : Q≤η₀.modulus) (e T : ℝ) (he : 0<e) (hT : 2<T) (hβlo : 51/100≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hP : ∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0)
    (hPN : ∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤Z^(28:ℝ)) :
    AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m→BufferIndex e :=
  mainPhysicalFamilySelector second (affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m)
    (fun j (χ ψ : RayCharacter)=>mainLowCanonicalSelector M H hH (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j) χ₀ χ ψ Q hQ72 m hm₀ hml hm₂
      Z 28 hZ second (hP j) (hPN j) η₀ hQM hQη e T he hT hβlo hβhi)

/-- The keys of the live rows of the nonzero second-stage blocks of a parent at the first height `t` in the dictionary
`(η₀, u₀, F₀, R₀)`, reflected for the second orientation. -/
def affineHighUniversalKey (η₀ : Character) (u₀ : O) (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) (hu₀ : u₀≠0)
    (second : Bool) (reflected : Bool) (s : Input α) (R seed : Ideal O) (Z Mrow amp μ t : ℝ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (χ₀ : RayCharacter) (Q : Ideal O) (m : O)
    (r : AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m) :
    NonzeroJointSourceLabel (!reflected) u₀ (fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)) :=
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  let ordinary:=affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m
  let first:=fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t (Fintype.card α) hZ
      bin hz₁ hz₂=>
    geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin j.val.1.1.val
  let unit:=fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
  let rawKey:=secondEncodedNonzeroRow (fun j=>(ordinary j).block) first r (!reflected) u₀ unit
    (geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val
      ordinary first r rfl)
  if second then reflectedNonzeroJointLabel rawKey else rawKey

/-- The compensated HIGH coordinates of the live rows of the nonzero second-stage blocks of a parent at the first height
`t`. -/
def affineHighUniversalCoordinates (second : Bool) (reflected : Bool) (s : Input α) (R seed : Ideal O) (Z Mrow amp μ t : ℝ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (χ₀ : RayCharacter) (Q : Ideal O) (m : O)
    (r : AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m) : Fin 4→ℝ :=
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  let ordinary:=affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m
  let A:=Real.logb Z (volume s.toData)
  compensatedHighCoordinates
    (childHighCoordinates (actualHighCoordinates reflected (!reflected) second
      (geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val) (ordinary r.val.1).C
      (ordinary r.val.1).D (ordinary r.val.1).inactive Z Mrow A amp (μ/64) (μ/8) (μ/8)) (μ/8))
    (geometryHighSide reflected A (geometryExponents s R seed (Z^Mrow) Z (μ/64) r.val.1.val.1.1.val.1.val))

variable [Cycle63.AffineLedger] in
/-- The HIGH rows of the nonzero second-stage blocks of a parent at the first height `t`: the live rows whose canonical
buffer bin is at least `(1 + qh)/2`. -/
def affineHighUniversalRows (η₀ : Character) (second : Bool) (reflected : Bool) (s : Input α) (R seed : Ideal O) (Z Mrow amp μ t : ℝ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (χ₀ : RayCharacter) (Q : Ideal O) (m : O)
    (hQ72 : Q≤Ideal.span {(72:O)}) (hm₀ : m≠0) (hml : goodLambda∣m) (hm₂ : (2:O)∣m) (hQM : Q≤M)
    (hQη : Q≤η₀.modulus) (e T : ℝ) (he : 0<e) (hT : 2<T) (hβlo : 51/100≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hP : ∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0)
    (hPN : ∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤Z^(28:ℝ)) (qh : ℝ) :
    Finset (AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m) :=
  Finset.univ.filter (fun r=>((1+qh)/2)≤bufferValue e (affineHighUniversalSelector M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m hQ72 hm₀ hml hm₂ hQM hQη e T he hT hβlo hβhi hP hPN r))

variable [Cycle63.AffineLedger] in
/-- The transport form of the HIGH rows of the nonzero second-stage blocks of a parent at the first height `t` is the sum
over the buffer bins of the binned counts of the named keys at the named coordinates. -/
theorem affineHighUniversalTransport_eq (η₀ : Character) (u₀ : O) (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O)
    (hu₀ : u₀≠0) (second : Bool) (reflected : Bool) (s : Input α) (R seed : Ideal O) (Z Mrow amp μ t : ℝ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (χ₀ : RayCharacter) (Q : Ideal O) (m : O)
    (hQ72 : Q≤Ideal.span {(72:O)}) (hm₀ : m≠0) (hml : goodLambda∣m) (hm₂ : (2:O)∣m) (hQM : Q≤M)
    (hQη : Q≤η₀.modulus) (e T : ℝ) (he : 0<e) (hT : 2<T) (hβlo : 51/100≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hP : ∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0)
    (hPN : ∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤Z^(28:ℝ)) (qh extra : ℝ) :
    affineHighUniversalTransport M H hH η₀ u₀ F₀ R₀ hu₀ reflected second s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
      Q hQ72 m hm₀ hml hm₂ hQM hQη e T he hT hβlo hβhi hP hPN qh extra=
    ∑q : BufferIndex e,keyBinnedCount
      ((affineHighUniversalRows M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m hQ72 hm₀ hml hm₂ hQM hQη e T he hT hβlo hβhi hP hPN qh).filter
        (fun r=>affineHighUniversalSelector M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m hQ72 hm₀ hml hm₂ hQM hQη e T he hT hβlo hβhi hP hPN r=q))
      (affineHighUniversalKey η₀ u₀ F₀ R₀ hu₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m)
      (affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m) (μ/32)
      (fun k=>Z^(exponentBinUpper (μ/32) k 0+(2*bufferValue e q-1)*exponentBinUpper (μ/32) k 3+extra)) :=
  rfl

/-- An exponent bin of coordinates in `[-B, B]` lies in the box of the bins of `[-B, B]`. -/
theorem exponentBin_mem_box (width B : ℝ) (hw : 0<width) (x : Fin 4→ℝ) (hx : ∀i,-B≤x i ∧ x i≤B) :
    exponentBin width x∈Fintype.piFinset (fun _ : Fin 4=>Finset.Icc (⌊-B/width⌋:ℤ) ⌊B/width⌋) :=
  Fintype.mem_piFinset.mpr fun i=>Finset.mem_Icc.mpr
    ⟨Int.floor_mono (div_le_div_of_nonneg_right (hx i).1 hw.le),
      Int.floor_mono (div_le_div_of_nonneg_right (hx i).2 hw.le)⟩

/-- The live rows of the nonzero second-stage blocks of a parent number at most a bound that does not depend on the
first height: the rows of every second-stage index at the height `0`. -/
theorem affine_high_rows_card (reflected : Bool) (s : Input α) (R seed : Ideal O) (Z Mrow amp μ : ℝ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (χ₀ : RayCharacter) (Q : Ideal O) (m : O) :
    ∃N : ℕ,∀t : ℝ,Fintype.card (AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m)≤N := by
  let rows₀ : GeometryMainSecondIndex reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) 0 (Fintype.card α) hZ bin→Finset O:=fun j=>
    (ordinarySecondDatum (geometryLowSecondDatum reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) 0 (Fintype.card α)
      hZ bin j.1 hz₁ hz₂ j.2) χ₀ Q m).rows
  refine ⟨Fintype.card ((j : GeometryMainSecondIndex reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) 0 (Fintype.card α) hZ bin)×RayCharacter×RayCharacter×↥(rows₀ j)),fun t=>?_⟩
  let emb : SecondRow (fun j=>(affineHighOrdinary reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m j).block)↪
      (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) 0 (Fintype.card α) hZ bin)×RayCharacter×RayCharacter×↥(rows₀ j):=
    Function.Embedding.sigmaMap ⟨fun j=>j.val,Subtype.val_injective⟩
      (fun _=>Function.Embedding.prodMap (Function.Embedding.refl _)
        (Function.Embedding.prodMap (Function.Embedding.refl _) (Function.Embedding.refl _)))
  exact (Fintype.card_le_of_embedding (Function.Embedding.subtype _)).trans (Fintype.card_le_of_embedding emb)

variable [Cycle63.AffineLedger] in
/-- Along the first heights the transport form of the HIGH rows of the nonzero second-stage blocks of a parent attains
its maximum, when the compensated coordinates of the live rows lie in `[-Bbox, Bbox]` at every first height. -/
theorem affine_high_transport_max (η₀ : Character) (u₀ : O) (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) (hu₀ : u₀≠0)
    (second : Bool) (reflected : Bool) (s : Input α) (R seed : Ideal O) (Z Mrow amp μ : ℝ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (χ₀ : RayCharacter) (Q : Ideal O) (m : O)
    (hQ72 : Q≤Ideal.span {(72:O)}) (hm₀ : m≠0) (hml : goodLambda∣m) (hm₂ : (2:O)∣m) (hQM : Q≤M)
    (hQη : Q≤η₀.modulus) (e T : ℝ) (he : 0<e) (hT : 2<T) (hβlo : 51/100≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hP : ∀t j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0)
    (hPN : ∀t j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤Z^(28:ℝ)) (qh extra Bbox : ℝ) (hμ : 0<μ)
    (hbox : ∀t,∀r : AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m,
      ∀i,-Bbox≤affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m r i ∧
        affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m r i≤Bbox) :
    ∃t₀ : ℝ,∀t : ℝ,
      affineHighUniversalTransport M H hH η₀ u₀ F₀ R₀ hu₀ reflected second s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
        Q hQ72 m hm₀ hml hm₂ hQM hQη e T he hT hβlo hβhi (hP t) (hPN t) qh extra≤
      affineHighUniversalTransport M H hH η₀ u₀ F₀ R₀ hu₀ reflected second s R seed Z Mrow amp μ t₀ hZ bin hz₁ hz₂ χ₀
        Q hQ72 m hm₀ hml hm₂ hQM hQη e T he hT hβlo hβhi (hP t₀) (hPN t₀) qh extra := by
  obtain ⟨N,hN⟩:=affine_high_rows_card reflected s R seed Z Mrow amp μ hZ bin hz₁ hz₂ χ₀ Q m
  have hw : 0<μ/32:=by positivity
  have hcard (t : ℝ) : (affineHighUniversalRows M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m hQ72 hm₀ hml hm₂ hQM hQη e T he hT hβlo hβhi (hP t) (hPN t) qh).card≤N:=
    (Finset.card_le_univ _).trans (hN t)
  have hbin (t : ℝ) (r : AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m) :
      exponentBin (μ/32) (affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m r)∈
        Fintype.piFinset (fun _ : Fin 4=>Finset.Icc (⌊-Bbox/(μ/32)⌋:ℤ) ⌊Bbox/(μ/32)⌋):=
    exponentBin_mem_box (μ/32) Bbox hw _ (hbox t r)
  exact exists_max_key_transport (I:=ℝ) (fun t=>AffineHighRows reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m)
    (fun t=>affineHighUniversalRows M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m hQ72 hm₀ hml hm₂ hQM hQη e T he hT hβlo hβhi (hP t) (hPN t) qh)
    (fun t=>affineHighUniversalSelector M H hH η₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m hQ72 hm₀ hml hm₂ hQM hQη e T he hT hβlo hβhi (hP t) (hPN t))
    (fun t=>affineHighUniversalKey η₀ u₀ F₀ R₀ hu₀ second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m)
    (fun t=>affineHighUniversalCoordinates second reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀ Q m) (μ/32)
    (fun q k=>Z^(exponentBinUpper (μ/32) k 0+(2*bufferValue e q-1)*exponentBinUpper (μ/32) k 3+extra))
    (Fintype.piFinset (fun _ : Fin 4=>Finset.Icc (⌊-Bbox/(μ/32)⌋:ℤ) ⌊Bbox/(μ/32)⌋)) N hbin hcard

end
end OAI.SevenEighths.Cycle63InitialMass
