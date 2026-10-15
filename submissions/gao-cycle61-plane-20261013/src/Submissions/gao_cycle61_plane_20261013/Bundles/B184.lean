/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B164
import Submissions.gao_cycle61_plane_20261013.Bundles.B178
import Submissions.gao_cycle61_plane_20261013.Bundles.B180
import Submissions.gao_cycle61_plane_20261013.Bundles.B181
import Submissions.gao_cycle61_plane_20261013.Bundles.B183

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineHighSelectedTransport; sha256 e54f99b9b6b541c6fb80cdab0e93fd73f1f2361d6ea2d69d8f79bd610e0d6811 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                
                                                                    

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedRows
open CenteredMomentSecondRetainedAggregate
open CenteredMomentFirstSourceReduction Cycle61Moment
local notation "O" => HeckeFamily.O

attribute [local irreducible] Finset.univ
section ActualCharacter
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance affineHighSelectedSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z D amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z)
variable (bin : ℤ×(Fin 5→ℤ)) (hs₁ : s.W₁ 0=0) (hs₂ : s.W₂ 0=0)
variable (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin)
local notation "Selected" => mainLowSelectedNonzeroRows reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂ firstIndex
local notation "Original" => geometryMainNonzeroBlocks reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂
local notation "embed" => mainLowSelectedOriginal reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂ firstIndex

/-- Extend the selected inducing ray to the full ORIGINAL nonzero family.
The value off the image is only a total-function default. -/
def affineHighSelectedOriginalCharacter (χ₀ : Selected→ RayCharacter) : Original→ RayCharacter :=
  Function.extend embed χ₀ (fun _=>1)

variable (hinj : Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^D) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin (firstIndex l).1.val,
  (firstIndex l).1.val.2.1.val)))

include hinj in
theorem affine_high_selected_original_character_apply (χ₀ : Selected→ RayCharacter) (q : Selected) :
    affineHighSelectedOriginalCharacter reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂
      firstIndex χ₀ (embed q)=χ₀ q := by
  exact (main_low_selected_original_injective reflected s R seed Z D amp ξ reserve b t N hZ
    bin hs₁ hs₂ firstIndex hinj).extend_apply χ₀ (fun _=>1) q

/-- The pullback is used as the selected ordinary family, so its row lift
has no dependent casts. The next theorem identifies the literal selected datum. -/
def affineHighSelectedOriginalDatum (χ₀ : Selected→ RayCharacter) (Q : Ideal O) (m : O)
    (q : Original) : SecondInputDatum α :=
  geometryMainOrdinaryDatum reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂
    (affineHighSelectedOriginalCharacter reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂
      firstIndex χ₀ q) Q m q.val

include hinj in
theorem affine_high_selected_original_datum_apply (χ₀ : Selected→ RayCharacter)
    (Q : Ideal O) (m : O) (q : Selected) :
    affineHighSelectedOriginalDatum reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂
      firstIndex χ₀ Q m (embed q)=
    ordinarySecondDatum
      (mainLowSelectedDatum reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂ firstIndex q)
      (χ₀ q) Q m := by
  unfold affineHighSelectedOriginalDatum
  rw [affine_high_selected_original_character_apply reflected s R seed Z D amp ξ reserve b t N
    hZ bin hs₁ hs₂ firstIndex hinj χ₀ q]
  exact main_low_selected_original_ordinary_datum reflected s R seed Z D amp ξ reserve b t N hZ
    bin hs₁ hs₂ firstIndex (χ₀ q) Q m q

include hinj in
theorem affine_high_selected_ordinary_family_eq (χ₀ : Selected→ RayCharacter) (Q : Ideal O) (m : O) :
    (fun q : Selected=>affineHighSelectedOriginalDatum reflected s R seed Z D amp ξ reserve b t N hZ
      bin hs₁ hs₂ firstIndex χ₀ Q m (embed q))=
    (fun q : Selected=>ordinarySecondDatum
      (mainLowSelectedDatum reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂ firstIndex q)
      (χ₀ q) Q m) := by
  funext q
  exact affine_high_selected_original_datum_apply reflected s R seed Z D amp ξ reserve b t N hZ
    bin hs₁ hs₂ firstIndex hinj χ₀ Q m q

/-- Physical first mass and child volume pull back exactly; neither is
replaced by an arithmetic-label count. -/
theorem affine_high_selected_first_coefficient (χ₀ : Selected→ RayCharacter) (Q : Ideal O) (m : O)
    (mass : GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin→ℝ) (q : Selected) :
    mass (embed q).val.1 /
        volume (affineHighSelectedOriginalDatum reflected s R seed Z D amp ξ reserve b t N hZ
          bin hs₁ hs₂ firstIndex χ₀ Q m (embed q)).input=
    mass (firstIndex q.val.1) /
        volume (geometryLowFirstChild reflected s R seed (Z^D) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin t (firstIndex q.val.1)) := rfl
end ActualCharacter

section LiveRows
variable {α Selected Original : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Selected] [Fintype Original]
variable (datum : Original→ SecondInputDatum α) (embed : Selected→ Original)

/-- The selected ordinary live row lifts into the same original physical
row: its label changes by the injection and both rays and row stay literal. -/
theorem affine_high_selected_live_label
    (r : secondLiveRows (fun j=>(datum (embed j)).block)) :
    (highSelectedLiveRowEmbedding datum embed r).val.1=embed r.val.1 := rfl

theorem affine_high_selected_live_payload
    (r : secondLiveRows (fun j=>(datum (embed j)).block)) :
    (highSelectedLiveRowEmbedding datum embed r).val.2=r.val.2 := rfl

theorem affine_high_selected_live_injective (hinj : Function.Injective embed) :
    Function.Injective (highSelectedLiveRowEmbedding datum embed) := by
  intro r v h
  apply Subtype.ext
  exact high_selected_row_embedding_injective datum embed hinj (congrArg Subtype.val h)

/-- Every residual divisor and its physical cost are unchanged pointwise.
The coefficient may already contain first mass divided by child volume. -/
theorem affine_high_selected_live_physical_cost
    (N : ℕ) (a ap : ℝ) (second : Bool) (coefficient : Original→ℝ) (t u : ℝ)
    (r : secondLiveRows (fun j=>(datum (embed j)).block)) (L : Ideal O) :
    mainNormalizedPhysicalCost N a ap second (fun j=>datum (embed j))
      (fun j=>coefficient (embed j)) t u r.val L=
    mainNormalizedPhysicalCost N a ap second datum coefficient t u
      (highSelectedLiveRowEmbedding datum embed r).val L := rfl

theorem affine_high_selected_live_residuals
    (r : secondLiveRows (fun j=>(datum (embed j)).block)) :
    secondResidualIdeals (fun j=>(datum (embed j)).block) r.val=
      secondResidualIdeals (fun j=>(datum j).block)
        (highSelectedLiveRowEmbedding datum embed r).val := rfl

/-- A high theorem can use the selected carrier itself as its index type.
Its indexed cost is already the original-family cost, without an image fee. -/
theorem affine_high_selected_indexed_physical_cost
    (N : ℕ) (a ap : ℝ) (second : Bool) (coefficient : Original→ℝ) (t u : ℝ)
    (rows : Finset (secondLiveRows (fun j=>(datum (embed j)).block))) :
    (∑r∈rows,∑L∈secondResidualIdeals (fun j=>(datum (embed j)).block) r.val,
      mainNormalizedPhysicalCost N a ap second (fun j=>datum (embed j))
        (fun j=>coefficient (embed j)) t u r.val L)=
    ∑r∈rows,∑L∈secondResidualIdeals (fun j=>(datum j).block)
      (highSelectedLiveRowEmbedding datum embed r).val,
      mainNormalizedPhysicalCost N a ap second datum coefficient t u
        (highSelectedLiveRowEmbedding datum embed r).val L := rfl

/-- Nonzero joint-key evidence is proof irrelevant. The exact original
key, including either reflected side, agrees with the selected key. -/
theorem affine_high_selected_live_reflected_key (first : Original→ FirstSourceLabel)
    (r : secondLiveRows (fun j=>(datum (embed j)).block))
    (left second : Bool) (u₀ : O) (unit : FirstSourceLabel→ O)
    (hOriginal : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun j=>(datum j).block) first
        (highSelectedLiveRowEmbedding datum embed r))≠0)
    (hSelected : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun j=>(datum (embed j)).block) (fun j=>first (embed j)) r)≠0) :
    (if second then reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun j=>(datum j).block) first
        (highSelectedLiveRowEmbedding datum embed r) left u₀ unit hOriginal)
      else secondEncodedNonzeroRow (fun j=>(datum j).block) first
        (highSelectedLiveRowEmbedding datum embed r) left u₀ unit hOriginal)=
    (if second then reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun j=>(datum (embed j)).block) (fun j=>first (embed j)) r
        left u₀ unit hSelected)
      else secondEncodedNonzeroRow (fun j=>(datum (embed j)).block) (fun j=>first (embed j)) r
        left u₀ unit hSelected) := by
  have hk := high_selected_live_nonzero_key datum embed first r left u₀ unit hOriginal hSelected
  cases second with
  | false => exact hk
  | true => exact congrArg reflectedNonzeroJointLabel hk
end LiveRows

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_original_character_apply
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_original_datum_apply
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_ordinary_family_eq
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_first_coefficient
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_live_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_live_physical_cost
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_live_residuals
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_indexed_physical_cost
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_live_reflected_key

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineHighSelectedTransport -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineHighSelectedFiber; sha256 bccb82d601d880379452271d28209e0da4d273e7c3cb864ae9a141a116acc53c -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                       

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
local instance affineHighSelectedFiberSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := mainOrdinaryFiberSumDecidable

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

open CenteredMomentCommonPairedSource CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow FourierBridge

open CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
open CenteredMomentSecondInputCapacitySource


open Cycle61FinalNatural CenteredMomentSourceRow CenteredMomentSecondEnergySplit
open CenteredMomentSecondHeightFamily Cycle61Moment.LowBranch

attribute [local irreducible] Finset.univ SecondInputDatum.block

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- An injective lift preserves the exact finite fiber count. -/
theorem affine_high_selected_fiber_card_image
    {A B Key : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (embed : A→ B) (hinj : Function.Injective embed) (rows : Finset A)
    (key : B→ Key) (target : Key) :
    (Finset.univ.filter (fun r : rows=>key (embed r.val)=target)).card=
      (Finset.univ.filter (fun r : rows.image embed=>key r.val=target)).card := by
  classical
  apply Finset.card_bij (fun r _=>
    (⟨embed r.val,Finset.mem_image.mpr ⟨r.val,r.property,rfl⟩⟩ : rows.image embed))
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hr).2⟩
  · intro r hr v hv he
    apply Subtype.ext
    exact hinj (congrArg Subtype.val he)
  · intro v hv
    obtain ⟨r,hr,he⟩:=Finset.mem_image.mp v.property
    refine ⟨⟨r,hr⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · simpa only [he] using (Finset.mem_filter.mp hv).2
    · exact Subtype.ext he

theorem affine_high_selected_block_nonzero_of_datum_eq
    {α : Type*} [Fintype α] [DecidableEq α] (d e : SecondInputDatum α)
    (he : d=e) (hne : e.block.value ballProfile≠0) : d.block.value ballProfile≠0 :=
  he.symm ▸ hne

/-- Support passes to the lifted row image before geometry is substituted. -/
theorem affine_high_selected_image_original_nonzero
    {α Selected Original : Type*} [Fintype α] [DecidableEq α]
    [Fintype Selected] [Fintype Original]
    (raw ordinary : Original→ SecondInputDatum α) (embed : Selected→ Original)
    [DecidableEq (secondLiveRows (fun q=>(ordinary q).block))]
    (hn : ∀q,(raw (embed q)).block.value ballProfile≠0)
    (rows : Finset (secondLiveRows (fun q=>(ordinary (embed q)).block))) :
    ∀r∈rows.image (highSelectedLiveRowEmbedding ordinary embed),
      (raw r.val.1).block.value ballProfile≠0 := by
  intro r hr
  obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hr
  exact hn v.val.1

section Membership
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z D amp ξ reserve b t : ℝ) (hZ : 1< Z)
variable (bin : ℤ×(Fin 5→ℤ)) (hs₁ : s.W₁ 0=0) (hs₂ : s.W₂ 0=0)
variable (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin)
local notation "Selected" => mainLowSelectedNonzeroRows reflected s R seed Z D amp ξ reserve b t (Fintype.card α) hZ bin hs₁ hs₂ firstIndex
local notation "Original" => geometryMainNonzeroBlocks reflected s R seed Z D amp ξ reserve b t (Fintype.card α) hZ bin hs₁ hs₂
local notation "embed" => mainLowSelectedOriginal reflected s R seed Z D amp ξ reserve b t (Fintype.card α) hZ bin hs₁ hs₂ firstIndex

/-- The original full-block filter supplies physical nonzero evidence. -/
theorem affine_high_selected_original_block_nonzero (q : Selected) :
    (mainLowSelectedDatum reflected s R seed Z D amp ξ reserve b t (Fintype.card α)
      hZ bin hs₁ hs₂ firstIndex q).block.value ballProfile≠0 :=
  (Finset.mem_filter.mp (embed q).property).2.2

/-- Constant inducing data commute literally with the whole-original lift. -/
theorem affine_high_selected_constant_ordinary (χ₀ : RayCharacter) (Q : Ideal O) (m : O)
    (q : Selected) :
    geometryMainOrdinaryDatum reflected s R seed Z D amp ξ reserve b t (Fintype.card α)
      hZ bin hs₁ hs₂ χ₀ Q m (embed q).val=
    ordinarySecondDatum
      (mainLowSelectedDatum reflected s R seed Z D amp ξ reserve b t (Fintype.card α)
        hZ bin hs₁ hs₂ firstIndex q) χ₀ Q m := rfl

/-- Every lifted ordinary row remains in the original full-nonzero family. -/
theorem affine_high_selected_live_original_support (χ₀ : RayCharacter) (Q : Ideal O) (m : O)
    (r : secondLiveRows (fun q : Selected=>
      (geometryMainOrdinaryDatum reflected s R seed Z D amp ξ reserve b t (Fintype.card α)
        hZ bin hs₁ hs₂ χ₀ Q m (embed q).val).block)) :
    let datum:=fun q : Original=>geometryMainOrdinaryDatum reflected s R seed Z D amp ξ reserve b t
      (Fintype.card α) hZ bin hs₁ hs₂ χ₀ Q m q.val
    let lift:=highSelectedLiveRowEmbedding datum embed r
    lift.val.1.val∈geometryMainNonzeroBlocks reflected s R seed Z D amp ξ reserve b t
      (Fintype.card α) hZ bin hs₁ hs₂ ∧
    (geometryLowSecondDatum reflected s R seed Z D amp ξ reserve b t (Fintype.card α) hZ bin
      lift.val.1.val.1 hs₁ hs₂ lift.val.1.val.2).block.value ballProfile≠0 :=
  ⟨(embed r.val.1).property,(Finset.mem_filter.mp (embed r.val.1).property).2.2⟩
end Membership

/-- The Fourier count is literally card α; supported first allocations
supply the uniform fiber budget without an arithmetic label fee. -/
theorem eventually_affine_high_selected_ordinary_fibers
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    {α : Type} [Fintype α] [DecidableEq α]
    (b bs ε Amax Mmax ξ : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hε : 0<ε)
    (hA : 0≤ Amax)(hM : 0≤ Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃Cfiber : ℝ,0< Cfiber ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(D amp reserve t : ℝ),
      Squarefree seed → Endpoints b bs bs s →
      volume s≤ Z^Amax → Z^D≤ Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ amp → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin),
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^D) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin (firstIndex l).1.val)
        R s.ν s.W s.P≠0) →
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^D) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin (firstIndex l).1.val,
        (firstIndex l).1.val.2.1.val)) →
      let Selected:=mainLowSelectedNonzeroRows reflected s R seed Z D amp ξ reserve b t
        (Fintype.card α) hZ bin hs₁ hs₂ firstIndex
      let datum:=mainLowSelectedDatum reflected s R seed Z D amp ξ reserve b t
        (Fintype.card α) hZ bin hs₁ hs₂ firstIndex
      let first:=fun q : Selected=>geometryFirstLabel s R seed (Z^D) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin (firstIndex q.val.1).1.val
      let left:=!reflected
      let unit:=fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      ∀(χ₀ : RayCharacter)(Q : Ideal O)(m : O),
      let ordinary:=fun q=>ordinarySecondDatum (datum q) χ₀ Q m
      ∀(labels : Finset (secondLiveRows (fun q=>(ordinary q).block)))(second : Bool)
        (hf : ∀r : secondLiveRows (fun q=>(ordinary q).block),
          jointFirstFrequency left u₀ unit (secondEncodedRow (fun q=>(ordinary q).block) first r)≠0),
      ∀target : NonzeroJointSourceLabel left u₀ unit,
      ((Finset.univ.filter (fun r : labels=>
        (if second then reflectedNonzeroJointLabel
          (secondEncodedNonzeroRow (fun q=>(ordinary q).block) first r.val left u₀ unit (hf r.val))
        else secondEncodedNonzeroRow (fun q=>(ordinary q).block) first r.val left u₀ unit (hf r.val))=target)).card:ℝ)≤
          Cfiber*Z^(2*ε) := by
  let receipt:=eventually_actual_selected_main_ordinary_fibers
    η₀ u₀ F₀ R₀ hu₀ (Fintype.card α) b bs ε Amax Mmax ξ hb hbs hε hA hM hξ hξε
  let Cfiber:=Classical.choose receipt
  have hC:=(Classical.choose_spec receipt).1
  have hevent:=(Classical.choose_spec receipt).2
  refine ⟨Cfiber,hC,?_⟩
  filter_upwards [hevent] with Z he
  intro hZ Label _ reflected s R seed D amp reserve t hseed hend hV hKM
    hs₁ hs₂ hamp hr bin firstIndex hf₁ hinj Selected datum first left unit χ₀ Q m ordinary
    labels second hf target
  let Index:=(l : Label)×GeometryLowSecondIndex reflected s R seed Z D amp ξ reserve b t
    (Fintype.card α) hZ bin (firstIndex l)
  let raw:=fun q : Index=>geometryLowSecondDatum reflected s R seed Z D amp ξ reserve b t
    (Fintype.card α) hZ bin (firstIndex q.1) hs₁ hs₂ q.2
  let rawOrdinary:=fun q : Index=>ordinarySecondDatum (raw q) χ₀ Q m
  let rawFirst:=fun q : Index=>geometryFirstLabel s R seed (Z^D) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin (firstIndex q.1).1.val
  let lift:=highSelectedLiveRowEmbedding rawOrdinary (fun q : Selected=>q.val)
  let rows:=labels.image lift
  have hlift : Function.Injective lift:=affine_high_selected_live_injective rawOrdinary
    (fun q : Selected=>q.val) Subtype.val_injective
  have hn0 : ∀q : Selected,(raw q.val).block.value ballProfile≠0 := by
    intro q
    exact affine_high_selected_block_nonzero_of_datum_eq (raw q.val) (datum q) rfl
      (affine_high_selected_original_block_nonzero reflected s R seed Z D amp ξ reserve b t
        hZ bin hs₁ hs₂ firstIndex q)
  have hn : ∀r∈rows,(raw r.val.1).block.value ballProfile≠0 := by
    simpa only [rows,lift] using
      affine_high_selected_image_original_nonzero raw rawOrdinary (fun q : Selected=>q.val) hn0 labels
  have hunit : ∀l,unit l≠0:=fun _=>Units.ne_zero _
  let ho : ∀r : secondLiveRows (fun q=>(rawOrdinary q).block),
      jointFirstFrequency left u₀ unit
        (secondEncodedRow (fun q=>(rawOrdinary q).block) rawFirst r)≠0:=fun r=>
    actual_joint_first_frequency_ne_zero left u₀ unit
      (secondEncodedRow (fun q=>(rawOrdinary q).block) rawFirst r) hu₀ (hunit _)
      (geometryFirstSource s R seed (Z^D) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin (firstIndex r.val.1.1).1.val.1).hC
  let key:=fun r : secondLiveRows (fun q=>(rawOrdinary q).block)=>
    if second then reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun q=>(rawOrdinary q).block) rawFirst r left u₀ unit (ho r))
    else secondEncodedNonzeroRow (fun q=>(rawOrdinary q).block) rawFirst r left u₀ unit (ho r)
  let core:=he hZ (α:=α) (Label:=Label) reflected s R seed (Z^D) amp reserve t
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) hseed (le_refl _) hend hV hKM hs₁ hs₂ hamp hr
    bin (fun l=>(firstIndex l).1) hinj (fun l=>(firstIndex l).2) hf₁
    (fun _=>χ₀) (fun _=>Q) (fun _=>m)
  have bound:=core rows hn second target
  change ((Finset.univ.filter (fun r : rows=>key r.val=target)).card:ℝ)≤ Cfiber*Z^(2*ε) at bound
  have cardEq:=affine_high_selected_fiber_card_image lift hlift labels key target
  have keyEq (r : secondLiveRows (fun q=>(ordinary q).block)) :
      key (lift r)=
      (if second then reflectedNonzeroJointLabel
        (secondEncodedNonzeroRow (fun q=>(ordinary q).block) first r left u₀ unit (hf r))
      else secondEncodedNonzeroRow (fun q=>(ordinary q).block) first r left u₀ unit (hf r)) :=
    affine_high_selected_live_reflected_key rawOrdinary (fun q : Selected=>q.val) rawFirst r
      left second u₀ unit (ho (lift r)) (hf r)
  have eqFilter : (Finset.univ.filter (fun r : labels=>key (lift r.val)=target))=
      Finset.univ.filter (fun r : labels=>
        (if second then reflectedNonzeroJointLabel
          (secondEncodedNonzeroRow (fun q=>(ordinary q).block) first r.val left u₀ unit (hf r.val))
        else secondEncodedNonzeroRow (fun q=>(ordinary q).block) first r.val left u₀ unit (hf r.val))=target) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,keyEq]
  have countEq:=congrArg (fun n : ℕ=>(n:ℝ)) cardEq
  have filterEq:=congrArg (fun fs : Finset labels=>(fs.card:ℝ)) eqFilter
  exact filterEq.symm.trans_le (countEq.trans_le bound)
end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_fiber_card_image
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_block_nonzero_of_datum_eq
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_image_original_nonzero
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_original_block_nonzero
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_constant_ordinary
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_high_selected_live_original_support
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventually_affine_high_selected_ordinary_fibers

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineHighSelectedFiber -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineMainLowPayment; sha256 9de646c2f1fd0fb4e3e77ef0efffdccdd74ac183c7c15a4b99e30a6bbf1396e2 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

                                                            

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle61InitialMass
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
open Cycle61FinalNatural Cycle61Moment.LowBranch
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
open Cycle61Moment LocalMoment
open CenteredMomentSecondInputCapacitySource
open CenteredMomentChildRows CenteredMomentSecondCanonical CenteredMomentSecondEnergySplit
open CenteredMomentNaturalRowSource
open Cycle61InitialSource
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

local notation "O" => HeckeFamily.O
local instance geometryAffineMainLowDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := geometryMainCoarseFamilySumDecidable

/-- Profiles supply the actual full-source zero gate. -/
theorem affine_main_low_profile_zero (p : Profiles (1/4) (9/4)) (j : Fin 2) : p.profile j 0=0 := by
  by_contra h
  have hh := (p.support j h).1
  norm_num at hh

/-- Only positive fees accompany the single negative low reserve. -/
theorem affine_main_low_target_lower (g : GeometryAffineLowSchedule) (N : ℕ)
    (amp omega mesh : ℝ)(ha : 0≤ amp)(ho : 0≤ omega)(hm : 0≤ mesh) :
    -1≤ geometryAffineLowTarget g N amp omega mesh := by
  have hq : 0≤ Cycle61.Arithmetic.q0 := by norm_num [Cycle61.Arithmetic.q0]
  have hmu:=g.μ_pos.le
  have hd:=g.δ_pos.le
  unfold geometryAffineLowTarget
  have hp : 0≤(2*Cycle61.Arithmetic.q0/9)*(omega+g.μ/8) := by positivity
  have hpm : 0≤ Cycle61.Arithmetic.q0*mesh := mul_nonneg hq hm
  have hN : 0≤2*g.δ*31*(N:ℝ) := by positivity
  have hs : 0≤3*((N:ℝ)+2)*3*g.δ := by positivity
  linarith

set_option linter.unusedVariables false in
set_option linter.defProp false in
set_option maxHeartbeats 160000 in
def GeometryAffineMainLowSpec
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (ηseed : Character)(Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)
    (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})(Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(tplain X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂)
    (height mesh : ℝ)(hw : ∀i,0≤ w i)(hmesh : 0≤ mesh)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))(hwm : ∀i,w i≤ mesh)
    (hheight : 0≤ height)(hfreq : ∀i,|freq i|≤ height)(hT : 2< Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hlo₁ : (41/100:ℝ)≤ length Z X₁)(hlo₂ : (41/100:ℝ)≤ length Z X₂)
    (hhi₁ : length Z X₁≤(44/100:ℝ))(hhi₂ : length Z X₂≤(44/100:ℝ))
    (hslots : (17/500:ℝ)≤∑i,w i ∧ (∑i,w i)≤1/25)
    (hcone : length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑i,w i)≤ Cycle61.Arithmetic.B),
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_main_low_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_main_low_profile_zero p 1
    ∀{Label : Type}[Fintype Label]
      (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
      (firstIndex : Label→ GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
    let first:=fun l=>geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let amp:=(1:ℝ)*Cycle61.Arithmetic.amp (Cycle61.Arithmetic.cellUpper
      (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
        1 s.ν s.W s.P≠0)
      (hinj : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val))),
    let rows:=mainLowSelectedNonzeroRows reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8)
      (9/4) t (Fintype.card α) hZ bin hz₁ hz₂ firstIndex
    let datum : rows→ SecondInputDatum α:=fun r=>geometryLowSecondDatum reflected s 1 1 Z 1 amp
      (g.μ/64) (g.μ/8) (9/4) t (Fintype.card α) hZ bin (firstIndex r.val.1)
      hz₁ hz₂ r.val.2
    ∀(χ₀ : rows→ RayFourExpansion.RayCharacter)(m : O)(hm₀ : m≠0)
      (hml : goodLambda∣m)(hm₂ : (2:O)∣m)(Ψ : 𝓢(ℝ,ℂ))(t₀ u : ℝ),
    ∃hP : ∀r,(datum r).R*(if second then (datum r).D else (datum r).C)≠0,
    ∃hPN : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤ Z^(28:ℝ),
    let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
      mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ (internalQ Q η₀) hQ72
        m hm₀ hml hm₂ Z 28 hZ second (hP r) (hPN r) η₀
        (inf_le_left.trans hQM) inf_le_right g.e (Z^g.τ) g.e_pos hT hbeta hβhi
    let firstMass:=fun l=>geometryFirstHighMass reflected s 1 1 Ψ 1 Z (g.μ/64) g.δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let childSrc:=fun l=>geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
    mainLowPhysicalCompleteCost (Fintype.card α) 1 (1/4) second
      (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
      (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u canonical≤
      Kall*(p.control Sp)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
        Z^(geometryAffineLowTarget g (Fintype.card α) amp omega mesh)*
        (1+|t|+height)^degreeAll*(1+|t₀|)^degreeAll*(1+|u|)^degreeAll

set_option linter.defProp false in
def GeometryAffineMainLowSourceSpec
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Cs Z : ℝ) : Prop :=
  ∀(θ : α→ RayQuotient.Characters M H)(η₀ : Character)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (tplain X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂),
    (∀i,0≤ w i) → (41/100:ℝ)≤ length Z X₁ → (41/100:ℝ)≤ length Z X₂ →
    length Z X₁≤(44/100:ℝ) → length Z X₂≤(44/100:ℝ) → (∑i,w i)≤1/25 →
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 tplain X₁ X₂ hX₁ hX₂
    GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z

attribute [local irreducible] Finset.univ mainLowPhysicalCompleteCost
set_option maxHeartbeats 180000 in
theorem affine_main_low_spec_of_receipts
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (ηseed : Character)(Cs : ℝ)(Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)
    (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})(Z : ℝ)
    (hω : 0≤ frequencyLoss Z 32 (g.μ/64)+g.μ/8 ∧
      frequencyLoss Z 32 (g.μ/64)+g.μ/8≤33*g.μ/128)
    (hcaps : GeometryAffineMainLowSourceSpec (α:=α) M H hH W hW hWs Cs Z)
    (hspec : GeometryAffineLowSelectedSpec (α:=α) M H hH W hbeta g ηseed Cs Sp degreeAll Kall η₀ Q hQM hQ72 Z) :
    GeometryAffineMainLowSpec (α:=α) M H hH W hW hWs hbeta g ηseed Sp degreeAll Kall η₀ Q hQM hQ72 Z := by
  unfold GeometryAffineMainLowSpec
  intro hZ θ w σ freq hσ bΦ state hη p tplain X₁ X₂ hX₁ hX₂ height mesh hw hmesh hmeshcap hwm
    hheight hfreq hT hβhi hlo₁ hlo₂ hhi₁ hhi₂ hslots hcone s hz₁ hz₂
    Label _ reflected second bin t firstIndex first amp omega hf₁ hinj rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u
  have cap₀:=hcaps θ η₀ w σ freq hσ bΦ state p tplain X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots.2
  obtain ⟨caps,hm⟩:=actual_affine_low_source_gates M H hH η₀ θ W hW hWs w σ freq hσ state p
    tplain X₁ X₂ hX₁ hX₂ Cs hZ hw hslots.2 hhi₁ hhi₂ cap₀
  have hlogs : ∀j,Real.logb Z (s.P j)=w j := by
    intro j
    change Real.logb Z (Z^(w j))=w j
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hsum : (∑j,Real.logb Z (s.P j))=∑j,w j := Finset.sum_congr rfl (fun j _=>hlogs j)
  have hηs : s.η=ηseed := hη
  have hw₁ (j : α) : w j≤1 :=
    (Finset.single_le_sum (fun i _=>hw i) (Finset.mem_univ j)).trans (hslots.2.trans (by norm_num))
  have hwr (j : α) : w j/31≤1 := by linarith [hw₁ j]
  have hcell:=Cycle61.Moment.originalCell_mem hslots
  have hbetaCell:=Cycle61.Arithmetic.cellUpper_bounds hcell.1 hcell.2.1
  have hamp0 : 0≤ amp := by
    simpa only [amp,hsum,div_one,one_mul] using (Cycle61.Arithmetic.amp_pos hbetaCell).le
  have hamp : |amp|≤4 := by
    rw [abs_of_nonneg hamp0]
    have h:= (Cycle61.Arithmetic.amp_bounds hbetaCell).2.trans (by norm_num : (21310217/1970880000:ℝ)≤4)
    simpa only [amp,hsum,div_one,one_mul] using h
  have homega : |omega|≤4 := by
    rw [abs_of_nonneg hω.1]
    exact hω.2.trans (by linarith [g.μ_cap])
  have htarget:=affine_main_low_target_lower g (Fintype.card α) amp omega mesh hamp0 hω.1 hmesh
  unfold GeometryAffineLowSelectedSpec at hspec
  have hb:=hspec (Label:=Label) hZ s p caps θ w σ freq hm hηs height mesh hw
    (fun j=>(hwm j).trans hmeshcap) hwr hmesh hwm hσ hheight hfreq hT hβhi
    (by simpa only [hsum] using hslots) (by
      change length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B
      simpa only [hsum] using hcone)
    reflected second bin t firstIndex hamp0 hamp homega htarget hf₁ hinj χ₀ m hm₀ hml hm₂ Ψ t₀ u
  exact hb

attribute [local irreducible] GeometryAffineMainLowSpec GeometryAffineLowSelectedSpec
attribute [local irreducible] actual_affine_low_selected_payment
set_option maxHeartbeats 180000 in
def actual_affine_main_low_payment
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)(ηseed : Character)
    (ηcoarse : Character)(u₀ : O)(F₀ : NaturalRow ηcoarse u₀)(R₀ : Ideal O)(hu₀ : u₀≠0) :
    ΣCs : ℝ,ΣdegreeAll : Finset α→ℕ,ΣSp : Finset α→ Finset (ℕ×ℕ),
      PLift (1≤ Cs ∧ ∀T,(0,0)∈Sp T) ×
      (∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤ M),
        internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)},
        ΣKall : Finset α→ℝ,PLift ((∀T,0< Kall T) ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
          ∀T : Finset α,GeometryAffineMainLowSpec (α:=T) M H hH W hW.continuous hWs hbeta g
            ηseed (Sp T) (degreeAll T) (Kall T) η₀ Q hQM hQ72 Z)) := by
  let sources:=eventual_actual_affine_exceptional_source_gates (α:=α) M H hH W hW.continuous hWs
  let Cs:=Classical.choose sources
  have hCs:=(Classical.choose_spec sources).1
  have hsources:=(Classical.choose_spec sources).2
  let ks (T : Finset α):=actual_affine_low_selected_payment (α:=T) M H hH W hWs hW hbeta g
    ηseed Cs hCs ηcoarse u₀ F₀ R₀ hu₀
  refine ⟨Cs,(fun T=>(ks T).1),(fun T=>(ks T).2.1),PLift.up ⟨hCs,fun T=>(ks T).2.2.1.down⟩,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  let kc (T : Finset α):=(ks T).2.2.2 η₀ Q hQM hQ0 hQt hQ72
  refine ⟨(fun T=>(kc T).1),PLift.up ⟨(fun T=>(kc T).2.down.1),?_⟩⟩
  filter_upwards [hsources,Filter.eventually_all.mpr (fun T=>(kc T).2.down.2),
    eventual_geometry_small_frequency g.μ g.μ_pos] with Z hc hk hfreq
  refine ⟨(hk ∅).1,?_⟩
  intro T
  apply affine_main_low_spec_of_receipts (α:=T) M H hH W hW.continuous hWs hbeta g
    ηseed Cs (ks T).2.1 (ks T).1 (kc T).1 η₀ Q hQM hQ72 Z hfreq.2
  · unfold GeometryAffineMainLowSourceSpec
    intro θ η₀' w σ freq hσ bΦ state p tplain X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots inp
    exact geometry_affine_source_gates_actual_card inp p (Fintype.card α) Cs Z
      (hc.2 T η₀' θ w σ freq hσ bΦ state p tplain X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots)
  · exact (hk T).2

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_main_low_profile_zero
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_main_low_target_lower

#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_main_low_spec_of_receipts

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_main_low_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineMainLowPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCompletePartition; sha256 3697962b5c903489fd2e9d42e7825f09dd9b9e001793a952258ba21909dc391c -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                  
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentAmplificationChildInput CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondLiveBlock CenteredMomentSourceRow
open LocalMoment CenteredMomentSecondInputCapacitySource CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondEnergySplit ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- Lift the per-source selector to the physical family before dividing it
into low and high rows. The signed row and its original block are unchanged. -/
def mainPhysicalFamilySelector (second : Bool) (d : Label→ SecondInputDatum α) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e) :
    secondLiveRows (fun l=>(d l).block)→ BufferIndex e :=
  fun r=>select r.val.1 r.val.2.1 r.val.2.2.1
    ⟨mainLowSignedRow second r.val.2.2.2.val,by
      apply (mem_main_low_source_rows second _ (fun _=>True) _).mpr
      refine ⟨r.val.2.2.2,?_,rfl,True.intro⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩⟩

theorem main_low_physical_predicate_iff (second : Bool) (d : Label→ SecondInputDatum α) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e)
    (r : secondLiveRows (fun l=>(d l).block)) :
    mainLowPhysicalSourcePredicate (mainLowSourceRows second (d r.val.1) (fun _=>True))
      (select r.val.1 r.val.2.1 r.val.2.2.1) (mainLowSignedRow second r.val.2.2.2.val) ↔
    bufferValue e (mainPhysicalFamilySelector second d select r)<167/200 := by
  have hz : mainLowSignedRow second r.val.2.2.2.val∈
      mainLowSourceRows second (d r.val.1) (fun _=>True) := by
    apply (mem_main_low_source_rows second _ (fun _=>True) _).mpr
    exact ⟨r.val.2.2.2,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩,rfl,True.intro⟩
  simp only [mainLowPhysicalSourcePredicate,dite_eq_left hz,mainPhysicalFamilySelector]

/-- Exact complementary physical costs on one selector. Both ray sums,
both signed Mellin heights, the lower factor, and all residual divisors remain
literal. No arithmetic-label or allocation count is introduced. -/
theorem actual_main_complete_low_high_partition
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→ SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e) :
    (∑l,coefficient l*mainNormalizedBlockCost N a ap second (d l) t u)=
      mainLowPhysicalCompleteCost N a ap second d coefficient t u select+
      ∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(d l).block)=>
        167/200≤ bufferValue e (mainPhysicalFamilySelector second d select r)),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_block_cost_rows]
  rw [←Finset.sum_coe_sort]
  rw [actual_main_low_physical_ordinary_row_cost]
  unfold mainLowPhysicalOrdinaryRows
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have hcost : (∑D∈secondResidualIdeals (fun l=>(d l).block) r.val,
      mainNormalizedPhysicalCost N a ap second d coefficient t u r.val D)=
      (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
        normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
      highNormalizedRowCost second d r
        ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
        ((d r.val.1).block.divisors.filter Squarefree) := by
    rw [actual_second_residual_ideals_label]
    cases second <;> simp [mainNormalizedPhysicalCost,highNormalizedRowCost,Finset.mul_sum]
  rw [hcost]
  have hp:=main_low_physical_predicate_iff second d select r
  by_cases hl : bufferValue e (mainPhysicalFamilySelector second d select r)<167/200
  · simp only [hp,hl,ite_true,not_le.mpr hl,ite_false,add_zero]
  · simp only [hp,hl,ite_false,le_of_not_gt hl,ite_true,zero_add]

/-- The lift used in the exact partition is the existing canonical family
selector. This equality fixes the same selector on both complementary costs. -/
theorem main_physical_family_canonical_selector_eq
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (d : Label→ SecondInputDatum α) (χ₀ : Label→ RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1< Z) (second : Bool)
    (hP : ∀l,(d l).R*(if second then (d l).D else (d l).C)≠0)
    (hPN : ∀l,(((d l).R*(if second then (d l).D else (d l).C)).absNorm:ℝ)≤ Z^Bmask)
    (η₀ : Character) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    mainPhysicalFamilySelector second (fun l=>ordinarySecondDatum (d l) (χ₀ l) Q m)
      (fun l χ ψ=>mainLowCanonicalSelector M H hH (d l) (χ₀ l) χ ψ Q hQ m hm hml hm2
        Z Bmask hZ second (hP l) (hPN l) η₀ hQM hQη e T he hT hβlo hβhi)=
    mainLowFamilyCanonicalSelector M H hH d χ₀ Q hQ m hm hml hm2 Z Bmask hZ second
      hP hPN η₀ hQM hQη e T he hT hβlo hβhi := rfl

/-- Complete complementary physical bounds give the exact normalized
ratio-fiber contract. The original source height belongs in `CL` and `CH`;
only the two inner Mellin heights are paid by the common degree here. -/
theorem second_normalized_bound_of_complete_low_high
    (N : ℕ) (a ap : ℝ) (ha : 0< a) (hap : 0< ap)
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ))
    (coefficient : Label→ℝ) (hw : ∀l,‖w l‖≤ coefficient l)
    (hcard : Fintype.card α≤ N) (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0→ ap≤ x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0→ ap≤ x)
    {e : ℝ} (select : (second : Bool)→(l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→ BufferIndex e)
    (CL CH : ℝ) (dl dh : ℕ) (hCL : 0≤ CL) (hCH : 0≤ CH)
    (hlow : ∀(second : Bool)(t u : ℝ),
      mainLowPhysicalCompleteCost N a ap second d coefficient t u (select second)≤
        (CL*(1+‖t‖)^dl)*(1+‖u‖)^dl)
    (hhigh : ∀(second : Bool)(t u : ℝ),
      (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(d l).block)=>
        167/200≤ bufferValue e (mainPhysicalFamilySelector second d (select second) r)),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree))≤
        (CH*(1+‖t‖)^dh)*(1+‖u‖)^dh) :
    SecondNormalizedBound W (max dl dh) (max dl dh) d w (fun _=>CL+CH) (fun _=>1) := by
  apply second_normalized_bound_of_full
  intro second t u
  have hc:=actual_main_normalized_coefficient_cost N a ap ha hap d w W coefficient hw
    hcard hlower hW₁ hW₂ second t u
  rw [actual_main_complete_low_high_partition N a ap second d coefficient t u (select second)] at hc
  have hsplit:=hc.trans (add_le_add (hlow second t u) (hhigh second t u))
  have hm (C : ℝ) (k : ℕ) (hC : 0≤ C) (hk : k≤ max dl dh) :
      (C*(1+‖t‖)^k)*(1+‖u‖)^k≤
        (C*(1+‖t‖)^(max dl dh))*(1+‖u‖)^(2*max dl dh) := by
    have ht : 1≤1+‖t‖ := by linarith [norm_nonneg t]
    have hu : 1≤1+‖u‖ := by linarith [norm_nonneg u]
    have hku : k≤2*max dl dh := by omega
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hk) hC)
      (pow_le_pow_right₀ hu hku) (pow_nonneg (zero_le_one.trans hu) _)
      (mul_nonneg hC (pow_nonneg (zero_le_one.trans ht) _))
  apply (hsplit.trans (add_le_add (hm CL dl hCL (le_max_left _ _))
    (hm CH dh hCH (le_max_right _ _)))).trans_eq
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_physical_predicate_iff
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_complete_low_high_partition
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_physical_family_canonical_selector_eq
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_normalized_bound_of_complete_low_high

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCompletePartition -/
