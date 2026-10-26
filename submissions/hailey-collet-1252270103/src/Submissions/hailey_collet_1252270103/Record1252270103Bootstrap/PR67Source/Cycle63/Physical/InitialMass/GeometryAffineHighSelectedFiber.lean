import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineHighSelectedTransport
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open CenteredMomentFirstAmplificationChoice
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

open Cycle63FinalNatural CenteredMomentSourceRow CenteredMomentSecondEnergySplit
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch

attribute [local irreducible] Finset.univ SecondInputDatum.block

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- An injective lift preserves the exact finite fiber count. -/
theorem affine_high_selected_fiber_card_image
    {A B Key : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (embed : A→B) (hinj : Function.Injective embed) (rows : Finset A)
    (key : B→Key) (target : Key) :
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
    (raw ordinary : Original→SecondInputDatum α) (embed : Selected→Original)
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
variable (Z D amp ξ reserve b t : ℝ) (hZ : 1<Z)
variable (bin : ℤ×(Fin 5→ℤ)) (hs₁ : s.W₁ 0=0) (hs₂ : s.W₂ 0=0)
variable (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin)
local notation "Selected" => mainLowSelectedNonzeroRows reflected s R seed Z D amp ξ reserve b t (Fintype.card α) hZ bin hs₁ hs₂ firstIndex
local notation "Original" => geometryMainNonzeroBlocks reflected s R seed Z D amp ξ reserve b t (Fintype.card α) hZ bin hs₁ hs₂
local notation "embed" => mainLowSelectedOriginal reflected s R seed Z D amp ξ reserve b t (Fintype.card α) hZ bin hs₁ hs₂ firstIndex

/-- The original full-block filter supplies physical nonzero evidence. -/
theorem affine_high_selected_original_block_nonzero (q : Selected) :
    (mainLowSelectedDatum reflected s R seed Z D amp ξ reserve b t (Fintype.card α)
      hZ bin hs₁ hs₂ firstIndex q).block.value ballProfile≠0 :=
  (Finset.mem_filter.mp (embed q).property).2.2

end Membership

/-- The Fourier count is literally card α; supported first allocations
supply the uniform fiber budget without an arithmetic label fee. -/
theorem eventually_affine_high_selected_ordinary_fibers
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    {α : Type} [Fintype α] [DecidableEq α]
    (b bs ε Amax Mmax ξ : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hε : 0<ε)
    (hA : 0≤Amax)(hM : 0≤Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃Cfiber : ℝ,0<Cfiber ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(D amp reserve t : ℝ),
      Squarefree seed → Endpoints b bs bs s →
      volume s≤Z^Amax → Z^D≤Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤amp → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
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
  change ((Finset.univ.filter (fun r : rows=>key r.val=target)).card:ℝ)≤Cfiber*Z^(2*ε) at bound
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
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
