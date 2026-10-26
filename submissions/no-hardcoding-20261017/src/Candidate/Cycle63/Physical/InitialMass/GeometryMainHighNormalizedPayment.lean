import Candidate.Cycle63.Physical.InitialMass.GeometryMainSelectedRowEmbedding
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainOrdinaryFiber

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
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
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
local instance geometryMainHighNormalizedPaymentSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := mainOrdinaryFiberSumDecidable

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
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The selected first allocation has the actual ordinary joint-key fiber
budget. The first-label/projector injection replaces every label count. -/
theorem eventually_actual_selected_main_ordinary_fibers (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(b bs ε Amax Mmax ξ : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hε : 0<ε)
    (hA : 0≤Amax)(hM : 0≤Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃D : ℝ,0<D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(K a reserve t : ℝ)(hK : 0<K),
      Squarefree seed → Fintype.card α≤N → Endpoints b bs bs s → volume s≤Z^Amax → K≤Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤a → 0≤reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed K Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed K Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→actualAllocations s.pools (C l),
      (∀l,frozenCoefficient (alloc l).val (C l) R s.ν s.W s.P≠0) →
      let slots := fun l=>liveIndices (alloc l).val
      let source := fun l=>child s (C l) R (alloc l) (χ l) t
      let first := fun l=>geometryFirstLabel s R seed K Z ξ hK bin (column l).val
      let projector := fun l=>(column l).val.2.1.val
      let Kmain := firstMainRadius reflected K (volume s) Z ξ (3*a) reserve
      let Tsec := firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0<Kmain (first l) := fun l=>first_main_radius_pos reflected K (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
      let label := fun q : Index=>first q.1
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hunit : ∀l,unit l≠0 := fun _=>Units.ne_zero _
      ∀(χ₀ : Index→RayCharacter)(Q : Index→Ideal O)(m : Index→O),
      let ordinary:=fun q=>ordinarySecondDatum (datum q) (χ₀ q) (Q q) (m q)
      ∀(rows : Finset (secondLiveRows (fun q=>(ordinary q).block))),
      (∀r∈rows,(datum r.val.1).block.value ballProfile≠0) →
      ∀second : Bool,
      let ho : ∀r : secondLiveRows (fun q=>(ordinary q).block),
        jointFirstFrequency left u₀ unit (secondEncodedRow (fun q=>(ordinary q).block) label r)≠0 :=
        fun r=>actual_joint_first_frequency_ne_zero left u₀ unit
          (secondEncodedRow (fun q=>(ordinary q).block) label r) hu₀ (hunit _)
          (geometryFirstSource s R seed K Z ξ hK bin (column r.val.1.1).val.1).hC
      let key := fun r : rows=>secondEncodedNonzeroRow (fun q=>(ordinary q).block) label r.val left u₀ unit (ho r.val)
      ∀target : NonzeroJointSourceLabel left u₀ unit,
      ((Finset.univ.filter (fun r : rows=>
        (if second then reflectedNonzeroJointLabel (key r) else key r)=target)).card:ℝ)≤D*Z^(2*ε) := by
  let receipt:=actual_geometry_main_ordinary_row_fiber_bound η₀ u₀ F₀ R₀ hu₀
    N b bs ε Amax Mmax ξ hb hbs hε hA hM hξ hξε
  let D:=Classical.choose receipt
  have hD:= (Classical.choose_spec receipt).1
  have hevent:=(Classical.choose_spec receipt).2
  refine ⟨D,hD,?_⟩
  filter_upwards [hevent] with Z he
  intro hZ α Label _ _ _ reflected s R seed K a reserve t hK hseed hcard hend hV hKM
    hs₁ hs₂ ha hr bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index datum label left unit hunit χ₀ Q m ordinary
    rows hn second ho key target
  let block:=fun q : Index=>(datum q).block
  let fullRows : ∀q,(datum q).rows=sourceRows (datum q).C (datum q).D (datum q).inactive (datum q).radius:=fun _=>rfl
  let embed:=ordinaryHighOriginalRow datum χ₀ Q m fullRows
  let hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0:=
    fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
      hu₀ (hunit _) (geometryFirstSource s R seed K Z ξ hK bin (column r.val.1.1).val.1).hC
  have hb:=he hZ reflected s R seed K a reserve t hK hseed hcard hend hV hKM hs₁ hs₂ ha hr
    bin column hinj alloc halloc χ₀ Q m rows hn second target
  have hkey (r : rows) :
      secondEncodedNonzeroRow block label (embed r.val) left u₀ unit (hf (embed r.val))=key r :=
    ordinary_main_nonzero_key_eq datum χ₀ Q m fullRows label left u₀ unit r.val
      (hf (embed r.val)) (ho r.val)
  let oldKey:=fun r : rows=>secondEncodedNonzeroRow block label (embed r.val) left u₀ unit (hf (embed r.val))
  change ((Finset.univ.filter (fun r : rows=>
    (if second then reflectedNonzeroJointLabel (oldKey r) else oldKey r)=target)).card:ℝ)≤D*Z^(2*ε) at hb
  have heq : oldKey=key:=funext hkey
  rw [heq] at hb
  exact hb

/-- The literal first-child height and both signed Mellin orientations
satisfy the high window gates on the small combined-height range. -/
theorem actual_selected_main_high_shifted_heights
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected second : Bool)(s : Input α)(R seed : Ideal O)
    (Z D amp ξ reserve b baseHeight : ℝ)(N : ℕ)(hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ))(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (q : (l : Label)×GeometryLowSecondIndex reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin (firstIndex l))
    (freq : α→ℝ)(height t₀ u T e : ℝ)(p : BufferIndex e)
    (hT : 0≤T)(hh : 0≤height)(hf : ∀j,|freq j|≤height)(hp : 1≤p.1.val)
    (hsmall : 2*(1+|baseHeight|+height+2*Real.pi*(|t₀|+|u|))≤T) :
    let d:=geometryLowSecondDatum reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin
      (firstIndex q.1) hs₁ hs₂ q.2
    let shifted:=d.input.t+2*Real.pi*(u-(if second then -t₀ else t₀))
    (∀j,|shifted+freq j|+T/2≤(3*p.1.val+2:ℕ)*T) ∧
      |shifted|+T/2≤(3*p.1.val+2:ℕ)*T := by
  intro d shifted
  have hs:=main_low_payment_shifted_height_envelope second baseHeight height t₀ u T hT hsmall
  have hb:=main_low_payment_height_bin p hp
    (baseHeight+2*Real.pi*(u-(if second then -t₀ else t₀))) height T hT hs
  have hshift : shifted=baseHeight+2*Real.pi*(u-(if second then -t₀ else t₀)):=rfl
  rw [←hshift] at hb
  refine ⟨?_,?_⟩
  · intro j
    have ha:=abs_add_le shifted (freq j)
    linarith [hf j]
  · linarith



section RowTransport
variable {α Selected Original : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Selected] [Fintype Original]
variable (datum : Original→SecondInputDatum α)(embed : Selected→Original)

def highSelectedRowEmbedding
    (r : SecondRow (fun j=>(datum (embed j)).block)) : SecondRow (fun j=>(datum j).block) :=
  ⟨embed r.1,r.2⟩

omit [Fintype Selected] [Fintype Original] in
theorem high_selected_row_embedding_injective (hinj : Function.Injective embed) :
    Function.Injective (highSelectedRowEmbedding datum embed) := by
  intro r v h
  have hl : r.1=v.1:=hinj (congrArg Sigma.fst h)
  apply Sigma.ext hl
  exact (Sigma.mk.inj_iff.mp h).2

theorem high_selected_row_embedding_live
    (r : SecondRow (fun j=>(datum (embed j)).block)) :
    highSelectedRowEmbedding datum embed r∈secondLiveRows (fun j=>(datum j).block) ↔
      r∈secondLiveRows (fun j=>(datum (embed j)).block) := by
  simp only [secondLiveRows,Finset.mem_filter,Finset.mem_univ,true_and]
  rfl


def highSelectedLiveRowEmbedding
    (r : secondLiveRows (fun j=>(datum (embed j)).block)) : secondLiveRows (fun j=>(datum j).block) :=
  ⟨highSelectedRowEmbedding datum embed r.val,(high_selected_row_embedding_live datum embed r.val).mpr r.property⟩

theorem high_selected_live_encoded_row (first : Original→FirstSourceLabel)
    (r : secondLiveRows (fun j=>(datum (embed j)).block)) :
    secondEncodedRow (fun j=>(datum j).block) first (highSelectedLiveRowEmbedding datum embed r)=
      secondEncodedRow (fun j=>(datum (embed j)).block) (fun j=>first (embed j)) r := rfl

theorem high_selected_live_nonzero_key (first : Original→FirstSourceLabel)
    (r : secondLiveRows (fun j=>(datum (embed j)).block))
    (left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)
    (hOriginal : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun j=>(datum j).block) first (highSelectedLiveRowEmbedding datum embed r))≠0)
    (hSelected : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun j=>(datum (embed j)).block) (fun j=>first (embed j)) r)≠0) :
    secondEncodedNonzeroRow (fun j=>(datum j).block) first (highSelectedLiveRowEmbedding datum embed r) left u₀ unit hOriginal=
      secondEncodedNonzeroRow (fun j=>(datum (embed j)).block) (fun j=>first (embed j)) r left u₀ unit hSelected := rfl

omit [Fintype Selected] in
/-- The projector union belongs to the original family, before any row or
zero-bin selection. -/
theorem high_selected_original_projector_union
    (r : SecondRow (fun j=>(datum (embed j)).block)) :
    secondResidualIdeals (fun j=>(datum (embed j)).block) r⊆mainHighProjectorUnion datum :=
  main_high_residual_subset_union datum (highSelectedRowEmbedding datum embed r)

omit [Fintype Selected] [Fintype Original] in
theorem high_selected_row_cost_image [DecidableEq (SecondRow (fun j=>(datum j).block))]
    (hinj : Function.Injective embed)
    (N : ℕ)(a ap : ℝ)(second : Bool)(coefficient : Original→ℝ)(t u : ℝ)
    (rows : Finset (SecondRow (fun j=>(datum (embed j)).block))) :
    (∑r∈rows,∑L∈secondResidualIdeals (fun j=>(datum (embed j)).block) r,
      mainNormalizedPhysicalCost N a ap second (fun j=>datum (embed j)) (fun j=>coefficient (embed j)) t u r L)=
    ∑r∈rows.image (highSelectedRowEmbedding datum embed),
      ∑L∈secondResidualIdeals (fun j=>(datum j).block) r,
      mainNormalizedPhysicalCost N a ap second datum coefficient t u r L := by
  rw [Finset.sum_image]
  · rfl
  · exact fun r _ v _ h=>high_selected_row_embedding_injective datum embed hinj h
end RowTransport

section SelectedTransport
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance geometryMainHighNormalizedSelectedSumDecidable : DecidableEq (α⊕Fin 2) := geometryMainNormalizedSumDecidable
variable (reflected : Bool)(s : Input α)(R seed : Ideal O)
variable (Z D amp ξ reserve b baseHeight : ℝ)(N : ℕ)(hZ : 1<Z)
variable (bin : ℤ×(Fin 5→ℤ))(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0)
variable (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
local notation "Original" => {j : GeometryMainSecondIndex reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin // j∈geometryMainNonzeroBlocks reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin hs₁ hs₂}
local notation "Selected" => mainLowSelectedNonzeroRows reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin hs₁ hs₂ firstIndex
local notation "embed" => mainLowSelectedOriginal reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin hs₁ hs₂ firstIndex

/-- Exact transport of the selected first-allocation family into the original
ordinary family. The coefficient includes physical mass and child volume. -/
theorem actual_selected_main_high_cost_image
    (hinj : Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^D) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val,
      (firstIndex l).1.val.2.1.val)))
    (a ap : ℝ)(second : Bool)(t u : ℝ) :
    let raw : Original→GeometryMainSecondIndex reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin:=Subtype.val
    ∀(χ : Original→RayCharacter)(Q : Original→Ideal O)(m : Original→O)(mass : Original→ℝ),
    let datum:=fun j : Original=>geometryMainOrdinaryDatum reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin hs₁ hs₂ (χ j) (Q j) (m j) (raw j)
    let coefficient:=fun j : Original=>mass j/volume (datum j).input
    ∀rows : Finset (SecondRow (fun j : Selected=>(datum (embed j)).block)),
    (∑r∈rows,∑L∈secondResidualIdeals (fun j : Selected=>(datum (embed j)).block) r,
      mainNormalizedPhysicalCost N a ap second (fun j : Selected=>datum (embed j)) (fun j=>coefficient (embed j)) t u r L)=
    ∑r∈rows.image (highSelectedRowEmbedding datum embed),
      ∑L∈secondResidualIdeals (fun j=>(datum j).block) r,
      mainNormalizedPhysicalCost N a ap second datum coefficient t u r L := by
  intro raw χ Q m mass datum coefficient rows
  exact high_selected_row_cost_image datum embed
    (main_low_selected_original_injective reflected s R seed Z D amp ξ reserve b baseHeight N hZ bin hs₁ hs₂ firstIndex hinj)
    N a ap second coefficient t u rows
end SelectedTransport

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventually_actual_selected_main_ordinary_fibers

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_selected_main_high_shifted_heights

#print axioms OAI.SevenEighths.Cycle63InitialMass.high_selected_row_embedding_injective

#print axioms OAI.SevenEighths.Cycle63InitialMass.high_selected_row_embedding_live

#print axioms OAI.SevenEighths.Cycle63InitialMass.high_selected_row_cost_image

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_selected_main_high_cost_image

#print axioms OAI.SevenEighths.Cycle63InitialMass.high_selected_live_encoded_row

#print axioms OAI.SevenEighths.Cycle63InitialMass.high_selected_live_nonzero_key

#print axioms OAI.SevenEighths.Cycle63InitialMass.high_selected_original_projector_union
