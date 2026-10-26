/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryAmplifiedRemainder
import Candidate.Uneven.AuxiliaryErrorMain
import Candidate.Uneven.AuxiliaryCellGeometry
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Uneven.AuxiliaryErrorFullPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowAggregate

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.AuxiliaryErrorReconstruction
open OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open OAI.SevenEighths.AuxiliaryReconstruction
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationActiveFactor CenteredMomentPrimeElements
open CenteredMomentSecondRadicalBudget CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair
open Cycle63Moment CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentChildRows CenteredMomentSourceMass CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CompletedGauss
local notation "O" => HeckeFamily.O
local instance errorSelectedPaymentSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

private theorem error_allocation_cast_val {κ : Type*} [Fintype κ]
    (pools : κ→Finset (Ideal O))(C D : Ideal O)(h : C=D)
    (B : actualAllocations pools C) : (h ▸ B).val=B.val := by
  cases h
  rfl

section Selected
variable {ι Label : Type} [Fintype ι] [Fintype Label]
variable (s : Input ι) (reflected : Bool)
variable (first : Label→FirstSourceLabel) (projector : Label→Ideal O)
variable (hinj : Function.Injective (fun j=>(first j,projector j)))
variable (alloc : (j : Label)→actualAllocations s.pools
  (if reflected then (first j).1.2 else (first j).1.1))

/-- The occupied-pair inverse keeps the original selected allocation. -/
@[irreducible] def selectedErrorAllocation (pair : SelectedLowFirstPair first projector) :
    actualAllocations s.pools (if reflected then pair.1.val.1.2 else pair.1.val.1.1) :=
  let j:=(selectedLowFirstPairEquiv first projector hinj).symm pair
  let h : (if reflected then (first j).1.2 else (first j).1.1)=
      (if reflected then pair.1.val.1.2 else pair.1.val.1.1) := by
    rw [(selected_low_pair_inverse_fields first projector hinj pair).1]
  h ▸ alloc j

theorem selected_error_allocation_val (pair : SelectedLowFirstPair first projector) :
    (selectedErrorAllocation s reflected first projector hinj alloc pair).val=
      (alloc ((selectedLowFirstPairEquiv first projector hinj).symm pair)).val := by
  unfold selectedErrorAllocation
  exact error_allocation_cast_val _ _ _ _ _

theorem selected_error_allocation_nonzero (R : Ideal O)
    (hf : ∀j,frozenCoefficient (alloc j).val
      (if reflected then (first j).1.2 else (first j).1.1) R s.ν s.W s.P≠0)
    (pair : SelectedLowFirstPair first projector) :
    frozenCoefficient (selectedErrorAllocation s reflected first projector hinj alloc pair).val
      (if reflected then pair.1.val.1.2 else pair.1.val.1.1) R s.ν s.W s.P≠0 := by
  rw [selected_error_allocation_val]
  have h:=(selected_low_pair_inverse_fields first projector hinj pair).1
  simpa only [h] using hf ((selectedLowFirstPairEquiv first projector hinj).symm pair)

theorem selected_error_allocation_at (j : Label) :
    selectedErrorAllocation s reflected first projector hinj alloc
      (selectedLowFirstPair first projector j)=alloc j := by
  apply Subtype.ext
  rw [selected_error_allocation_val]
  change (alloc ((selectedLowFirstPairEquiv first projector hinj).symm
    ((selectedLowFirstPairEquiv first projector hinj) j))).val=(alloc j).val
  rw [Equiv.symm_apply_apply]

end Selected

/-- Reindex complete costs after all second labels and active allocations
have been summed; the prime denominator is retained. -/
theorem selected_error_prime_ray_cost_reindex {Label PrimeIndex : Type*}
    [Fintype Label] [Fintype PrimeIndex]
    (first : Label→FirstSourceLabel)(projector : Label→Ideal O)
    (hinj : Function.Injective (fun j=>(first j,projector j)))
    (outside : ℝ)(branch : Fin 3→ℝ)
    (cost : PrimeIndex→Fin 3→RayCharacter→SelectedLowFirstPair first projector→ℝ) :
    outside*(∑q : PrimeIndex,∑i : Fin 3,branch i*
      ∑j : Label,∑ψ : RayCharacter,
        cost q i ψ ((selectedLowFirstPairEquiv first projector hinj) j))=
    outside*(∑q : PrimeIndex,∑i : Fin 3,branch i*
      ∑l : selectedLowFirstLabels first,∑ψ : RayCharacter,
        ∑D : selectedLowFirstProjectors first projector l.val,cost q i ψ ⟨l,D⟩) := by
  apply congrArg (fun x : ℝ=>outside*x)
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x : ℝ=>branch i*x)
  calc
    _=∑p : SelectedLowFirstPair first projector,∑ψ : RayCharacter,cost q i ψ p :=
      Fintype.sum_equiv (selectedLowFirstPairEquiv first projector hinj) _ _ (fun _=>rfl)
    _=∑l : selectedLowFirstLabels first,
        ∑D : selectedLowFirstProjectors first projector l.val,∑ψ : RayCharacter,cost q i ψ ⟨l,D⟩ :=
      Fintype.sum_sigma _
    _=_ := Finset.sum_congr rfl (fun l _=>Finset.sum_comm)


private theorem error_selected_label_gate {Label : Type*}[Fintype Label]
    (first : Label→FirstSourceLabel)(P : FirstSourceLabel→Prop)(hP : ∀j,P (first j)) :
    ∀l∈selectedLowFirstLabels first,P l := by
  intro l hl
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hl
  exact hP j

private theorem error_selected_projector_gate {Label : Type*}[Fintype Label]
    (first : Label→FirstSourceLabel)(projector : Label→Ideal O)
    (P : Ideal O→Prop)(hP : ∀j,P (projector j)) :
    ∀(l : selectedLowFirstLabels first) D,D∈selectedLowFirstProjectors first projector l.val→P D := by
  intro l D hD
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hD
  exact hP j

private theorem error_actual_second_label_gates {κ : Type*}[Fintype κ]
    (s : Input κ)(R seed : Ideal O)(cap : ℝ)
    (hs : Squarefree seed)(hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(hcap : sourceRadius s ≤ cap) :
    (∀v∈actualSecondLabels s R seed,Supported v.1.1 ∧ Supported v.1.2) ∧
    (∀v∈actualSecondLabels s R seed,primeSupport v.1.1=primeSupport v.1.2) ∧
    (∀v∈actualSecondLabels s R seed,seed∣v.1.1 ∧ seed∣v.1.2) ∧
    (∀v∈actualSecondLabels s R seed,(v.1.1.absNorm:ℝ) ≤ cap ∧ (v.1.2.absNorm:ℝ) ≤ cap) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro v hv
    have h:=actual_second_labels_gates s R seed hs hw₁ hw₂ v hv
    exact ⟨h.1,h.2.1⟩
  · intro v hv
    exact (actual_second_labels_gates s R seed hs hw₁ hw₂ v hv).2.2.1
  · intro v hv
    have h:=actual_second_labels_gates s R seed hs hw₁ hw₂ v hv
    exact ⟨h.2.2.2.1,h.2.2.2.2.1⟩
  · intro v hv
    have h:=actual_second_labels_gates s R seed hs hw₁ hw₂ v hv
    exact ⟨h.2.2.2.2.2.1.trans hcap,h.2.2.2.2.2.2.trans hcap⟩

set_option linter.defProp false in
/-- Original occupied first keys feed the saved prime payment with their
own allocations. The extracted labels come from the literal child source. -/
def eventual_actual_selected_error_saved_payment (N : ℕ)(lo εv B ε : ℝ)
    (hlo : 0 < lo)(hev : 0 < εv)(hB : 0 ≤ B)(he : 0 < ε)
    (Mmin εaffine : ℝ)(hMmin : 0 < Mmin) :=
  let data:=eventual_actual_error_dependent_saved_payment N lo εv B ε hlo hev hB he Mmin εaffine hMmin
  let receipt:=Classical.choose_spec data
  And.intro receipt.1 (receipt.2.mono fun Z hz=>And.intro hz.1 (
    fun {ι Label : Type}[Fintype ι][Fintype Label](s : Input ι)
      (hcard : Fintype.card ι ≤ N)(hlower : lo ≤ s.lower)
      (reflected second : Bool)(T p exponent error εcommon M a δ reserve : ℝ)
      (hT : 1 ≤ T)(hp : p ≤ B)(hecommon : 0 ≤ εcommon)(hM : Mmin ≤ M)
      (hloss : error+εv+B*εcommon+ε ≤ 64*geometryLossUnit Mmin εaffine)
      (seed : Ideal O)(hs : Squarefree seed)(hs0 : seed≠0)
      (first : Label→FirstSourceLabel)(projector : Label→Ideal O)
      (hinj : Function.Injective (fun j=>(first j,projector j)))
      (hsup : ∀j,Supported (first j).1.1 ∧ Supported (first j).1.2)
      (heq : ∀j,primeSupport (first j).1.1=primeSupport (first j).1.2)
      (hseed : ∀j,seed∣(first j).1.1 ∧ seed∣(first j).1.2)
      (hnorm : ∀j,((first j).1.1.absNorm:ℝ) ≤ Z^B ∧ ((first j).1.2.absNorm:ℝ) ≤ Z^B)
      (hrad : ∀j,((commonRadical (first j).1.1 (first j).1.2).absNorm:ℝ) ≤ Z^p)
      (hgeom : ∀j,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first j) ≤ exponent)
      (hprojector : ∀j,Squarefree (projector j))
      (hdyad : ∀j,T ≤ ((projector j).absNorm:ℝ) ∧ ((projector j).absNorm:ℝ) < 2*T)
      (Rfirst : Ideal O)
      (alloc : (j : Label)→actualAllocations s.pools
        (if reflected then (first j).1.2 else (first j).1.1))
      (χ : Label→Character)(t : ℝ)
      (hf : ∀j,frozenCoefficient (alloc j).val
        (if reflected then (first j).1.2 else (first j).1.1) Rfirst s.ν s.W s.P≠0)
      (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)=>
    let labels:=selectedLowFirstLabels first
    let Ds : labels→Finset (Ideal O):=fun l=>selectedLowFirstProjectors first projector l.val
    let e:=selectedLowFirstPairEquiv first projector hinj
    let alloc' : (l : labels)→Ds l→actualAllocations s.pools
        (if reflected then l.val.1.2 else l.val.1.1):=
      fun l D=>selectedErrorAllocation s reflected first projector hinj alloc ⟨l,D⟩
    let χ' : (l : labels)→Ds l→Character:=fun l D=>χ (e.symm ⟨l,D⟩)
    let u : (l : labels)→(D : Ds l)→Input (liveIndices (alloc' l D).val):=
      fun l D=>child s (if reflected then l.val.1.2 else l.val.1.1) Rfirst (alloc' l D) (χ' l D) t
    fun (P : Finset (Ideal O))(hP : P.Nonempty)(hprime : ∀Q∈P,Prime Q)
      (hbad : ∀Q∈P,Q∉fixedBadPrimes)
      (hslot : ∀l D,∀q : elementPool P,∀j I,I∈(u l D).slots j→IsCoprime (Ideal.span {q.val}) I)=>
    let Bps:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)=>
      errorLiftedActiveAllocations (u l D) (Ideal.span {q.val}) (errorIndex i+1)
    fun (υ : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→
        RayCharacter→Bps l D q i→Character)(vheight : ℝ)=>
    let source:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i)=>
      child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
        (Rfirst*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight
    let R₂:=fun (l : labels)(q : elementPool P)(i : Fin 3)=>
      (Rfirst*(if reflected then l.val.1.2 else l.val.1.1))*(Ideal.span {q.val})^(errorIndex i+1)
    let children:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i)=>
      actualSecondLabels (source l D q i ψ Bp) (R₂ l q i) D.val
    fun (hsource : ∀l D q i ψ Bp,sourceRadius (source l D q i ψ Bp) ≤ Z^B)=>
    let gates : ∀(l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i),
        (∀v∈children l D q i ψ Bp,Supported v.1.1 ∧ Supported v.1.2) ∧
        (∀v∈children l D q i ψ Bp,primeSupport v.1.1=primeSupport v.1.2) ∧
        (∀v∈children l D q i ψ Bp,D.val∣v.1.1 ∧ D.val∣v.1.2) ∧
        (∀v∈children l D q i ψ Bp,(v.1.1.absNorm:ℝ) ≤ Z^B ∧ (v.1.2.absNorm:ℝ) ≤ Z^B) :=
      fun l D q i ψ Bp=>error_actual_second_label_gates
        (source l D q i ψ Bp) (R₂ l q i) D.val (Z^B)
        (error_selected_projector_gate first projector _ hprojector l D.val D.property)
        hw₁ hw₂ (hsource l D q i ψ Bp)
    let pay:=hz.2 s hcard hlower reflected second T p exponent error εcommon M a δ reserve
      hT hp hecommon hM hloss seed hs hs0 labels
      (error_selected_label_gate first _ hsup)
      (error_selected_label_gate first _ heq)
      (error_selected_label_gate first _ hseed)
      (error_selected_label_gate first _ hnorm)
      (error_selected_label_gate first _ hrad)
      (error_selected_label_gate first _ hgeom)
      Ds (error_selected_projector_gate first projector _ hprojector)
      (error_selected_projector_gate first projector _ hdyad)
      Rfirst alloc' χ' t
      (fun l D=>selected_error_allocation_nonzero s reflected first projector hinj alloc Rfirst hf ⟨l,D⟩)
      P hP hprime hbad hslot υ vheight
    let hpaid:=pay children
      (fun l D q i ψ Bp=>(gates l D q i ψ Bp).1)
      (fun l D q i ψ Bp=>(gates l D q i ψ Bp).2.1)
      (fun l D q i ψ Bp=>(gates l D q i ψ Bp).2.2.1)
      (fun l D q i ψ Bp=>(gates l D q i ψ Bp).2.2.2)
    let cost:=fun (q : elementPool P)(i : Fin 3)(ψ : RayCharacter)
        (pair : SelectedLowFirstPair first projector)=>
      ∑Bp : Bps pair.1 pair.2 q i,∑v∈children pair.1 pair.2 q i ψ Bp,
        extractedErrorLabelScalar reflected second pair.1.val v Z M a δ reserve error εcommon
          (volume s) (volume (source pair.1 pair.2 q i ψ Bp)) q.val (errorIndex i+1)
    (selected_error_prime_ray_cost_reindex first projector hinj
      (56/(P.card:ℝ)) (fun i=>16*(errorIndex i+2:ℝ)) cost).le.trans hpaid
  ))


end
end OAI.SevenEighths.AuxiliaryErrorReconstruction
