/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal fixed-residual Newton reduction returns the same three actual
allocations used by both the LOW and HIGH cofactor suppliers. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalFixedPlainNewton
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSelectedMass
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalNewtonGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSecondHeightFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentCanonicalFirst Cycle61Moment
open OAI.SevenEighths.Record1252270103Source Record1252270103Second Collision Admission.JointForced
open QRH.Record1252270103Low QRH.Record1252270103KernelMass CorrectedCentered
open Admission.SelectedHighCofactorFamily
local notation "O"=>HeckeFamily.O
local instance selectedNewtonDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

namespace Selection
variable {α:Type}[Fintype α]{s:Input α}{reflected second:Bool}
    {l:FirstSourceLabel}{C₂ D₂ R:Ideal O}
def frozenLeft (sel:Selection s reflected second l C₂ D₂ R):Ideal O :=
  (sel.B₁.val (Sum.inr 0)*sel.B₂.val (Sum.inr 0))*sel.Bf.val (Sum.inr 0)
def frozenRight (sel:Selection s reflected second l C₂ D₂ R):Ideal O :=
  (sel.B₁.val (Sum.inr 1)*sel.B₂.val (Sum.inr 1))*sel.Bf.val (Sum.inr 1)
def correction (sel:Selection s reflected second l C₂ D₂ R):Ideal O :=
  (1*(if second then D₂ else C₂))*sel.Cf
def marked (sel:Selection s reflected second l C₂ D₂ R):Ideal O :=
  (markedProduct sel.B₁.val*markedProduct sel.B₂.val)*markedProduct sel.Bf.val
def puncture (sel:Selection s reflected second l C₂ D₂ R):Ideal O :=
  ((R*(if reflected then l.1.2 else l.1.1))*(if second then D₂ else C₂))*sel.Cf
end Selection

private theorem selected_three_embedding {α:Type}[Fintype α]
    (B₁:Tuple α)(B₂:Tuple (liveIndices B₁))(Bf:Tuple (liveIndices B₂)):
    inheritedSlotEmbedding Bf (inheritedSlotEmbedding B₂
      (⟨Subtype.val,Subtype.val_injective⟩:liveIndices B₁↪α))=
      Admission.SelectedHighSlots.finalEmbedding B₁ B₂ Bf := by
  ext i
  rfl

private theorem selected_three_image {α:Type}[Fintype α]
    (B₁:Tuple α)(B₂:Tuple (liveIndices B₁))(Bf:Tuple (liveIndices B₂)):
    Admission.SelectedHighSlots.finalImage B₁ B₂ Bf=
      Finset.univ.map (inheritedSlotEmbedding Bf (inheritedSlotEmbedding B₂
        (⟨Subtype.val,Subtype.val_injective⟩:liveIndices B₁↪α))) :=
  (Admission.SelectedHighSlots.finalImage_eq_map B₁ B₂ Bf).trans
    (congrArg (fun e=>Finset.univ.map e) (selected_three_embedding B₁ B₂ Bf).symm)

/-- Only finite geometric source fields and one joint cofactor estimate remain
after selection; no individual child energy is used. -/
theorem uniform_selected_plain_newton (N:ℕ)(ε:ℝ)(hε:0<ε):
    ∃K₀:ℝ,0<K₀ ∧ ∀{α Row:Type}[Fintype α]
      (s:Input α)(rows:Finset Row)(reflected second:Bool)(first:Row→FirstSourceLabel)
      (R:Ideal O)(C₂ D₂ seed:Row→Ideal O)
      (B₁:∀r,actualAllocations s.pools (if reflected then (first r).1.2 else (first r).1.1))
      (τ₁:Row→Character)(t₁:Row→ℝ),
    Fintype.card α≤N→
    (∀r,frozenCoefficient (B₁ r).val (if reflected then (first r).1.2 else (first r).1.1)
      R s.ν s.W s.P≠0)→
    let s₁:=fun r=>child s (if reflected then (first r).1.2 else (first r).1.1) R (B₁ r) (τ₁ r) (t₁ r)
    let common:=fun r=>if second then D₂ r else C₂ r
    let parentR:=fun r=>R*(if reflected then (first r).1.2 else (first r).1.1)
    ∀(P:Finset (Ideal O))(L:Ideal O),Squarefree L→
    ∀(hC:∀r,Supported (common r)),(∀r,seed r∣common r)→
    ∀(τ:Row→Character)(t:Row→ℝ)(z:Row→O)(weight:Row→ℝ),(∀r∈rows,0≤weight r)→
    let energy:=fun r=>fixedPlainEnergy (s₁ r) ((B₁ r).val (Sum.inr 0)) ((B₁ r).val (Sum.inr 1))
      1 (markedProduct (B₁ r).val) (common r) (parentR r) (seed r) L (poolCorrection P) (hC r) (τ r) (t r) (z r)
    let live:=rows.filter (fun r=>energy r≠0)
    ∃sel:∀r:live,Selection s reflected second (first r) (C₂ r) (D₂ r) R,
      (∀r,(sel r).B₁=B₁ r ∧ (sel r).τ₁=τ₁ r ∧ (sel r).t₁=t₁ r ∧
        (sel r).τ₂=τ r ∧ (sel r).t₂=t r ∧ (sel r).τf=τ r ∧ (sel r).tf=t r ∧
        L∣(sel r).Cf ∧ (sel r).Cf∣L^2) ∧
    ∀(W₁ W₂:𝓢(ℝ,ℂ))(b Z BA Bpool:ℝ)(depth:ℕ)(E Bslot:ℝ),0≤E→1≤Bslot→
      (∀r,CorrectedSourceGeometry (sel r).finalInput W₁ W₂ b Z BA Bpool depth
        (Selection.frozenLeft (sel r)) (Selection.frozenRight (sel r)) (Selection.correction (sel r))
        (Selection.marked (sel r)) (Selection.puncture (sel r)) P)→
      (∀p∈P,Prime p)→(∀p∈P,16≤p.absNorm)→0<P.card→
      (∀i,1≤s.P i)→(∀i,∀p∈s.slots i,‖restoredSlotCoeff s i p‖≤Bslot)→
      (∀i,∀p∈s.slots i,(p.absNorm:ℝ)≤2*s.P i)→
      (∀S∈P.powerset.filter (fun S=>S.card≤depth),∀A∈S.powerset,∀T:Finset α,
        (∑r∈Finset.univ.filter (fun r:live=>T⊆(sel r).full),
          ‖newtonCofactorPlain (sel r).finalInput (Selection.frozenLeft (sel r))
            (Selection.frozenRight (sel r)) (Selection.puncture (sel r)) b S A (τ r) (t r) (z r)*
            (∏j:T,normalizedSlot (τ r) (fixedBadMask*idealGenerator (Selection.puncture (sel r))) 1 (z r)
              (s.slots j) (restoredSlotCoeff s j) (t r) (s.P j))‖^2*selectedPaidWeight (sel r) (weight r))≤E)→
      (∑r∈rows,energy r*weight r)≤K₀*((L.absNorm:ℝ)^ε/(L.absNorm:ℝ))*
        newtonMassBound depth^2*(collisionProjectionCost Bslot 256 N*((2:ℝ)^N*E)) := by
  obtain ⟨K₀,hK₀,hreduce⟩:=uniform_fixed_plain_newton_supported N ε hε
  refine ⟨K₀,hK₀,?_⟩
  intro α Row _ s rows reflected second first R C₂ D₂ seed B₁ τ₁ t₁ hN hf₁ s₁ common parentR
    P L hL hC hseed τ t z weight hw energy live
  let embedding:=fun r:Row=>(⟨Subtype.val,Subtype.val_injective⟩:liveIndices (B₁ r).val↪α)
  have hKR (r:Row):markedProduct (B₁ r).val∣parentR r:=by
    simpa only [one_mul] using marked_puncture_invariant 1 R
      (if reflected then (first r).1.2 else (first r).1.1) (B₁ r).val (one_dvd R)
      (Finset.mem_filter.mp (B₁ r).property).2
  obtain ⟨B₂,hf₂,pick,hpick,hbound⟩:=hreduce rows
    (fun r=>liveIndices (B₁ r).val) s₁ embedding s.slots (restoredSlotCoeff s) s.P hN
    (fun _ _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) P
    (fun r=>(B₁ r).val (Sum.inr 0)) (fun r=>(B₁ r).val (Sum.inr 1)) (fun _=>1)
    (fun r=>markedProduct (B₁ r).val) common parentR seed L hL hKR hC hseed τ t z weight hw
  let sel:∀r:live,Selection s reflected second (first r) (C₂ r) (D₂ r) R:=fun r=>
    { B₁:=B₁ r,τ₁:=τ₁ r,t₁:=t₁ r,hf₁:=hf₁ r,
      B₂:=B₂ r,τ₂:=τ r,t₂:=t r,hf₂:=hf₂ r,
      Cf:=(pick r).1,Bf:=(pick r).2,τf:=τ r,tf:=t r,hff:=(hpick r).1 }
  refine ⟨sel,fun r=>⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,(hpick r).2.2.1,(hpick r).2.2.2⟩,?_⟩
  intro W₁ W₂ b Z BA Bpool depth E Bslot hE hBslot hg hp hn hP hscale hcoeff hnorm hcofactor
  apply hbound depth (fun _=>b) E Bslot hE hBslot
    (fun r=>(hg r).frozen_left_ne) (fun r=>(hg r).frozen_right_ne)
    (fun r=>(hg r).support_left) (fun r=>(hg r).support_right) hp hn
    (fun r=>input_pool_avoids_marked (sel r).finalInput P hp (hg r).pool_avoids)
    (fun r=>corrected_geometry_newton_support (sel r).finalInput W₁ W₂ b Z BA Bpool depth
      (Selection.frozenLeft (sel r)) (Selection.frozenRight (sel r)) (Selection.correction (sel r))
      (Selection.marked (sel r)) (Selection.puncture (sel r)) P (hg r) (τ r) (t r) (z r))
    hP (fun r=>(hg r).pool_budget) hscale hcoeff s.prime hnorm
  intro S hS A hA T
  have himage (r:live):(sel r).full=
      Finset.univ.map (inheritedSlotEmbedding (pick r).2.val
        (inheritedSlotEmbedding (B₂ r).val (embedding r))) := by
    exact selected_three_image (B₁ r).val (B₂ r).val (pick r).2.val
  have hh:=hcofactor S hS A hA T
  simp_rw [himage] at hh
  simpa only [sel,Admission.SelectedHighCofactorFamily.Selection.finalInput,
    Admission.SelectedHighCofactorFamily.Selection.firstInput,
    Selection.frozenLeft,Selection.frozenRight,Selection.puncture,selectedPaidWeight,s₁,common,parentR,
    CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh


end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.uniform_selected_plain_newton
