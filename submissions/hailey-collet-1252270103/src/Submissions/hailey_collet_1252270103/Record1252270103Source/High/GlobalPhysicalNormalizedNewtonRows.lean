/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One original-key selection, one fixed residual ideal and one joint Newton
family feed the literal normalized second sum. The cofactor inlet below is
explicit; the genuine LOW/HIGH source estimates supply it at the caller. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalNormalizedNewton
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentSecondHeightFamily CenteredMomentHeckeExpansion CenteredMomentCanonicalFirst
open CenteredMomentExceptionalAmplitudePair CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open Cycle61InitialMass Cycle61Moment OAI.SevenEighths.Record1252270103Source
open Record1252270103Second SecondRemainder Collision
open Admission.SelectedHighCofactorFamily Admission.ModifiedFibers Pool
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
local notation "O"=>HeckeFamily.O
local instance normalizedNewtonRowsDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

theorem normalized_selected_newton_collection_rows (N:ℕ)(Bres δ ε:ℝ)
    (hBres:0≤Bres)(hδ:0<δ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{α Label Key:Type}[Fintype α][Fintype Label][DecidableEq Key]
      (s:Input α)(reflected second:Bool)(first:Label→FirstSourceLabel)(R:Ideal O)
      (B₁:∀l,actualAllocations s.pools (if reflected then (first l).1.2 else (first l).1.1))
      (τ₁:Label→Character)(t₁:Label→ℝ)(d:Label→SecondInputDatum α),
    Fintype.card α≤N→R≠0→
    (∀l,(d l).slots=liveIndices (B₁ l).val)→
    (∀l,HEq (d l).input (child s (if reflected then (first l).1.2 else (first l).1.1) R (B₁ l) (τ₁ l) (t₁ l)))→
    (∀l,(d l).R=R*(if reflected then (first l).1.2 else (first l).1.1))→
    (∀l,(d l).seed∣(d l).C ∧ (d l).seed∣(d l).D)→
    (∀l,frozenCoefficient (B₁ l).val (if reflected then (first l).1.2 else (first l).1.1)
      R s.ν s.W s.P≠0)→
    ∀(P:Finset (Ideal O))(w:Label→ℂ)(t u W:ℝ),0≤W→
    let A₁:=fun l=>(B₁ l).val (Sum.inr 0)
    let A₂:=fun l=>(B₁ l).val (Sum.inr 1)
    let K:=fun l=>markedProduct (B₁ l).val
    let modifier:∀l,Tuple (d l).slots→ℂ:=fun l=>correctedModifier P (A₁ l) (A₂ l) 1 (K l) (fun _=>1)
    let blocks:=fun l=>modifiedDatumBlock (d l) (modifier l)
    let rows:=secondLiveRows (fun l=>(d l).block)
    ∀(key:rows→Key)(transform:Key→Key),FullCostSelection key transform W→
    (∀r∈rows,∀L∈secondResidualIdeals blocks r,(L.absNorm:ℝ)≤Z^Bres)→
    ∀(W₁ W₂:𝓢(ℝ,ℂ))(b Bfirst Bsecond Bplain amp ell mesh loss Bsource:ℝ)
      (depth:ℕ)(E Bslot:ℝ),0≤E→1≤Bslot→
    s.W₁=(W₁:ℝ→ℂ)→s.W₂=(W₂:ℝ→ℂ)→s.b₁≤b→s.b₂≤b→0≤b→0<ell→
    (∀l,((if reflected then (first l).1.2 else (first l).1.1).absNorm:ℝ)≤Z^Bfirst)→
    (∀l,((if second then (d l).D else (d l).C).absNorm:ℝ)≤Z^Bsecond)→
    FixedCellPoolData P Z amp ell mesh loss (Bsecond+2*Bres) Bsource depth→
    (∀p∈P,∀i I,I∈s.slots i→¬p∣I)→Bplain/ell≤depth→b^2*(s.X₁*s.X₂)≤Z^Bplain→
    (∀i,1≤s.P i)→(∀i,∀p∈s.slots i,‖restoredSlotCoeff s i p‖≤Bslot)→
    (∀i,∀p∈s.slots i,(p.absNorm:ℝ)≤2*s.P i)→
    (∀{Row:Type}[Fintype Row](row:Row → rows),Function.Injective (fun r=>transform (key (row r)))→
      ∀L:Ideal O,Squarefree L→(L.absNorm:ℝ)≤Z^Bres→
      ∀sel:∀r,Selection s reflected second (first (row r).val.1)
        (d (row r).val.1).C (d (row r).val.1).D R,
      (∀r,(sel r).B₁=B₁ (row r).val.1 ∧ (sel r).τ₁=τ₁ (row r).val.1 ∧
        (sel r).t₁=t₁ (row r).val.1 ∧ L∣(sel r).Cf ∧ (sel r).Cf∣L^2)→
      ∀S∈P.powerset.filter (fun S=>S.card≤depth),∀A∈S.powerset,∀T:Finset α,
        (∑r∈Finset.univ.filter (fun r:Row=>T⊆(sel r).full),
          ‖newtonCofactorPlain (sel r).finalInput (Selection.frozenLeft (sel r))
            (Selection.frozenRight (sel r)) (Selection.puncture (sel r)) b S A
            (residualCharacter second d (row r).val) (residualHeight second d t u (row r).val)
            (residualPoint second d (row r).val)*
            (∏j:T,normalizedSlot (residualCharacter second d (row r).val)
              (fixedBadMask*idealGenerator (Selection.puncture (sel r))) 1 (residualPoint second d (row r).val)
              (s.slots j) (restoredSlotCoeff s j) (residualHeight second d t u (row r).val) (s.P j))‖^2*
            selectedPaidWeight (sel r) (residualWeight d w (row r).val))≤E)→
    modifiedSecondNormalizedSum second d modifier w t u≤
      W*C*Z^(δ+Bres*ε)*newtonMassBound depth^2*
        (collisionProjectionCost Bslot 256 N*((2:ℝ)^N*E)) := by
  exact normalized_selected_newton_collection N Bres δ ε hBres hδ hε

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.normalized_selected_newton_collection_rows
