/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One original-key selection, one fixed residual ideal and one joint Newton
family feed the literal normalized second sum. The cofactor inlet below is
explicit; the genuine LOW/HIGH source estimates supply it at the caller. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalNormalizedCollection
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSelectedNewtonGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalResidualDictionary
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
local instance normalizedNewtonDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

def residualCharacter {α Label:Type}[Fintype α](second:Bool)(d:Label→SecondInputDatum α)
    (r:SecondRow (fun l=>(d l).block)):Character :=
  if second then (d r.1).τ r.2.2.1⁻¹ else (d r.1).τ r.2.1
def residualHeight {α Label:Type}[Fintype α](second:Bool)(d:Label→SecondInputDatum α)
    (t u:ℝ)(r:SecondRow (fun l=>(d l).block)):ℝ :=
  (d r.1).input.t+2*Real.pi*(u-(if second then -t else t))
def residualPoint {α Label:Type}[Fintype α](second:Bool)(d:Label→SecondInputDatum α)
    (r:SecondRow (fun l=>(d l).block)):O :=
  if second then -r.2.2.2.val else r.2.2.2.val
def residualWeight {α Label:Type}[Fintype α](d:Label→SecondInputDatum α)(w:Label→ℂ)
    (r:SecondRow (fun l=>(d l).block)):ℝ :=
  ‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData

theorem residualWeight_nonneg {α Label:Type}[Fintype α](d:Label→SecondInputDatum α)
    (w:Label→ℂ)(r:SecondRow (fun l=>(d l).block)):0≤residualWeight d w r :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (second_outside_pos _).le)
    (CenteredMomentExceptionalAmplitudePair.volume_pos _).le

theorem normalized_selected_newton_collection (N:ℕ)(Bres δ ε:ℝ)
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
    let rows:=secondLiveRows blocks
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
  obtain ⟨Ccollect,hCcollect,hcollect⟩:=normalized_fixed_key_collection Bres δ hBres hδ
  obtain ⟨Cnewton,hCnewton,hnewton⟩:=uniform_selected_plain_newton N ε hε
  refine ⟨Ccollect*Cnewton,mul_pos hCcollect hCnewton,?_⟩
  filter_upwards [hcollect] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α Label Key _ _ _ s reflected second first R B₁ τ₁ t₁ d hN hR hslots hinput hparentR hseed hf₁
    P w t u W hW A₁ A₂ K modifier blocks rows key transform hselect hcap
    W₁ W₂ b Bfirst Bsecond Bplain amp ell mesh loss Bsource depth E Bslot hE hBslot
    hW₁ hW₂ hb₁ hb₂ hb hell hfirst hsecond hpool havoid hdepth hplain hscale hcoeff hnorm hcofactor
  let total:=Cnewton*newtonMassBound depth^2*(collisionProjectionCost Bslot 256 N*((2:ℝ)^N*E))
  have htotal:0≤total:=by
    have hc:0≤collisionProjectionCost Bslot 256 N:=by unfold collisionProjectionCost;positivity
    dsimp only [total]
    positivity
  have hc:=hZ.2 second d P A₁ A₂ (fun _=>1) K w t u W ε total hW hε.le htotal
    key transform hselect hcap ?_
  · apply hc.trans_eq
    dsimp only [total]
    ring
  let labels := Finset.univ.image key
  intro pick hpick hinj L hL
  obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hL
  have hsf:Squarefree L:=((mem_second_residual_ideals blocks (pick j).val L).mp hj).2
  have hLcap:(L.absNorm:ℝ)≤Z^Bres:=hcap (pick j).val (pick j).property L hj
  let rowsL:=Finset.univ.filter (fun j:labels=>L∈secondResidualIdeals blocks (pick j).val)
  let first':=fun j:labels=>first (pick j).val.1
  let C₂:=fun j:labels=>(d (pick j).val.1).C
  let D₂:=fun j:labels=>(d (pick j).val.1).D
  have hC (j:labels):Supported (if second then D₂ j else C₂ j):=by
    cases second
    · exact (d (pick j).val.1).hC
    · exact (d (pick j).val.1).hD
  have hseed' (j:labels):(d (pick j).val.1).seed∣(if second then D₂ j else C₂ j):=by
    cases second
    · exact (hseed _).1
    · exact (hseed _).2
  let energy := fun r:labels =>
    fixedPlainEnergy (child s (if reflected then (first' r).1.2 else (first' r).1.1)
      R (B₁ (pick r).val.1) (τ₁ (pick r).val.1) (t₁ (pick r).val.1))
      (A₁ (pick r).val.1) (A₂ (pick r).val.1) 1 (K (pick r).val.1)
      (if second then D₂ r else C₂ r) (R*(if reflected then (first' r).1.2 else (first' r).1.1))
      (d (pick r).val.1).seed L (poolCorrection P) (hC r)
      (residualCharacter second d (pick r).val) (residualHeight second d t u (pick r).val)
      (residualPoint second d (pick r).val)
  let live := rowsL.filter (fun r=>energy r≠0)
  obtain ⟨sel,hsel,hbound⟩:=hnewton s rowsL reflected second first' R C₂ D₂
    (fun j=>(d (pick j).val.1).seed) (fun j=>B₁ (pick j).val.1)
    (fun j=>τ₁ (pick j).val.1) (fun j=>t₁ (pick j).val.1) hN (fun j=>hf₁ _)
    P L hsf hC hseed'
    (fun j=>residualCharacter second d (pick j).val) (fun j=>residualHeight second d t u (pick j).val)
    (fun j=>residualPoint second d (pick j).val) (fun j=>residualWeight d w (pick j).val)
    (fun j _=>residualWeight_nonneg d w (pick j).val)
  have hgeometry : ∀ r, CorrectedSourceGeometry (sel r).finalInput W₁ W₂ b Z
      (Bfirst+Bsecond+2*Bres) amp depth (Selection.frozenLeft (sel r))
      (Selection.frozenRight (sel r)) (Selection.correction (sel r))
      (Selection.marked (sel r)) (Selection.puncture (sel r)) P := by
    intro r
    exact actual_selected_newton_geometry s reflected second (first' r.val) (C₂ r.val) (D₂ r.val) R
      (sel r) W₁ W₂ b Z Bfirst Bsecond Bres Bplain amp ell mesh loss Bsource depth P L
      hR hsf (hsel r).2.2.2.2.2.2.2.2 (hfirst _) (hsecond _) hLcap
      hW₁ hW₂ hb₁ hb₂ hb hell hpool havoid hdepth hplain
  have hbnd:=hbound W₁ W₂ b Z (Bfirst+Bsecond+2*Bres) amp depth E Bslot hE hBslot
    hgeometry hpool.prime (fun p hp=>by exact_mod_cast hpool.norm_ge_sixteen p hp)
    (Finset.card_pos.mpr hpool.nonempty) hscale hcoeff hnorm ?_
  · have heq:(∑r∈rowsL,correctedResidualTerm second d P A₁ A₂ (fun _=>1) K w t u (pick r).val L)=
        (∑r∈rowsL,
          fixedPlainEnergy (child s (if reflected then (first' r).1.2 else (first' r).1.1)
            R (B₁ (pick r).val.1) (τ₁ (pick r).val.1) (t₁ (pick r).val.1))
            (A₁ (pick r).val.1) (A₂ (pick r).val.1) 1 (K (pick r).val.1)
            (if second then D₂ r else C₂ r) (R*(if reflected then (first' r).1.2 else (first' r).1.1))
            (d (pick r).val.1).seed L (poolCorrection P) (hC r)
            (residualCharacter second d (pick r).val) (residualHeight second d t u (pick r).val)
            (residualPoint second d (pick r).val)*residualWeight d w (pick r).val):=by
      apply Finset.sum_congr rfl
      intro r _
      exact corrected_residual_first_child s reflected second first R B₁ τ₁ t₁ d hslots hinput hparentR P w t u (pick r).val L
    change (∑r∈rowsL,correctedResidualTerm second d P A₁ A₂ (fun _=>1) K w t u (pick r).val L)≤_
    rw [heq]
    apply hbnd.trans_eq
    dsimp only [total]
    ring
  intro S hS A hA T
  have hsrel := fun r =>
    And.intro (hsel r).1 (And.intro (hsel r).2.1 (And.intro (hsel r).2.2.1
      (And.intro (hsel r).2.2.2.2.2.2.2.1 (hsel r).2.2.2.2.2.2.2.2)))
  have hh := hcofactor (fun r:live=>pick r.val) (hinj.comp Subtype.val_injective) L hsf hLcap sel hsrel S hS A hA T
  exact hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.normalized_selected_newton_collection
