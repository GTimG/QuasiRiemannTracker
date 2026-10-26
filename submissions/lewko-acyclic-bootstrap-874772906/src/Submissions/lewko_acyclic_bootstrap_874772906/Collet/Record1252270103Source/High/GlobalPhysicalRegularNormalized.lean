/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual kept complete family feeds the fixed-L normalized Newton reduction.
The one joint cofactor inlet is stated on its literal selected original rows. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalNormalizedNewtonRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularSourceData
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
open Admission Admission.SelectedRegularSourceData
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
local notation "O"=>HeckeFamily.O
local instance regularNormalizedDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

section Family
variable {α Label:Type}[Fintype α][Fintype Label]{Z:ℝ}{a:Anchor α Z}(F:Family a Label)

def regularKey (second:Bool)(r:F.Rows):NonzeroJointSourceLabel (!F.reflected) 1
    (fun l=>(Record12518109Raw.fixedParentUnit (!F.reflected) F.s.η l:O)):=
  FirstFamily.rawKey F.reflected F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin
    (F.column r.val.1.1) F.datum F.first r rfl second

def regularFirstAllocation (q:F.Complete):actualAllocations F.s.pools
    (if F.reflected then (F.first q).1.2 else (F.first q).1.1):=(F.stage q.1).B

theorem regular_datum_slots (q:F.Complete):
    (F.datum q).slots=liveIndices (regularFirstAllocation F q).val:=rfl

theorem regular_datum_input (q:F.Complete):
    HEq (F.datum q).input (child F.s
      (if F.reflected then (F.first q).1.2 else (F.first q).1.1) F.R
      (regularFirstAllocation F q) (F.stage q.1).τ (F.stage q.1).t):=HEq.rfl

theorem regular_datum_parent (q:F.Complete):
    (F.datum q).R=F.R*(if F.reflected then (F.first q).1.2 else (F.first q).1.1):=rfl

def regularModifier (P:Finset (Ideal O))(q:F.Complete):Tuple (F.datum q).slots→ℂ:=
  correctedModifier P ((F.stage q.1).B.val (Sum.inr 0)) ((F.stage q.1).B.val (Sum.inr 1))
    1 (markedProduct (F.stage q.1).B.val) (fun _=>1)

def regularRowRay (second:Bool)(r:F.Rows):RayFourExpansion.RayCharacter:=
  if second then r.val.2.2.1⁻¹ else r.val.2.1

/-- The source branches act on this one signed-key family, at one fixed L.
The original singleton subset is filtered before either branch is counted. -/
def RegularCofactorBound (second:Bool)(P:Finset (Ideal O))(depth:ℕ)
    (w:F.Complete→ℂ)(t u b Bres E:ℝ):Prop:=
  ∀{Row:Type}[Fintype Row](rows:Finset Row)(G:Selected F Row rows second),
    Function.Injective G.key→Squarefree G.L→(G.L.absNorm:ℝ)≤Z^Bres→
    (∀r,G.ψ r=regularRowRay F second (G.row r))→
    ∀S∈P.powerset.filter (fun S=>S.card≤depth),∀A∈S.powerset,∀T:Finset α,
      (∀r,T⊆(G.sel r).full)→
      (∑r:rows,‖newtonCofactorPlain (G.sel r).finalInput (Selection.frozenLeft (G.sel r))
        (Selection.frozenRight (G.sel r)) (Selection.puncture (G.sel r)) b S A
        (G.τ r) (residualHeight second F.datum t u (G.row r).val) (G.z r)*
        (∏j:T,normalizedSlot (G.τ r) (fixedBadMask*idealGenerator (Selection.puncture (G.sel r)))
          1 (G.z r) (F.s.slots j) (restoredSlotCoeff F.s j)
          (residualHeight second F.datum t u (G.row r).val) (F.s.P j))‖^2*
        selectedPaidWeight (G.sel r) (residualWeight F.datum w (G.row r).val))≤E

end Family

def RegularNormalizedAt (N:ℕ)(Bres δ ε C Z:ℝ)
    {α Label:Type}[Fintype α][Fintype Label](a:Anchor α Z)(F:Family a Label)(second:Bool):Prop:=
      Fintype.card α≤N→
      (∀l,frozenCoefficient (F.stage l).B.val (F.stage l).common F.R F.s.ν F.s.W F.s.P≠0)→
    ∀(P:Finset (Ideal O))(w:F.Complete→ℂ)(t u W:ℝ),0≤W→
      FullCostSelection (regularKey F false)
        (fun k=>if second then reflectedNonzeroJointLabel k else k) W→
      (∀r∈F.Rows,∀L∈secondResidualIdeals
        (fun q=>modifiedDatumBlock (F.datum q) (regularModifier F P q)) r,(L.absNorm:ℝ)≤Z^Bres)→
    ∀(W₁ W₂:𝓢(ℝ,ℂ))(b Bfirst Bsecond Bplain amp ell mesh loss Bsource:ℝ)
      (depth:ℕ)(E Bslot:ℝ),0≤E→1≤Bslot→
      F.s.W₁=(W₁:ℝ→ℂ)→F.s.W₂=(W₂:ℝ→ℂ)→F.s.b₁≤b→F.s.b₂≤b→0≤b→0<ell→
      (∀l,((F.stage l).common.absNorm:ℝ)≤Z^Bfirst)→
      (∀q:F.Complete,((if second then (F.datum q).D else (F.datum q).C).absNorm:ℝ)≤Z^Bsecond)→
      FixedCellPoolData P Z amp ell mesh loss (Bsecond+2*Bres) Bsource depth→
      (∀p∈P,∀i I,I∈F.s.slots i→¬p∣I)→Bplain/ell≤depth→b^2*(F.s.X₁*F.s.X₂)≤Z^Bplain→
      (∀i,1≤F.s.P i)→(∀i,∀p∈F.s.slots i,‖restoredSlotCoeff F.s i p‖≤Bslot)→
      (∀i,∀p∈F.s.slots i,(p.absNorm:ℝ)≤2*F.s.P i)→
      RegularCofactorBound F second P depth w t u b Bres E→
      modifiedSecondNormalizedSum second F.datum (regularModifier F P) w t u≤
        W*C*Z^(δ+Bres*ε)*newtonMassBound depth^2*
          (collisionProjectionCost Bslot 256 N*((2:ℝ)^N*E))

theorem actual_regular_normalized_newton_collection (N:ℕ)(Bres δ ε:ℝ)
    (hBres:0≤Bres)(hδ:0<δ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{α Label:Type}[Fintype α][Fintype Label](a:Anchor α Z)(F:Family a Label)(second:Bool),
      RegularNormalizedAt N Bres δ ε C Z a F second := by
  obtain ⟨C,hC,hbound⟩:=normalized_selected_newton_collection_rows N Bres δ ε hBres hδ hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α Label _ _ a F second hN hf P w t u W hW hselect hcap
    W₁ W₂ b Bfirst Bsecond Bplain amp ell mesh loss Bsource depth E Bslot hE hBs
    hW₁ hW₂ hb₁ hb₂ hb hell hfirst hsecond hpool havoid hdepth hplain hscale hcoeff hnorm hcofactor
  have hseed(q:F.Complete):(F.datum q).seed∣(F.datum q).C ∧ (F.datum q).seed∣(F.datum q).D:=by
    have h:=modified_retained_seed_and_caps (F.slots q.1) (F.input q.1) (F.childModifier q.1)
      (F.mask q.1) (F.childSeed q.1) (F.childSeed_sf q.1) F.zero₁ F.zero₂
      (F.Hmain q.1) (F.Tsec q.1) Z F.ξ (F.Hmain_pos q.1) q.2.val
    exact ⟨h.1,h.2.1⟩
  have h0:=hZ.2 (α:=α) (Label:=F.Complete)
    (Key:=NonzeroJointSourceLabel (!F.reflected) 1
      (fun l=>(Record12518109Raw.fixedParentUnit (!F.reflected) F.s.η l:O))) F.s F.reflected second F.first F.R (regularFirstAllocation F)
    (fun q=>(F.stage q.1).τ) (fun q=>(F.stage q.1).t) F.datum
  have h1:=h0 hN F.R_ne
    (regular_datum_slots F) (regular_datum_input F) (regular_datum_parent F) hseed (fun q=>hf q.1)
  have h2:=h1 P w t u W hW (regularKey F false) (fun k=>if second then reflectedNonzeroJointLabel k else k)
    hselect hcap
  apply h2 W₁ W₂ b Bfirst Bsecond Bplain amp ell mesh loss Bsource depth E Bslot hE hBs
    hW₁ hW₂ hb₁ hb₂ hb hell (fun q=>hfirst q.1) hsecond hpool havoid hdepth hplain hscale hcoeff hnorm
  intro Row _ row hinj L hL hLcap sel hsel S hS A hA T
  let rows:=Finset.univ.filter (fun r:Row=>T⊆(sel r).full)
  let G:Selected F Row rows second:={
    row:=fun r=>row r.val
    sel:=fun r=>sel r.val
    first_allocation:=fun r=>(hsel r.val).1
    ψ:=fun r=>regularRowRay F second (row r.val)
    L:=L
    L_ne:=hL.ne_zero
    forced_lower:=fun r=>(hsel r.val).2.2.2.1
    forced_upper:=fun r=>(hsel r.val).2.2.2.2 }
  have hkey:Function.Injective G.key:=by
    have heq:∀r,G.key r=(if second then reflectedNonzeroJointLabel (regularKey F false (row r.val))
      else regularKey F false (row r.val)):=by intro r;cases second <;> rfl
    intro r s hrs
    apply Subtype.ext
    apply hinj
    simpa only [←heq r,←heq s] using hrs
  have he:=hcofactor rows G hkey hL hLcap (fun _=>rfl) S hS A hA T
    (fun r=>(Finset.mem_filter.mp r.property).2)
  have hchar(r:rows):G.τ r=residualCharacter second F.datum (row r.val).val:=by
    cases second <;> rfl
  simp only [hchar] at he
  let value:Row→ℝ:=fun r=>‖newtonCofactorPlain (sel r).finalInput (Selection.frozenLeft (sel r))
    (Selection.frozenRight (sel r)) (Selection.puncture (sel r)) b S A
    (residualCharacter second F.datum (row r).val) (residualHeight second F.datum t u (row r).val)
    (residualPoint second F.datum (row r).val)*
    (∏j:T,normalizedSlot (residualCharacter second F.datum (row r).val)
      (fixedBadMask*idealGenerator (Selection.puncture (sel r))) 1
      (residualPoint second F.datum (row r).val) (F.s.slots j) (restoredSlotCoeff F.s j)
      (residualHeight second F.datum t u (row r).val) (F.s.P j))‖^2*
    selectedPaidWeight (sel r) (residualWeight F.datum w (row r).val)
  change (∑r:rows,value r.val)≤E at he
  simpa only [Finset.sum_coe_sort] using he

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_regular_normalized_newton_collection
