/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A single concrete first-stage/complete-second family for both regular source callers. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedSecondPhase
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedSecondNaturalFamily
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedSecondKeyCaps
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSelectedNewton
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularSourceData
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open Cycle61Moment Cycle61InitialMass LocalMoment Record12518109Raw
open OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
open High.GlobalPhysical SecondSectorDatum SelectedSecondPhase SelectedSecondNatural SelectedHighCofactorFamily
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

structure Anchor (α:Type) [Fintype α](Z:ℝ) where
  s : Input α
  modifier : Tuple α→ℂ
  R : Ideal O
  seed : Ideal O
  R_ne : R≠0
  seed_sf : Squarefree seed
  zero₁ : s.W₁ 0=0
  zero₂ : s.W₂ 0=0
  D : ℝ
  ξ : ℝ
  reserve : ℝ
  hZ : 1<Z
  hK : 0<Z^D
  bin : ℤ×(Fin 5→ℤ)
  reflected : Bool
  Q : Ideal O
  m : O

namespace Anchor
variable {α:Type}[Fintype α]{Z:ℝ}(a:Anchor α Z)
def Column:=FirstColumnIndex (High.CoupledFirst.geometryFirstSource a.s a.modifier a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin)
def label (j:a.Column):FirstSourceLabel:=FirstFamily.firstLabel a.s a.modifier a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin j
def character (j:a.Column):Character:=FirstFamily.columnCharacter a.reflected a.s a.modifier a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin j
def childSeed (j:a.Column):Ideal O:=j.2.1.val
end Anchor

structure ColumnData {α:Type}[Fintype α](s:Input α)(reflected:Bool)
    (R seed:Ideal O)(l:FirstSourceLabel)(τ:Character) where
  stage : FirstStage s reflected R l
  stage_character : stage.τ=τ
  childModifier : Tuple (liveIndices stage.B.val)→ℂ
  childSeed_sf : Squarefree seed
  Tsec : ℝ
  amp : ℝ
  χ₀ : RayCharacter

structure Family {α:Type} [Fintype α]{Z:ℝ}(anchor:Anchor α Z)(Label:Type)[Fintype Label] where
  column : Label→anchor.Column
  data : ∀l,ColumnData anchor.s anchor.reflected anchor.R (anchor.childSeed (column l))
    (anchor.label (column l)) (anchor.character (column l))

namespace Family
variable {α Label:Type}[Fintype α][Fintype Label]{Z:ℝ}{a:Anchor α Z}(F:Family a Label)
abbrev anchor (_F:Family a Label) := a
abbrev s := F.anchor.s
abbrev modifier := F.anchor.modifier
abbrev R := F.anchor.R
abbrev seed := F.anchor.seed
abbrev R_ne := F.anchor.R_ne
abbrev seed_sf := F.anchor.seed_sf
abbrev zero₁ := F.anchor.zero₁
abbrev zero₂ := F.anchor.zero₂
abbrev D := F.anchor.D
abbrev ξ := F.anchor.ξ
abbrev reserve := F.anchor.reserve
abbrev hZ := F.anchor.hZ
abbrev hK := F.anchor.hK
abbrev bin := F.anchor.bin
abbrev reflected := F.anchor.reflected
abbrev Q := F.anchor.Q
abbrev m := F.anchor.m
abbrev stage (l:Label) := (F.data l).stage
abbrev stage_character (l:Label) := (F.data l).stage_character
abbrev childModifier (l:Label) := (F.data l).childModifier
abbrev childSeed_sf (l:Label) := (F.data l).childSeed_sf
abbrev Tsec (l:Label) := (F.data l).Tsec
abbrev amp (l:Label) := (F.data l).amp
abbrev χ₀ (l:Label) := (F.data l).χ₀
def slots (l:Label):Finset α:=liveIndices (F.stage l).B.val
def input (l:Label):Input (F.slots l):=(F.stage l).input
def mask (l:Label):Ideal O:=F.R*(F.stage l).common
def childSeed (l:Label):Ideal O:=(F.column l).2.1.val
def Hmain (l:Label):ℝ:=(F.stage l).height Z F.D (F.amp l) F.ξ F.reserve
theorem Hmain_pos (l:Label):0<F.Hmain l:=
  (F.stage l).height_pos Z F.D (F.amp l) F.ξ F.reserve (zero_lt_one.trans F.hZ)
abbrev Complete:=CompleteFamily F.slots F.input F.childModifier F.mask F.childSeed ballProfile
  F.Hmain F.Tsec (fun _=>Z) (fun _=>F.ξ)
def datum (q:F.Complete):SecondInputDatum α:=
  regularDatum F.slots F.input F.childModifier F.mask F.childSeed F.Hmain F.Tsec Z F.ξ ballProfile
    F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos F.χ₀ F.Q F.m q
def first (q:F.Complete):FirstSourceLabel:=
  FirstFamily.firstLabel F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin (F.column q.1)
abbrev Rows:=secondLiveRows (fun q=>(F.datum q).block)
theorem mask_ne (l:Label):F.mask l≠0:=mul_ne_zero F.R_ne
  (allocation_ne F.s (F.stage l).common (F.stage l).B)
theorem datum_fields (q:F.Complete):
    (F.datum q).input=F.input q.1 ∧ (F.datum q).R=F.mask q.1 ∧
    (F.datum q).K=F.Hmain q.1 ∧ (F.datum q).radius=frequencyRadius (F.Tsec q.1) Z F.ξ ∧
    (F.datum q).seed=F.childSeed q.1:=⟨rfl,rfl,rfl,rfl,rfl⟩
theorem parent_character (q:F.Complete):
    (F.datum q).input.η=FirstFamily.columnCharacter F.reflected F.s F.modifier F.R F.seed
      (Z^F.D) Z F.ξ F.hK F.bin (F.column q.1):=F.stage_character q.1
end Family

structure Selected {α Label:Type}[Fintype α][Fintype Label]{Z:ℝ}
    {a:Anchor α Z}(F:Family a Label)(Row:Type)(rows:Finset Row)(second:Bool) where
  row : rows→F.Rows
  sel : ∀u,Selection F.s F.reflected second (F.first (row u).val.1)
    (F.datum (row u).val.1).C (F.datum (row u).val.1).D F.R
  first_allocation : ∀u,(sel u).B₁=(F.stage (row u).val.1.1).B
  ψ : rows→RayCharacter
  L : Ideal O
  L_ne : L≠0
  forced_lower : ∀u,L∣(sel u).Cf
  forced_upper : ∀u,(sel u).Cf∣L^2

namespace Selected
variable {α Label Row:Type}[Fintype α][Fintype Label]{Z:ℝ}{a:Anchor α Z}{F:Family a Label}
    {rows:Finset Row}{second:Bool}(G:Selected F Row rows second)
def column (u:rows):FirstColumnIndex (High.CoupledFirst.geometryFirstSource F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin):=
  F.column (G.row u).val.1.1
def datum (u:rows):SecondInputDatum α:=F.datum (G.row u).val.1
def z (u:rows):O:=if second then -(G.row u).val.2.2.2.val else (G.row u).val.2.2.2.val
def τ (u:rows):Character:=(G.datum u).τ (G.ψ u)
def key (u:rows):NonzeroJointSourceLabel (!F.reflected) 1
    (fun l=>(fixedParentUnit (!F.reflected) F.s.η l:O)):=
  FirstFamily.rawKey F.reflected F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin
    (G.column u) F.datum F.first (G.row u) rfl second
def extra (S A:Finset (Ideal O))(u:rows):Ideal O:=
  (G.sel u).Cf*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)
def x (err errv annular:ℝ)(w:α→ℝ)(wmin:ℝ)(T:Finset α)(u:rows):Fin 4→ℝ:=
  (G.sel u).coordinate (G.datum u).inactive Z F.D (F.amp (G.row u).val.1.1) F.ξ F.reserve
    err errv annular w wmin T

theorem structural (u:rows):
    (G.datum u).input.η=FirstFamily.columnCharacter F.reflected F.s F.modifier F.R F.seed
      (Z^F.D) Z F.ξ F.hK F.bin (G.column u) ∧
    F.first (G.row u).val.1=FirstFamily.firstLabel F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin (G.column u) ∧
    (G.datum u).R=F.R*FirstFamily.columnIdeal F.reflected F.s F.modifier F.R F.seed
      (Z^F.D) Z F.ξ F.hK F.bin (G.column u) ∧ (G.datum u).R≠0 := by
  refine ⟨F.parent_character _,rfl,?_,F.mask_ne _⟩
  rfl

theorem selected_puncture (S A:Finset (Ideal O))(u:rows):
    enlargedRetainedPuncture (G.datum u) second (G.extra S A u)=
      High.GlobalPhysical.Selection.puncture (G.sel u)*
        ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2) := by
  dsimp only [enlargedRetainedPuncture,extra,High.GlobalPhysical.Selection.puncture]
  change (((F.R*(F.stage (G.row u).val.1.1).common)*
    (if second then (G.datum u).D else (G.datum u).C))*
    ((G.sel u).Cf*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)))=_
  simp only [FirstStage.common,Family.first,mul_assoc]
  rfl

end Selected
end
end QRH.Record1252270103Source.Admission.SelectedRegularSourceData
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularSourceData.Family.Hmain_pos
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularSourceData.Family.mask_ne
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularSourceData.Family.datum_fields
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularSourceData.Family.parent_character
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularSourceData.Selected.structural
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularSourceData.Selected.selected_puncture
