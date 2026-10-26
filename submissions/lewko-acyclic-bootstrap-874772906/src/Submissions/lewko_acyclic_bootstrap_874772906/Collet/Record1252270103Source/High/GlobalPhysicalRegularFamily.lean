/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The columns and allocations returned by the first MAIN selection construct
one literal regular second family, with a common first Mellin height. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularPhase
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalScalar CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentLogDyadic RayFourExpansion
open Cycle61InitialMass Cycle61Moment Record1252270103Second
open SecondRemainder
open Admission OAI.SevenEighths.Record1252270103Source.Collision
open Admission.SelectedRegularSourceData Admission.SelectedSecondPhase
local notation "O"=>HeckeFamily.O
local instance regularFamilyDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

variable {α Label:Type}[Fintype α][Fintype Label]{Z:ℝ}(a:Anchor α Z)
variable (column:Label→a.Column)
variable (hLive:∀l,column l∈firstLiveColumns
  (CoupledFirst.geometryFirstSource a.s a.modifier a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin)
  (fun _=>logAnnulus))
variable (alloc:∀l,actualAllocations a.s.pools
  (FirstFamily.columnIdeal a.reflected a.s a.modifier a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin (column l)))
variable (P:Finset (Ideal O))(amp ht:ℝ)(N:ℕ)(χ₀:Label→RayCharacter)

def allocatedRegularFamily:Family a Label where
  column:=column
  data l:={
    stage:={ B:=alloc l,τ:=a.character (column l),t:=ht }
    stage_character:=rfl
    childModifier:=correctedModifier P ((alloc l).val (Sum.inr 0)) ((alloc l).val (Sum.inr 1))
      1 (markedProduct (alloc l).val) (fun _=>1)
    childSeed_sf:=FirstFamily.live_projector_squarefree a.s a.modifier a.R a.seed (Z^a.D) Z a.ξ a.hK a.bin
      (fun _=>logAnnulus) (column l) (hLive l)
    Tsec:=firstMainFourierScale a.reflected (Z^a.D) (volume a.s) Z a.ξ (3*amp) a.reserve 2 N (a.label (column l))
    amp:=amp
    χ₀:=χ₀ l }

local notation "F"=>allocatedRegularFamily a column hLive alloc P amp ht N χ₀

theorem allocated_regular_fields (l:Label):
    ((F).stage l).B=alloc l ∧ ((F).stage l).t=ht ∧ (F).amp l=amp ∧
    (F).input l=child a.s (FirstFamily.columnIdeal a.reflected a.s a.modifier a.R a.seed
      (Z^a.D) Z a.ξ a.hK a.bin (column l)) a.R (alloc l) (a.character (column l)) ht ∧
    (F).mask l=a.R*FirstFamily.columnIdeal a.reflected a.s a.modifier a.R a.seed
      (Z^a.D) Z a.ξ a.hK a.bin (column l) ∧
    (F).Hmain l=firstMainRadius a.reflected (Z^a.D) (volume a.s) Z a.ξ (3*amp) a.reserve (a.label (column l)) ∧
    (F).Tsec l=firstMainFourierScale a.reflected (Z^a.D) (volume a.s) Z a.ξ (3*amp) a.reserve 2 N (a.label (column l)):=by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem allocated_regular_modifier (q:(F).Complete):
    regularModifier F P q=(F).childModifier q.1:=rfl

theorem allocated_regular_residual_height (second:Bool)(t u:ℝ)(r:(F).Rows):
    residualHeight second (F).datum t u r.val=mellinShift ht second t u:=
  regular_common_residual_height F ht t u second (fun _=>rfl) r

/-- The genuine first column key is exactly the pair required by the
modified second-fiber count. No first choice or ray multiplicity is dropped. -/
theorem allocated_regular_first_injective
    (hinj:Function.Injective (fun l=>(a.label (column l),(column l).2.1.val))):
    Function.Injective (fun l=>(a.label ((F).column l),(F).childSeed l)):=hinj

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.allocated_regular_fields
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.allocated_regular_modifier
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.allocated_regular_residual_height
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.allocated_regular_first_injective
