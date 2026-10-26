/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.SelectedRegularFibersGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Low.SelectedRegularFibers
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT CanonicalRowCompletion CenteredMomentFirstScale
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSourceConductorCaps CenteredMomentSecondLiveBlock
open Cycle61Moment Cycle61InitialMass Record1252270103Second
open Admission Admission.SelectedRegularSourceData Admission.ModifiedFibers Admission.SelectedSecondFibers
open High.GlobalPhysical CenteredMomentFirstAmplificationChoice
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

/-- The genuine finite selector required by the actual regular normalized
Newton collection. The frequency and row support gates are derived internally
on the complete original modified family, before keep and zero restriction. -/
theorem eventual_regular_full_cost_selection (A D₀ B Bfirst L Cr ε:ℝ)
    (hA:0≤A)(hD:0≤D₀)(hB:0≤B)(hBfirst:0≤Bfirst)(hL:0≤L)(hCr:0<Cr)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1≤Z ∧
    ∀{α Label:Type}[Fintype α][Fintype Label](a:Anchor α Z)(F:Family a Label),
    Function.Injective (fun l=>FirstAllocationSelection.columnKey F.s F.modifier F.R F.seed
      (Z^F.D) Z F.ξ F.hK F.bin (F.column l))→
    (∀l,Z^(-D₀)≤F.Hmain l)→(∀l,F.Hmain l≤Z^A)→
    (∀l,frequencyRadius (F.Tsec l) Z F.ξ≤Cr*Z^L)→
    (∀l,sourceRadius (F.input l)≤Z^B)→sourceRadius F.s≤Z^Bfirst→
    ∀second:Bool,FullCostSelection (regularKey F false)
      (fun k=>if second then reflectedNonzeroJointLabel k else k) (C*Z^ε):=by
  obtain ⟨C,hC,hselect⟩:=selected_second_restricted_full_cost_selection A D₀ B L Cr (6*Bfirst+L+1) ε
    hA hD hB hL hCr (by positivity) hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hselect,eventually_ge_atTop (4*Cr)] with Z hs hlarge
  refine ⟨hs.1,?_⟩
  intro α Label instα instLabel a F hinj hKlo hKhi hrad hsource hparent second
  have hfirst:=original_first_key_injective F hinj
  have hf:=original_first_frequency_nonzero F
  have hrow:=original_joint_row_cap F Bfirst L Cr hparent hrad hlarge
  have hh:=hs.2 F.slots F.input F.childModifier F.mask F.childSeed F.Hmain F.Tsec F.ξ
    F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂) F.Hmain_pos
    (fun l=>a.label (F.column l)) hfirst hKlo hKhi hrad hsource
    (!F.reflected) 1 (originalUnit F) hf hrow ballProfile
    (SelectedSecondNatural.regularKeep F.slots F.input F.childModifier F.mask F.childSeed
      F.Hmain F.Tsec Z F.ξ F.χ₀ F.Q F.m) second
  exact hh

end
end QRH.Record1252270103Source.Low.SelectedRegularFibers
#print axioms QRH.Record1252270103Source.Low.SelectedRegularFibers.eventual_regular_full_cost_selection
