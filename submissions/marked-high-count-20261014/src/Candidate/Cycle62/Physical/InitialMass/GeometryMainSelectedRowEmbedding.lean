/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryMainLowPayment

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance mainSelectedRowEmbeddingSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
variable (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
variable (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)

/-- One selected first allocation per arithmetic-label/projector key embeds
into the literal ORIGINAL full-nonzero main family. The complete second
index, including all four dyads, is recovered by dependent sigma equality. -/
theorem main_low_selected_original_injective
    (hinj : Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val,
      (firstIndex l).1.val.2.1.val))) :
    Function.Injective (mainLowSelectedOriginal reflected s R seed Z Mrow amp ξ reserve b t
      N hZ key hz₁ hz₂ firstIndex) := by
  intro q r h
  have hb := congrArg Subtype.val h
  change (⟨firstIndex q.val.1,q.val.2⟩ :
    GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)=
      ⟨firstIndex r.val.1,r.val.2⟩ at hb
  have hf : firstIndex q.val.1=firstIndex r.val.1 := congrArg Sigma.fst hb
  have hl : q.val.1=r.val.1 := hinj (congrArg (fun j : GeometryLowFirstIndex reflected s R seed
    (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key=>
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.val,j.1.val.2.1.val)) hf)
  apply Subtype.ext
  exact Sigma.ext hl (Sigma.mk.inj_iff.mp hb).2

/-- The selected carrier uses the actual datum, before ordinary restriction. -/
def mainLowSelectedDatum
    (q : mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex) :
    SecondInputDatum α :=
  geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    (firstIndex q.val.1) hz₁ hz₂ q.val.2

theorem main_low_selected_original_datum
    (q : mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex) :
    geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      (mainLowSelectedOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex q).val.1
      hz₁ hz₂
      (mainLowSelectedOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex q).val.2=
    mainLowSelectedDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex q := rfl

/-- The same exact datum identity preserves both ordinary rays and their
original inducing exclusion. No nonzero ordinary block is required. -/
theorem main_low_selected_original_ordinary_datum
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (q : mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex) :
    geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m
      (mainLowSelectedOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex q).val=
    ordinarySecondDatum
      (mainLowSelectedDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex q) χ Q m := rfl


end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_selected_original_injective
#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_selected_original_datum
#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_selected_original_ordinary_datum
