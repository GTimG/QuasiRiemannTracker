/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighFinalPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainSelectedRowEmbedding

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedRows
open CenteredMomentSecondRetainedAggregate
open CenteredMomentFirstSourceReduction Cycle63Moment

attribute [local irreducible] Finset.univ
section ActualCharacter
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance affineHighSelectedSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z D amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
variable (bin : ℤ×(Fin 5→ℤ)) (hs₁ : s.W₁ 0=0) (hs₂ : s.W₂ 0=0)
variable (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin)
local notation "Selected" => mainLowSelectedNonzeroRows reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂ firstIndex
local notation "Original" => geometryMainNonzeroBlocks reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂
local notation "embed" => mainLowSelectedOriginal reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂ firstIndex

variable (hinj : Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^D) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin (firstIndex l).1.val,
  (firstIndex l).1.val.2.1.val)))

end ActualCharacter

section LiveRows
variable {α Selected Original : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Selected] [Fintype Original]
variable (datum : Original→SecondInputDatum α) (embed : Selected→Original)

theorem affine_high_selected_live_injective (hinj : Function.Injective embed) :
    Function.Injective (highSelectedLiveRowEmbedding datum embed) := by
  intro r v h
  apply Subtype.ext
  exact high_selected_row_embedding_injective datum embed hinj (congrArg Subtype.val h)

/-- Nonzero joint-key evidence is proof irrelevant. The exact original
key, including either reflected side, agrees with the selected key. -/
theorem affine_high_selected_live_reflected_key (first : Original→FirstSourceLabel)
    (r : secondLiveRows (fun j=>(datum (embed j)).block))
    (left second : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (hOriginal : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun j=>(datum j).block) first
        (highSelectedLiveRowEmbedding datum embed r))≠0)
    (hSelected : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun j=>(datum (embed j)).block) (fun j=>first (embed j)) r)≠0) :
    (if second then reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun j=>(datum j).block) first
        (highSelectedLiveRowEmbedding datum embed r) left u₀ unit hOriginal)
      else secondEncodedNonzeroRow (fun j=>(datum j).block) first
        (highSelectedLiveRowEmbedding datum embed r) left u₀ unit hOriginal)=
    (if second then reflectedNonzeroJointLabel
      (secondEncodedNonzeroRow (fun j=>(datum (embed j)).block) (fun j=>first (embed j)) r
        left u₀ unit hSelected)
      else secondEncodedNonzeroRow (fun j=>(datum (embed j)).block) (fun j=>first (embed j)) r
        left u₀ unit hSelected) := by
  have hk := high_selected_live_nonzero_key datum embed first r left u₀ unit hOriginal hSelected
  cases second with
  | false => exact hk
  | true => exact congrArg reflectedNonzeroJointLabel hk
end LiveRows

end
end OAI.SevenEighths.Cycle63InitialMass
