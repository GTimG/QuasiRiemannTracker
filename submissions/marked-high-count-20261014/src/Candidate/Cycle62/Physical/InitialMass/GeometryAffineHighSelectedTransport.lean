/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryMainHighFinalPayment
import Candidate.Cycle62.Physical.InitialMass.GeometryMainSelectedRowEmbedding

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedRows
open CenteredMomentSecondRetainedAggregate
open CenteredMomentFirstSourceReduction Cycle62Moment
local notation "O" => HeckeFamily.O

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

/-- Extend the selected inducing ray to the full ORIGINAL nonzero family.
The value off the image is only a total-function default. -/
def affineHighSelectedOriginalCharacter (χ₀ : Selected→RayCharacter) : Original→RayCharacter :=
  Function.extend embed χ₀ (fun _=>1)

variable (hinj : Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^D) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin (firstIndex l).1.val,
  (firstIndex l).1.val.2.1.val)))

include hinj in
theorem affine_high_selected_original_character_apply (χ₀ : Selected→RayCharacter) (q : Selected) :
    affineHighSelectedOriginalCharacter reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂
      firstIndex χ₀ (embed q)=χ₀ q := by
  exact (main_low_selected_original_injective reflected s R seed Z D amp ξ reserve b t N hZ
    bin hs₁ hs₂ firstIndex hinj).extend_apply χ₀ (fun _=>1) q

/-- The pullback is used as the selected ordinary family, so its row lift
has no dependent casts. The next theorem identifies the literal selected datum. -/
def affineHighSelectedOriginalDatum (χ₀ : Selected→RayCharacter) (Q : Ideal O) (m : O)
    (q : Original) : SecondInputDatum α :=
  geometryMainOrdinaryDatum reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂
    (affineHighSelectedOriginalCharacter reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂
      firstIndex χ₀ q) Q m q.val

include hinj in
theorem affine_high_selected_original_datum_apply (χ₀ : Selected→RayCharacter)
    (Q : Ideal O) (m : O) (q : Selected) :
    affineHighSelectedOriginalDatum reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂
      firstIndex χ₀ Q m (embed q)=
    ordinarySecondDatum
      (mainLowSelectedDatum reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂ firstIndex q)
      (χ₀ q) Q m := by
  unfold affineHighSelectedOriginalDatum
  rw [affine_high_selected_original_character_apply reflected s R seed Z D amp ξ reserve b t N
    hZ bin hs₁ hs₂ firstIndex hinj χ₀ q]
  exact main_low_selected_original_ordinary_datum reflected s R seed Z D amp ξ reserve b t N hZ
    bin hs₁ hs₂ firstIndex (χ₀ q) Q m q

include hinj in
theorem affine_high_selected_ordinary_family_eq (χ₀ : Selected→RayCharacter) (Q : Ideal O) (m : O) :
    (fun q : Selected=>affineHighSelectedOriginalDatum reflected s R seed Z D amp ξ reserve b t N hZ
      bin hs₁ hs₂ firstIndex χ₀ Q m (embed q))=
    (fun q : Selected=>ordinarySecondDatum
      (mainLowSelectedDatum reflected s R seed Z D amp ξ reserve b t N hZ bin hs₁ hs₂ firstIndex q)
      (χ₀ q) Q m) := by
  funext q
  exact affine_high_selected_original_datum_apply reflected s R seed Z D amp ξ reserve b t N hZ
    bin hs₁ hs₂ firstIndex hinj χ₀ Q m q

/-- Physical first mass and child volume pull back exactly; neither is
replaced by an arithmetic-label count. -/
theorem affine_high_selected_first_coefficient (χ₀ : Selected→RayCharacter) (Q : Ideal O) (m : O)
    (mass : GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin→ℝ) (q : Selected) :
    mass (embed q).val.1 /
        volume (affineHighSelectedOriginalDatum reflected s R seed Z D amp ξ reserve b t N hZ
          bin hs₁ hs₂ firstIndex χ₀ Q m (embed q)).input=
    mass (firstIndex q.val.1) /
        volume (geometryLowFirstChild reflected s R seed (Z^D) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin t (firstIndex q.val.1)) := rfl
end ActualCharacter

section LiveRows
variable {α Selected Original : Type*} [Fintype α] [DecidableEq α]
variable [Fintype Selected] [Fintype Original]
variable (datum : Original→SecondInputDatum α) (embed : Selected→Original)

/-- The selected ordinary live row lifts into the same original physical
row: its label changes by the injection and both rays and row stay literal. -/
theorem affine_high_selected_live_label
    (r : secondLiveRows (fun j=>(datum (embed j)).block)) :
    (highSelectedLiveRowEmbedding datum embed r).val.1=embed r.val.1 := rfl

theorem affine_high_selected_live_payload
    (r : secondLiveRows (fun j=>(datum (embed j)).block)) :
    (highSelectedLiveRowEmbedding datum embed r).val.2=r.val.2 := rfl

theorem affine_high_selected_live_injective (hinj : Function.Injective embed) :
    Function.Injective (highSelectedLiveRowEmbedding datum embed) := by
  intro r v h
  apply Subtype.ext
  exact high_selected_row_embedding_injective datum embed hinj (congrArg Subtype.val h)

/-- Every residual divisor and its physical cost are unchanged pointwise.
The coefficient may already contain first mass divided by child volume. -/
theorem affine_high_selected_live_physical_cost
    (N : ℕ) (a ap : ℝ) (second : Bool) (coefficient : Original→ℝ) (t u : ℝ)
    (r : secondLiveRows (fun j=>(datum (embed j)).block)) (L : Ideal O) :
    mainNormalizedPhysicalCost N a ap second (fun j=>datum (embed j))
      (fun j=>coefficient (embed j)) t u r.val L=
    mainNormalizedPhysicalCost N a ap second datum coefficient t u
      (highSelectedLiveRowEmbedding datum embed r).val L := rfl

theorem affine_high_selected_live_residuals
    (r : secondLiveRows (fun j=>(datum (embed j)).block)) :
    secondResidualIdeals (fun j=>(datum (embed j)).block) r.val=
      secondResidualIdeals (fun j=>(datum j).block)
        (highSelectedLiveRowEmbedding datum embed r).val := rfl

/-- A high theorem can use the selected carrier itself as its index type.
Its indexed cost is already the original-family cost, without an image fee. -/
theorem affine_high_selected_indexed_physical_cost
    (N : ℕ) (a ap : ℝ) (second : Bool) (coefficient : Original→ℝ) (t u : ℝ)
    (rows : Finset (secondLiveRows (fun j=>(datum (embed j)).block))) :
    (∑r∈rows,∑L∈secondResidualIdeals (fun j=>(datum (embed j)).block) r.val,
      mainNormalizedPhysicalCost N a ap second (fun j=>datum (embed j))
        (fun j=>coefficient (embed j)) t u r.val L)=
    ∑r∈rows,∑L∈secondResidualIdeals (fun j=>(datum j).block)
      (highSelectedLiveRowEmbedding datum embed r).val,
      mainNormalizedPhysicalCost N a ap second datum coefficient t u
        (highSelectedLiveRowEmbedding datum embed r).val L := rfl

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
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.affine_high_selected_original_character_apply
#print axioms OAI.SevenEighths.Cycle62InitialMass.affine_high_selected_original_datum_apply
#print axioms OAI.SevenEighths.Cycle62InitialMass.affine_high_selected_ordinary_family_eq
#print axioms OAI.SevenEighths.Cycle62InitialMass.affine_high_selected_first_coefficient
#print axioms OAI.SevenEighths.Cycle62InitialMass.affine_high_selected_live_injective
#print axioms OAI.SevenEighths.Cycle62InitialMass.affine_high_selected_live_physical_cost
#print axioms OAI.SevenEighths.Cycle62InitialMass.affine_high_selected_live_residuals
#print axioms OAI.SevenEighths.Cycle62InitialMass.affine_high_selected_indexed_physical_cost
#print axioms OAI.SevenEighths.Cycle62InitialMass.affine_high_selected_live_reflected_key
