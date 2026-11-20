/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The exact nonnegative selected allocation weights in the two H.25 sides. -/
import Candidate.C092.transport.PairedRetainedBudgetParts
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
local instance (priority := 2000) pairedWeightsSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentChildRows
open CenteredMomentFirstAmplificationChoice
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedFirstLiveSource
open MixedInnerExceptionalBlock MixedOriginalNormCap
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle092.TwistedRawBall
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι]

def selectedPartTerm (part : Bool) (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Z ξ : ℝ) (ζ : RayCharacter) : ℝ :=
  let r := restOf s (by norm_num) cover G B J
  let W := RawSides.selectionScaleQ s (by norm_num) cover G B J
  let X := RawSides.residualCapQ r
  RootColoredSeed.groupedPartTerms part r (by norm_num) (idealCoeff η₁) (idealCoeff η₂)
    (childCharacter τ ζ) χ₀ Q m t (16*K*W^4) (RootColoredSeed.secondCutoffQ X K W) Z ξ X

/-- Includes the actual assignment sum; no unrestricted assignment count is omitted. -/
def selectedWeight (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (t : ℝ) : ℝ :=
  allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B *
    Atot (allocatedLiveSource s (by norm_num) cover G B) J τ t *
    (∑y∈selY (allocatedLiveSource s (by norm_num) cover G B) J,
      (2:ℝ)^(IdealMobiusDivisorSum.primeSupport (∏j,y j)).card) * Fintype.card RayCharacter

theorem selectedWeight_nonneg (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (t : ℝ) : 0 ≤ selectedWeight s cover G B J η₁ η₂ τ t := by
  unfold selectedWeight allocationWeight Atot
  positivity

private theorem assignment_ray_sum {α : Type*} (Y : Finset α) (weight : α→ℝ) (F : RayCharacter→ℝ) :
    (∑y∈Y,∑χ : RayCharacter,∑ζ : RayCharacter,weight y*F ζ) =
      (∑y∈Y,weight y)*(Fintype.card RayCharacter)*(∑ζ : RayCharacter,F ζ) := by
  simp only [←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←Finset.sum_mul]
  ring

/-- The H.26 physical positive part is collected with its own selected
    Φ weight. The original source denominator remains outside this identity. -/
theorem partSideCost_eq_weighted_parts (part : Bool) (s : Source ι (1/4) (9/4))
    (cover : OriginalEnclosure s) (G : Id)
    (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Z ξ : ℝ) :
    partSideCost part s cover G Js η₁ η₂ τ χ₀ Q m t K Z ξ =
      ((actualAllocations (tuplePools s) G).card : ℝ)*
        ∑B : actualAllocations (tuplePools s) G,
          selectedWeight s cover G B (Js B) η₁ η₂ τ t *
            ∑ζ : RayCharacter,selectedPartTerm part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t K Z ξ ζ := by
  unfold partSideCost selectedWeight selectedPartTerm
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  dsimp only
  rw [assignment_ray_sum]
  ring

/-- Pointwise bounds on actual completed physical terms can be aggregated
    without changing their label, assignment or allocation measure. -/
theorem partSideCost_le_weighted_parts (part : Bool) (s : Source ι (1/4) (9/4))
    (cover : OriginalEnclosure s) (G : Id)
    (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Z ξ : ℝ)
    (cost : actualAllocations (tuplePools s) G→RayCharacter→ℝ)
    (hcost : ∀B ζ,selectedPartTerm part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t K Z ξ ζ ≤ cost B ζ) :
    partSideCost part s cover G Js η₁ η₂ τ χ₀ Q m t K Z ξ ≤
      ((actualAllocations (tuplePools s) G).card : ℝ)*
        ∑B : actualAllocations (tuplePools s) G,
          selectedWeight s cover G B (Js B) η₁ η₂ τ t *∑ζ : RayCharacter,cost B ζ := by
  rw [partSideCost_eq_weighted_parts]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B hB
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ζ _=>hcost B ζ))
    (selectedWeight_nonneg s cover G B (Js B) η₁ η₂ τ t)

#print axioms selectedWeight_nonneg
#print axioms partSideCost_eq_weighted_parts
#print axioms partSideCost_le_weighted_parts
end
end QRH.Cycle092.PairedRetainedBudget
