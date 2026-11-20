/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Corrected selected image-multiplicity average, without a free assignment sum. -/
import Candidate.C092.transport.PairedRetainedBudgetScalar
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.PairedRetainedBudget
noncomputable section
local instance (priority := 2000) pairedAverageSubtypeDecEq {κ : Type*} {p : κ→Prop} :
    DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
open QRH.SilDensitySplit.CubeFree.Second.Provider
open QRH.Cycle092.TwistedRawBall
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type} [Fintype ι]

/-- M is the actual selected-image multiplicity supplied by the corrected
    selection theorem. There is no unrestricted selY sum in these weights. -/
def coloredOuterAverage (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s) (G : Id)
    (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (t : ℝ) (M : actualAllocations (tuplePools s) G→ℝ)
    (F : actualAllocations (tuplePools s) G→RayCharacter→ℝ) : ℝ :=
  ((actualAllocations (tuplePools s) G).card : ℝ)*
    ∑B : actualAllocations (tuplePools s) G,allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B *
      (Atot (allocatedLiveSource s (by norm_num) cover G B) (Js B) τ t *
        ((2:ℝ)^Fintype.card (Js B)*M B)*∑_χ : RayCharacter,∑ζ : RayCharacter,F B ζ)

def averagedPartSideCost (part : Bool) (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (G : Id) (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (M : actualAllocations (tuplePools s) G→ℝ) (η₁ η₂ τ : Character)
    (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Z ξ : ℝ) : ℝ :=
  coloredOuterAverage s cover G Js η₁ η₂ τ t M
    (fun B ζ=>selectedPartTerm part s cover G B (Js B) η₁ η₂ τ χ₀ Q m t K Z ξ ζ)

/-- The exact colored analogue of native label_outer_bound. Its premises
    concern only the literal finite positive selected parts. -/
theorem colored_outerAverage_bound (s : Source ι (1/4) (9/4)) (cover : OriginalEnclosure s)
    (G : Id) (Js : ∀B : actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (t : ℝ) (M Λ : actualAllocations (tuplePools s) G→ℝ)
    (F : actualAllocations (tuplePools s) G→RayCharacter→ℝ) (J : ℕ)
    (hM : ∀B,0 ≤ M B) (hF0 : ∀B ζ,0 ≤ F B ζ)
    (hF : ∀B ζ,F B ζ ≤ Λ B*(1+‖t‖)^(2*J)) :
    coloredOuterAverage s cover G Js η₁ η₂ τ t M F ≤
      (((actualAllocations (tuplePools s) G).card : ℝ)*
        ∑B : actualAllocations (tuplePools s) G,allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B *
          (AtotP (allocatedLiveSource s (by norm_num) cover G B) (Js B)*
            ((2:ℝ)^Fintype.card (Js B)*M B)*
              ((Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ)*Λ B)))*(1+‖t‖)^(2*J) := by
  unfold coloredOuterAverage
  rw [mul_assoc,Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro B hB
  have hA := Atot_le (allocatedLiveSource s (by norm_num) cover G B) (Js B) τ t
  have hAP := AtotP_nonneg (allocatedLiveSource s (by norm_num) cover G B) (Js B)
  have h2M : 0 ≤ (2:ℝ)^Fintype.card (Js B)*M B := mul_nonneg (by positivity) (hM B)
  have hsum : (∑_χ : RayCharacter,∑ζ : RayCharacter,F B ζ) ≤
      (Fintype.card RayCharacter:ℝ)*(Fintype.card RayCharacter:ℝ)*Λ B*(1+‖t‖)^(2*J) := by
    apply (Finset.sum_le_sum (fun χ _=>Finset.sum_le_sum (fun ζ _=>hF B ζ))).trans_eq
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  have hsum0 : 0 ≤ ∑_χ : RayCharacter,∑ζ : RayCharacter,F B ζ :=
    Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun ζ _=>hF0 B ζ))
  have hinner := mul_le_mul (mul_le_mul_of_nonneg_right hA h2M) hsum hsum0 (mul_nonneg hAP h2M)
  have hweight : 0 ≤ allocationWeight s (idealCoeff η₁) (idealCoeff η₂) G B := by
    unfold allocationWeight
    exact sq_nonneg _
  exact (mul_le_mul_of_nonneg_left hinner hweight).trans_eq (by ring)

#print axioms colored_outerAverage_bound
end
end QRH.Cycle092.PairedRetainedBudget
