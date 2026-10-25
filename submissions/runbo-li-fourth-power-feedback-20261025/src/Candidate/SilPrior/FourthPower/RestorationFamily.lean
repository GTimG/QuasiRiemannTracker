/- Copyright (c) 2026 Sil. Apache-2.0.
Literal natural families used by restoration. Cross-distinctness holes are
common coefficient masks, not arbitrary subsets of a positive moment.
-/
import Candidate.SilPrior.FourthPower.KernelMarkedRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.RestorationFamily
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelMarkedRows KernelRowProfiles KernelRowPools
open KernelNaturalSlots
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

def row (inv : Bool) (S : Finset PrimeIdeal) (χ : Character)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) : ℂ :=
  weightedSum (naturalCoefficients χ S pool β P)
    (fun slot => normalizedRow χ (supportedRectangle S b X₁ X₂)
      (sourceValue inv S slot) W₁ W₂ X₁ X₂)

def maskedBeta (β : α → Id → ℂ) (keep : α → Id → Prop) (i : α) (I : Id) : ℂ :=
  if keep i I then β i I else 0

omit [Fintype α] in
theorem maskedBeta_bound (β : α → Id → ℂ) (keep : α → Id → Prop)
    (pool : α → Finset Id) (B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) :
    ∀ i I, I ∈ pool i → ‖maskedBeta β keep i I‖ ≤ B := by
  intro i I hI
  by_cases h : keep i I
  · simpa only [maskedBeta,h,ite_true] using hβ i I hI
  · simpa only [maskedBeta,h,ite_false,norm_zero] using hB

theorem slotTerm_mask (χ : Character) (pool : Finset Id) (β : Id → ℂ)
    (P : ℝ) (keep : Id → Prop) (I : Id) :
    slotTerm χ pool (fun J => if keep J then β J else 0) P I =
      if keep I then slotTerm χ pool β P I else 0 := by
  by_cases hk : keep I <;> by_cases hp : I ∈ pool <;> simp [slotTerm,hk,hp]

def crossBeta (T : Finset α) (S : Finset PrimeIdeal) (t : T → S)
    (β : α → Id → ℂ) : {i // i ∉ T} → Id → ℂ :=
  maskedBeta (fun i => β i.val) (fun _ I => ∀ j : T, (t j).val.val ≠ I)

omit [Fintype α] in
theorem crossBeta_bound (T : Finset α) (S : Finset PrimeIdeal) (t : T → S)
    (β : α → Id → ℂ) (pool : α → Finset Id) (B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) :
    ∀ (i : {i // i ∉ T}) I, I ∈ pool i.val → ‖crossBeta T S t β i I‖ ≤ B :=
  maskedBeta_bound _ _ _ B hB (fun i => hβ i.val)

/-- The entire live sum is kept before taking its physical norm. The mask
depends on the frozen assignments but is common to all physical rows. -/
theorem remaining_mask (T : Finset α) (S : Finset PrimeIdeal) (t : T → S)
    (χ : Character) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (f : ({i // i ∉ T} → S) → ℂ) :
    remainingSum T (naturalCoefficients χ S pool β P) t f =
      weightedSum (naturalCoefficients χ S (fun i : {i // i ∉ T} => pool i.val)
        (crossBeta T S t β) (fun i => P i.val)) f := by
  unfold remainingSum weightedSum
  apply Finset.sum_congr (by ext; simp)
  intro s _
  have hcoeff (j : {i // i ∉ T}) :
      naturalCoefficients χ S (fun i : {i // i ∉ T} => pool i.val)
        (crossBeta T S t β) (fun i => P i.val) j (s j) =
      if ∀ i : T, t i ≠ s j then naturalCoefficients χ S pool β P j.val (s j) else 0 := by
    unfold naturalCoefficients crossBeta maskedBeta
    rw [slotTerm_mask]
    dsimp only
    have he : (∀ i : T, (t i).val.val ≠ (s j).val.val) ↔ (∀ i : T, t i ≠ s j) := by
      constructor
      · intro h i hi
        exact h i (congrArg (fun Q : S => Q.val.val) hi)
      · intro h i hi
        exact h i (Subtype.ext (Subtype.ext hi))
    simp only [he]
  simp_rw [hcoeff]
  by_cases hs : Function.Injective s
  · rw [ite_eq_left hs,Fintype.prod_ite_zero]
    by_cases hc : ∀ i : T, ∀ j : {i // i ∉ T}, t i ≠ s j
    · have hc' : ∀ j : {i // i ∉ T}, ∀ i : T, t i ≠ s j := fun j i => hc i j
      simp only [hs,true_and]
      rw [ite_eq_left hc,ite_eq_left hc']
    · have hc' : ¬ (∀ j : {i // i ∉ T}, ∀ i : T, t i ≠ s j) := fun h => hc (fun i j => h j i)
      simp only [hs,true_and,hc,hc',ite_false,mul_zero]
  · simp only [hs,false_and,ite_false]

theorem inverse_remaining_row (T : Finset α) (S : Finset PrimeIdeal) (t : T → S)
    (χ : Character) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) :
    remainingSum T (naturalCoefficients χ S pool β P) t
      (fun s => normalizedRow χ (supportedRectangle S b X₁ X₂)
        (childValue true S s) W₁ W₂ X₁ X₂) =
      row false S χ (fun i : {i // i ∉ T} => pool i.val)
        (crossBeta T S t β) (fun i => P i.val) W₁ W₂ b X₁ X₂ := by
  rw [remaining_mask]
  rfl

theorem unrestricted_row (S : Finset PrimeIdeal) (χ : Character)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) :
    row true S χ pool β P W₁ W₂ b X₁ X₂ =
      normalizedRow χ (supportedRectangle S b X₁ X₂) (fun _ => 1) W₁ W₂ X₁ X₂ *
        OAI.SevenEighths.Record12518109GainDeletion.injectiveTuplePolynomial
          (naturalCoefficients χ S pool β P) := by
  unfold row weightedSum OAI.SevenEighths.Record12518109GainDeletion.injectiveTuplePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : Function.Injective s <;> simp only [h,ite_true,ite_false,mul_zero,sourceValue]

theorem sum_prime_slot (S : Finset PrimeIdeal) (χ : Character)
    (pool : Finset Id) (β : Id → ℂ) (P : ℝ) (hpool : pool ⊆ primeValues S) :
    (∑ Q : S, slotTerm χ pool β P Q.val.val) =
      CenteredMomentCommonMaskExpansion.naturalSlot χ pool β P := by
  rw [Finset.sum_coe_sort S (fun Q : PrimeIdeal => slotTerm χ pool β P Q.val)]
  have he : (∑ Q ∈ S, slotTerm χ pool β P Q.val) =
      ∑ I ∈ primeValues S, slotTerm χ pool β P I := by
    unfold primeValues
    rw [Finset.sum_image]
    intro Q _ R _ h
    exact Subtype.ext h
  rw [he]
  exact (Finset.sum_coe_sort (primeValues S) (slotTerm χ pool β P)).symm.trans
    (sum_slotTerm χ pool (primeValues S) β P hpool)

def fullRow (S : Finset PrimeIdeal) (χ : Character)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) : ℂ :=
  normalizedRow χ (supportedRectangle S b X₁ X₂) (fun _ => 1) W₁ W₂ X₁ X₂ *
    ∏ i, CenteredMomentCommonMaskExpansion.naturalSlot χ (pool i) (β i) (P i)

theorem fullRow_eq (S : Finset PrimeIdeal) (χ : Character)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) (hpool : ∀ i, pool i ⊆ primeValues S) :
    fullRow S χ pool β P W₁ W₂ b X₁ X₂ =
      normalizedRow χ (supportedRectangle S b X₁ X₂) (fun _ => 1) W₁ W₂ X₁ X₂ *
        ∏ i, ∑ Q : S, naturalCoefficients χ S pool β P i Q := by
  unfold fullRow naturalCoefficients
  simp_rw [sum_prime_slot S χ _ _ _ (hpool _)]

end
end Candidate.SilPrior.FourthPower.RestorationFamily
