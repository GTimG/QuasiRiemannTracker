/- Copyright (c) 2026 Sil. Apache-2.0.
Exact forward and inverse restoration of the entire injective marked family.
The supplying-prime kernel depends only on frozen assignments. Live sums stay
intact, with all cross-distinctness holes and their natural coefficients.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelAssignmentReindex
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelPhysicalScalars
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelRowPools

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelMarkedRows
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelAllocationIdentity KernelLabelledSlots KernelRowExpansion
open KernelRowProfiles KernelRowPools KernelAssignmentReindex KernelPhysicalScalars
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

theorem marked_restriction (S : Finset PrimeIdeal) (slot : α → S) (T : Finset α) :
    marked S (fun i : T => slot i.val) = frozen S slot T := by
  funext P
  apply Bool.eq_iff_iff.mpr
  simp only [marked_true,frozen_true,Subtype.exists,exists_prop]

theorem marked_complement (S : Finset PrimeIdeal) (slot : α → S) (T : Finset α) :
    marked S (fun i : {i // i ∉ T} => slot i.val) = frozen S slot Tᶜ := by
  funext P
  apply Bool.eq_iff_iff.mpr
  simp only [marked_true,frozen_true,Subtype.exists,Finset.mem_compl,exists_prop]

def sourceValue (inv : Bool) (S : Finset PrimeIdeal) (slot : α → S) : IdealPair → ℂ :=
  if inv then fun _ => 1 else restrictedValue S (marked S slot)

def childValue (inv : Bool) (S : Finset PrimeIdeal) (slot : α → S) : IdealPair → ℂ :=
  if inv then restrictedValue S (marked S slot) else fun _ => 1

def extraction (inv : Bool) (S : Finset PrimeIdeal) (t : α → S)
    (χ : Character) (d : IdealPair) : ℂ :=
  extractedScalar χ (fun e => (kernelOn S
    (fun P => if marked S t P then markedSeriesFor inv else ordinarySeriesFor inv)
    e.1 e.2 : ℂ)) d

/-- The fixed-slot identity is now expressed in the actual frozen and live
subtypes. It is the same kernel as in the uniform selected-mass estimates. -/
theorem fixed_profile (inv : Bool) (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    normalizedRow χ D (sourceValue inv S slot) W₁ W₂ X₁ X₂ =
      ∑ T : Finset α, ∑ d ∈ divisorPool D,
        extraction inv S (fun i : T => slot i.val) χ d *
        normalizedRow χ (residualPool D d)
          (childValue inv S (fun i : {i // i ∉ T} => slot i.val)) W₁ W₂
          (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  cases inv
  · simpa only [sourceValue,childValue,extraction,ordinarySeriesFor,markedSeriesFor,
      Bool.false_eq_true,ite_false,marked_restriction,forwardFactor] using
      forward_profile_row S slot hinj D hnz hs χ W₁ W₂ X₁ X₂ hX₁ hX₂
  · simpa only [sourceValue,childValue,extraction,ordinarySeriesFor,markedSeriesFor,
      ite_true,marked_restriction,marked_complement,inverseFactor] using
      inverse_profile_row S slot hinj D hnz hs χ W₁ W₂ X₁ X₂ hX₁ hX₂

/-- The whole family, including arbitrary live marked coefficients, is
reindexed before taking any norm. Frozen phases remain outside each child. -/
theorem family_expansion (inv : Bool) (S : Finset PrimeIdeal) (a : α → S → ℂ)
    (D : Finset IdealPair) (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    weightedSum a (fun slot => normalizedRow χ D (sourceValue inv S slot) W₁ W₂ X₁ X₂) =
      ∑ T : Finset α, ∑ t : T → S, if Function.Injective t then ∑ d ∈ divisorPool D,
        (extraction inv S t χ d * ∏ i : T, a i.val (t i)) *
        remainingSum T a t (fun s => normalizedRow χ (residualPool D d)
          (childValue inv S s) W₁ W₂ (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)) else 0 := by
  calc
    _ = weightedSum a (fun slot => ∑ T : Finset α, ∑ d ∈ divisorPool D,
        extraction inv S (fun i : T => slot i.val) χ d *
        normalizedRow χ (residualPool D d)
          (childValue inv S (fun i : {i // i ∉ T} => slot i.val)) W₁ W₂
          (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)) := by
      unfold weightedSum
      apply Finset.sum_congr rfl
      intro slot _
      by_cases hi : Function.Injective slot
      · rw [if_pos hi,if_pos hi]
        dsimp only
        rw [fixed_profile inv S slot hi D hnz hs χ W₁ W₂ X₁ X₂ hX₁ hX₂]
      · simp [hi]
    _ = _ := by
      rw [weightedSum_sum]
      apply Finset.sum_congr rfl
      intro T _
      convert split_convolution (divisorPool D) T a (fun t d => extraction inv S t χ d)
        (fun d s => normalizedRow χ (residualPool D d) (childValue inv S s) W₁ W₂
          (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)) using 1
      apply Finset.sum_congr (by ext; simp)
      intro t _
      split_ifs <;> rfl

def naturalCoefficients (χ : Character) (S : Finset PrimeIdeal)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ) (i : α) (Q : S) : ℂ :=
  KernelNaturalSlots.slotTerm χ (pool i) (β i) (P i) Q.val.val

/-- The scalar in this exact expansion is precisely the one whose full
absolute mass was proved in KernelPhysicalScalars.natural_scalar_mass. -/
theorem natural_family_expansion (inv : Bool) (S : Finset PrimeIdeal)
    (χ : Character) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (D : Finset IdealPair) (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    weightedSum (naturalCoefficients χ S pool β P)
      (fun slot => normalizedRow χ D (sourceValue inv S slot) W₁ W₂ X₁ X₂) =
      ∑ T : Finset α, ∑ t : T → S, if Function.Injective t then ∑ d ∈ divisorPool D,
        scalar χ S (ordinarySeriesFor inv) (markedSeriesFor inv)
          (fun i : T => pool i.val) (fun i : T => β i.val) (fun i : T => P i.val) t d *
        remainingSum T (naturalCoefficients χ S pool β P) t
          (fun s => normalizedRow χ (residualPool D d) (childValue inv S s) W₁ W₂
            (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)) else 0 := by
  exact family_expansion inv S (naturalCoefficients χ S pool β P) D hnz hs χ W₁ W₂ X₁ X₂ hX₁ hX₂

/-- For supported rectangles the child is a full shorter rectangle. The
only live exclusions here are the displayed finite cross-distinctness holes. -/
theorem natural_rectangle_expansion (inv : Bool) (S : Finset PrimeIdeal)
    (χ : Character) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    weightedSum (naturalCoefficients χ S pool β P)
      (fun slot => normalizedRow χ (supportedRectangle S b X₁ X₂)
        (sourceValue inv S slot) W₁ W₂ X₁ X₂) =
      ∑ T : Finset α, ∑ t : T → S, if Function.Injective t then
        ∑ d ∈ divisorPool (supportedRectangle S b X₁ X₂),
          scalar χ S (ordinarySeriesFor inv) (markedSeriesFor inv)
            (fun i : T => pool i.val) (fun i : T => β i.val) (fun i : T => P i.val) t d *
          remainingSum T (naturalCoefficients χ S pool β P) t
            (fun s => normalizedRow χ
              (supportedRectangle S b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2))
              (childValue inv S s) W₁ W₂
              (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)) else 0 := by
  rw [natural_family_expansion inv S χ pool β P _
    (fun _ h => supportedRectangle_nonzero h) (fun _ h => (Finset.mem_filter.mp h).2)
    W₁ W₂ X₁ X₂ hX₁ hX₂]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : Function.Injective t
  · simp only [ht,ite_true]
    apply Finset.sum_congr rfl
    intro d hd
    rw [residual_rectangle hd]
  · simp [ht]

end
end Candidate.FourthPower.KernelMarkedRows
