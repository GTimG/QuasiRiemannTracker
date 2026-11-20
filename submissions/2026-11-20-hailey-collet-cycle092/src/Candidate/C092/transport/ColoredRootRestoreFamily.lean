/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The whole native marked forward family with two independent ordinary colors. -/
import Candidate.C092.transport.ColoredRootRestoreInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredRootRestore
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open Candidate.FourthPower
open QRH.SilDensitySplit.CubeFree.FP
open KernelLabelledSlots KernelAllocationIdentity KernelRowExpansion KernelRowProfiles KernelMarkedRows
open KernelPhysicalScalars KernelAssignmentReindex KernelRowPools
open QRH.Cycle092.RegularColoredForward
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]

/-- Reindex the actual injective supplying assignments before taking norms.
The ordinary colors stay on ordinary coordinates, separate from mark χ. -/
theorem inverse_family_expansion (S : Finset PrimeIdeal) (a : α → S → ℂ)
    (D : Finset IdealPair) (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    weightedSum a (fun slot => row χ ω₁ ω₂ D
      (sourceValue true S slot) W₁ W₂ X₁ X₂) =
      ∑ T : Finset α, ∑ t : T → S, if Function.Injective t then ∑ d ∈ divisorPool D,
        (extraction true S t χ d * color ω₁ ω₂ d * ∏ i : T, a i.val (t i)) *
          remainingSum T a t (fun s => row χ ω₁ ω₂ (residualPool D d)
            (childValue true S s) W₁ W₂
            (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)) else 0 := by
  calc
    _ = weightedSum a (fun slot => ∑ T : Finset α, ∑ d ∈ divisorPool D,
        (extraction true S (fun i : T => slot i.val) χ d * color ω₁ ω₂ d) *
          row χ ω₁ ω₂ (residualPool D d) (childValue true S (fun i : {i // i ∉ T} => slot i.val)) W₁ W₂
            (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)) := by
      unfold weightedSum
      apply Finset.sum_congr rfl
      intro slot hslot
      by_cases hi : Function.Injective slot
      · rw [ite_eq_left hi,ite_eq_left hi]
        simp only [sourceValue,ite_true]
        rw [inverse_profile S slot hi D hnz hs χ ω₁ ω₂ W₁ W₂ X₁ X₂ hX₁ hX₂]
        simp only [childValue,ite_true,marked_complement]
      · simp [hi]
    _ = _ := by
      rw [weightedSum_sum]
      apply Finset.sum_congr rfl
      intro T hT
      convert split_convolution (divisorPool D) T a
        (fun t d => extraction true S t χ d * color ω₁ ω₂ d)
        (fun d s => row χ ω₁ ω₂ (residualPool D d) (childValue true S s) W₁ W₂
          (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)) using 1
      apply Finset.sum_congr (by ext; simp)
      intro t ht
      split_ifs <;> rfl

/-- Natural coefficients have exactly the original native scalar; ordinary
colors multiply that scalar and are never absorbed into a mark-only ν. -/
theorem natural_inverse_family_expansion (S : Finset PrimeIdeal)
    (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (D : Finset IdealPair) (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    weightedSum (naturalCoefficients χ S pool β P) (fun slot =>
      row χ ω₁ ω₂ D (sourceValue true S slot) W₁ W₂ X₁ X₂) =
      ∑ T : Finset α, ∑ t : T → S, if Function.Injective t then ∑ d ∈ divisorPool D,
        scalar χ S (ordinarySeriesFor true) (markedSeriesFor true)
          (fun i : T => pool i.val) (fun i : T => β i.val) (fun i : T => P i.val) t d *
          color ω₁ ω₂ d * remainingSum T (naturalCoefficients χ S pool β P) t
            (fun s => row χ ω₁ ω₂ (residualPool D d) (childValue true S s) W₁ W₂
              (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)) else 0 := by
  rw [inverse_family_expansion S (naturalCoefficients χ S pool β P) D hnz hs
    χ ω₁ ω₂ W₁ W₂ X₁ X₂ hX₁ hX₂]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs
  · apply Finset.sum_congr rfl
    intro d hd
    simp only [scalar,naturalCoefficients,extraction]
    ring
  · rfl


#print axioms inverse_family_expansion
#print axioms natural_inverse_family_expansion
end
end QRH.Cycle092.ColoredRootRestore
