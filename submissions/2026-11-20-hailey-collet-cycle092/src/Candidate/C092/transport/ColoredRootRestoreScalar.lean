/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The native scalar envelope for independent ordinary colors, for either direction. -/
import Candidate.C092.transport.ColoredRootRestoreInverse
import Submissions.sil_density_split_20261026.CubeFree.FP.KernelFamilyEnergy
set_option autoImplicit false
namespace QRH.Cycle092.ColoredRootRestore
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.FP
open KernelPhysicalScalars KernelCommonScalarMass KernelFamilyEnergy
open QRH.Cycle092.RegularColoredForward
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]
/-- Exact native scalar and exact H16 mass: ordinary colors are extracted
without replacing the collision coefficient or adding a label count. -/
theorem colored_subpower_energy (inv : Bool) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ t ∈ F, Function.Injective t) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ t ∈ F, ∀ d ∈ D t, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ t ∈ F, ∀ d ∈ D t, pairSupport d.1 d.2 ⊆ primeValues S) →
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (ω₁ ω₂ : Id →*₀ ℂ),
      (∀ d : Id × Id, ‖color ω₁ ω₂ d‖ ≤ 1) →
      ∀ (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ G : (α → S) → (Id × Id) → Row → ℂ, ∀ E : ℝ, 0 ≤ E →
      (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ t ∈ F, ∀ d ∈ D t, (∑ u ∈ rows, ρ u*‖G t d u‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u*‖∑ t ∈ F, ∑ d ∈ D t,
        scalar (χ u) S (ordinarySeriesFor inv) (markedSeriesFor inv)
          pool β P t d * color ω₁ ω₂ d * G t d u‖^2) ≤ C*X^ε*E := by
  obtain ⟨C,hC,hbound⟩ := KernelFamilyEnergy.actual_subpower_energy (α:=α) inv B ε hB hε
  refine ⟨C,hC,?_⟩
  intro X hX S hS F hinj D hd hs Row rows ρ χ ω₁ ω₂ hω pool β P hP hp hβ G E hE hρ hG
  have hchild (t : α → S) (ht : t ∈ F) (d : Id × Id) (hdd : d ∈ D t) :
      (∑ u ∈ rows, ρ u*‖color ω₁ ω₂ d * G t d u‖^2) ≤ E := by
    apply (Finset.sum_le_sum ?_).trans (hG t ht d hdd)
    intro u hu
    apply mul_le_mul_of_nonneg_left _ (hρ u hu)
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hω d)
  have h := hbound X hX S hS F hinj D hd hs rows ρ χ pool β P hP hp hβ
    (fun t d u => color ω₁ ω₂ d * G t d u) E hE hρ hchild
  simpa only [mul_assoc] using h


#print axioms colored_subpower_energy
end
end QRH.Cycle092.ColoredRootRestore
