/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine live injective child reduces to products on surviving original
slots with the original coefficients and the actual frozen-prime holes. -/
import Candidate.C092.transport.RegularColoredForwardPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open Candidate.FourthPower
open QRH.SilDensitySplit.CubeFree.FP
open KernelAssignmentReindex KernelMarkedRows KernelNaturalSlots KernelCollisionMass
open NativeInjectiveEnergy NativeRemainingEnergy NativeFiniteHoles
open ReferencePrimeEnclosure
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]

/-- Reverse collision completion for exactly the live factor produced by the
forward identity. The coefficient is the original coefficient punctured at
all actual frozen suppliers; further holes have the native cardinal bound.
The ordinary multiplier is arbitrary, so the two polynomial factors remain
intact through this positive-norm operation. -/
theorem remaining_energy_of_products (T : Finset α) (B ε : ℝ)
    (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ (frozen : T → enclosure X),
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (D : Row → ℂ) (χ : Row → Character)
        (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ) (E : ℝ),
      (∀ i, pool i ⊆ ReferencePrimeEnclosure.primePool X) →
      0 ≤ E → (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ u ∈ rows, ∀ (i : α) (p : ReferencePrimeEnclosure.primePool X),
        ‖slotTerm (χ u) (pool i) (β i) (P i) p.val‖ ≤ centralWeight B p.val) →
      (∀ (A : Finset {i // i ∉ T}) (R : {i // i ∉ T} → Finset Id),
        (∀ i ∈ A, (R i).card ≤ Fintype.card {i // i ∉ T} * Fintype.card {i // i ∉ T}) →
        (∑ u ∈ rows, ρ u * ‖D u * ∏ i ∈ A,
          naturalSlot (χ u) (pool i.val)
            (holeCoefficient
              (holeCoefficient (fun i : {i // i ∉ T} => β i.val)
                (fun _ => frozenHoles T (enclosure X) frozen)) R i) (P i.val)‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u * ‖D u *
        remainingSum T (naturalCoefficients (χ u) (enclosure X) pool β P) frozen (fun _ => 1)‖^2) ≤
        C*X^ε*E := by
  obtain ⟨C,hC,hbound⟩ := natural_finite_energy (α:={i // i ∉ T}) B ε hB hε
  refine ⟨C,hC,?_⟩
  intro X hX frozen Row rows ρ D χ pool β P E hp hE hρ hslot hproducts
  simp_rw [remaining_as_injective]
  apply hbound X hX (ReferencePrimeEnclosure.primePool X)
    (fun I hI => ⟨(Finset.mem_filter.mp hI).2.2,
      ((CenteredMomentSourceMass.mem_idealBall _ _).mp (Finset.mem_filter.mp hI).1).2⟩)
    rows ρ D χ (fun i => pool i.val)
    (holeCoefficient (fun i : {i // i ∉ T} => β i.val)
      (fun _ => frozenHoles T (enclosure X) frozen)) (fun i => P i.val) E
    (fun i => hp i.val) hE hρ _ hproducts
  intro u hu i p
  by_cases hhole : p.val ∈ frozenHoles T (enclosure X) frozen
  · simp only [slotTerm,holeCoefficient,hhole,ite_true,mul_zero]
    split_ifs <;> simp only [norm_zero]
    all_goals exact centralWeight_nonneg B (zero_le_one.trans hB) p.val
  · simpa only [slotTerm,holeCoefficient,hhole,ite_false] using hslot u hu i.val p

/-- The two independent ordinary polynomial factors are retained exactly in
the reverse-collision step; no Hölder replacement of the ordinary pair occurs. -/
theorem polynomial_remaining_energy_of_products (T : Finset α) (B ε : ℝ)
    (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ (frozen : T → enclosure X),
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (ω₁ ω₂ : Character) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
        (W₁ W₂ : ℝ → ℂ) (X₁ X₂ t₁ t₂ E : ℝ),
      (∀ i, pool i ⊆ ReferencePrimeEnclosure.primePool X) →
      0 ≤ E → (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ u ∈ rows, ∀ (i : α) (p : ReferencePrimeEnclosure.primePool X),
        ‖slotTerm (χ u) (pool i) (β i) (P i) p.val‖ ≤ centralWeight B p.val) →
      (∀ (A : Finset {i // i ∉ T}) (R : {i // i ∉ T} → Finset Id),
        (∀ i ∈ A, (R i).card ≤ Fintype.card {i // i ∉ T} * Fintype.card {i // i ∉ T}) →
        (∑ u ∈ rows, ρ u * ‖
          HeckeDyadic.polynomial ((χ u).product ω₁) false W₁ X₁ 0 (2*Real.pi*t₁) *
          HeckeDyadic.polynomial ((χ u).product ω₂) false W₂ X₂ 0 (2*Real.pi*t₂) *
          ∏ i ∈ A, naturalSlot (χ u) (pool i.val)
            (holeCoefficient
              (holeCoefficient (fun i : {i // i ∉ T} => β i.val)
                (fun _ => frozenHoles T (enclosure X) frozen)) R i) (P i.val)‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u * ‖
        HeckeDyadic.polynomial ((χ u).product ω₁) false W₁ X₁ 0 (2*Real.pi*t₁) *
        HeckeDyadic.polynomial ((χ u).product ω₂) false W₂ X₂ 0 (2*Real.pi*t₂) *
        remainingSum T (naturalCoefficients (χ u) (enclosure X) pool β P) frozen (fun _ => 1)‖^2) ≤
        C*X^ε*E := by
  obtain ⟨C,hC,hbound⟩ := remaining_energy_of_products T B ε hB hε
  exact ⟨C,hC,fun X hX frozen Row rows ρ χ ω₁ ω₂ pool β P W₁ W₂ X₁ X₂ t₁ t₂ E =>
    hbound X hX frozen rows ρ
      (fun u => HeckeDyadic.polynomial ((χ u).product ω₁) false W₁ X₁ 0 (2*Real.pi*t₁) *
        HeckeDyadic.polynomial ((χ u).product ω₂) false W₂ X₂ 0 (2*Real.pi*t₂))
      χ pool β P E⟩

#print axioms remaining_energy_of_products
#print axioms polynomial_remaining_energy_of_products
end
end QRH.Cycle092.RegularColoredForward
