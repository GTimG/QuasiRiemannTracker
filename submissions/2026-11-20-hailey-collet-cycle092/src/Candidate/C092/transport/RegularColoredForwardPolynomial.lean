/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The remaining two-color ordinary rectangle is exactly the product of the two
actual ordinary polynomials, with separate characters and profile heights. -/
import Candidate.C092.transport.RegularColoredForwardEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open Candidate.FourthPower
open QRH.SilDensitySplit.CubeFree.FP
open KernelRowExpansion KernelRowProfiles KernelRowPools ReferencePrimeEnclosure
open KernelMarkedRows KernelPhysicalScalars KernelAssignmentReindex
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]

/-- Distinct ordinary factors share only the moving χ. -/
theorem natural_pair_row (χ ω₁ ω₂ : Character) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b) (hW₂ : Function.support W₂ ⊆ Set.Iic b) :
    row χ (idealCoeff ω₁) (idealCoeff ω₂) (rectangle b X₁ X₂) (fun _ => 1) W₁ W₂ X₁ X₂ =
      HeckeDyadic.polynomial (χ.product ω₁) false W₁ X₁ 0 0 *
        HeckeDyadic.polynomial (χ.product ω₂) false W₂ X₂ 0 0 := by
  rw [natural_polynomial_finite (χ.product ω₁) W₁ b X₁ hX₁ hW₁,
    natural_polynomial_finite (χ.product ω₂) W₂ b X₂ hX₂ hW₂]
  unfold row normalizedRow
  rw [Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  simp only [rectangle,Finset.sum_product,pairCharacter,map_mul,pairProfile,one_mul,
    idealCoeff_product,color]
  simp only [Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  ring

/-- The prime enclosure is discharged using the moving χ's actual support.
The independent ordinary characters, their zeros and both heights persist. -/
theorem enclosed_phase_pair (χ ω₁ ω₂ : Character) (S : Finset PrimeIdeal)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ t₁ t₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b) (hW₂ : Function.support W₂ ⊆ Set.Iic b)
    (hχ : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (henclose : ∀ I, Supported I →
      ((Ideal.absNorm I : ℝ) ≤ b*X₁ ∨ (Ideal.absNorm I : ℝ) ≤ b*X₂) →
      primeSupport I ⊆ primeValues S) :
    row χ (idealCoeff ω₁) (idealCoeff ω₂) (supportedRectangle S b X₁ X₂) (fun _ => 1)
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) X₁ X₂ =
      HeckeDyadic.polynomial (χ.product ω₁) false W₁ X₁ 0 (2*Real.pi*t₁) *
        HeckeDyadic.polynomial (χ.product ω₂) false W₂ X₂ 0 (2*Real.pi*t₂) := by
  unfold row
  rw [enclosed_row χ S b X₁ X₂ _ _ _ hχ henclose]
  change row χ (idealCoeff ω₁) (idealCoeff ω₂) (rectangle b X₁ X₂) (fun _ => 1)
    (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) X₁ X₂ = _
  rw [natural_pair_row χ ω₁ ω₂ _ _ b X₁ X₂ hX₁ hX₂
    ((phaseProfile_support W₁ t₁).trans hW₁) ((phaseProfile_support W₂ t₂).trans hW₂),
    phase_polynomial (χ.product ω₁) W₁ b X₁ t₁ hX₁ hW₁,
    phase_polynomial (χ.product ω₂) W₂ b X₂ t₂ hX₂ hW₂]

/-- The exact two-character polynomial child of C.7, in the original positive
finite norm. This is the usable forward input for StrongPair finite sources. -/
theorem finite_forward_polynomial_energy (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ Q ∈ S, Supported Q.val ∧ (Q.val.absNorm : ℝ) ≤ X) →
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (ω₁ ω₂ : Character) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (I.absNorm : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ t₁ t₂ E : ℝ),
      0 ≤ b → 0 < X₁ → 0 < X₂ → 0 ≤ E →
      Function.support W₁ ⊆ Set.Iic b → Function.support W₂ ⊆ Set.Iic b →
      (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ u ∈ rows, ∀ I, ¬Supported I → idealCoeff (χ u) I = 0) →
      (∀ I, Supported I →
        ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues S) →
      (∀ (T : Finset α) (frozen : T → S), Function.Injective frozen →
        ∀ d ∈ divisorPool (supportedRectangle S b X₁ X₂),
          (∑ u ∈ rows, ρ u * ‖
            HeckeDyadic.polynomial ((χ u).product ω₁) false W₁
                (X₁/(d.1.absNorm : ℝ)) 0 (2*Real.pi*t₁) *
            HeckeDyadic.polynomial ((χ u).product ω₂) false W₂
                (X₂/(d.2.absNorm : ℝ)) 0 (2*Real.pi*t₂) *
            remainingSum T (naturalCoefficients (χ u) S pool β P) frozen (fun _ => 1)‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u * ‖weightedSum (naturalCoefficients (χ u) S pool β P)
        (fun slot => row (χ u) (idealCoeff ω₁) (idealCoeff ω₂) (supportedRectangle S b X₁ X₂)
          (sourceValue false S slot) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) X₁ X₂)‖^2) ≤ C*X^ε*E := by
  obtain ⟨C,hC,hbound⟩ := finite_forward_energy (α:=α) B ε hB hε
  refine ⟨C,hC,?_⟩
  intro X hX S hS Row rows ρ χ ω₁ ω₂ pool β P hP hp hβ W₁ W₂ b X₁ X₂ t₁ t₂ E
    hb hX₁ hX₂ hE hW₁ hW₂ hρ hχ henclose hchildren
  apply hbound X hX S hS rows ρ χ (idealCoeff ω₁) (idealCoeff ω₂)
    (color_norm_le_one ω₁ ω₂) pool β P hP hp hβ _ _ b X₁ X₂ E hX₁ hX₂ hE hρ
  intro T frozen hfrozen d hd
  apply (le_of_eq ?_).trans (hchildren T frozen hfrozen d hd)
  apply Finset.sum_congr rfl
  intro u hu
  have h₁ := shortened_positive_le hX₁ (divisor_supported hd).1
  have h₂ := shortened_positive_le hX₂ (divisor_supported hd).2.1
  rw [enclosed_phase_pair (χ u) ω₁ ω₂ S W₁ W₂ b _ _ t₁ t₂
    h₁.1 h₂.1 hW₁ hW₂ (hχ u hu) (by
      intro I hI hlen
      apply henclose I hI
      exact hlen.elim
        (fun h => Or.inl (h.trans (mul_le_mul_of_nonneg_left h₁.2 hb)))
        (fun h => Or.inr (h.trans (mul_le_mul_of_nonneg_left h₂.2 hb))))]

#print axioms natural_pair_row
#print axioms enclosed_phase_pair
#print axioms finite_forward_polynomial_energy
end
end QRH.Cycle092.RegularColoredForward
