/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Independent ordinary colors in the native C.7 forward restriction. The
restriction, extracted divisors and finite collision coefficients are unchanged. -/
import Submissions.sil_density_split_20261026.CubeFree.FP.KernelMarkedRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open KernelFormal KernelAllocationIdentity KernelLabelledSlots KernelRowExpansion
open KernelRowProfiles KernelMarkedRows KernelPhysicalScalars
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]

/-- The ordinary factors are independent and retain their actual zeros. -/
def color (ω₁ ω₂ : Id →*₀ ℂ) (n : IdealPair) : ℂ := ω₁ n.1 * ω₂ n.2

@[simp] theorem color_multiply (ω₁ ω₂ : Id →*₀ ℂ) (d a : IdealPair) :
    color ω₁ ω₂ (multiplyPair d a) = color ω₁ ω₂ d * color ω₁ ω₂ a := by
  simp only [color,multiplyPair,map_mul]
  ring

/-- Literal two-character C.7 identity, before normalization or any norm.
The native forward kernel is untouched, including its supplying-prime terms. -/
theorem forward_row (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ) (f : IdealPair → ℂ) :
    (∑ n ∈ D, restrictedValue S (marked S slot) n * pairCharacter χ n *
      color ω₁ ω₂ n * f n) =
      ∑ T : Finset α, ∑ d ∈ divisorPool D,
        (kernelOn S (fun P => forwardFactor (frozen S slot T P)) d.1 d.2 : ℂ) *
          pairCharacter χ d * color ω₁ ω₂ d *
          ∑ a ∈ residualPool D d, pairCharacter χ a * color ω₁ ω₂ a *
            f (multiplyPair d a) := by
  have h := forward_row_expansion S slot hinj D hnz hs χ
    (fun n => color ω₁ ω₂ n * f n)
  simp only [color_multiply] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro n hn
    ring
  · apply Finset.sum_congr rfl
    intro T hT
    apply Finset.sum_congr rfl
    intro d hd
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring

/-- The normalized two-color row uses the original native normalizer. -/
def row (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ) (D : Finset IdealPair)
    (r : IdealPair → ℂ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  normalizedRow χ D (fun n => r n * color ω₁ ω₂ n) W₁ W₂ X₁ X₂

/-- Exact shortened profiles and the original extracted square-root factor.
No color is divided and no ramified coefficient is declared a unit. -/
theorem forward_profile (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    row χ ω₁ ω₂ D (restrictedValue S (marked S slot)) W₁ W₂ X₁ X₂ =
      ∑ T : Finset α, ∑ d ∈ divisorPool D,
        extraction false S (fun i : T => slot i.val) χ d * color ω₁ ω₂ d *
          row χ ω₁ ω₂ (residualPool D d) (fun _ => 1) W₁ W₂
            (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  unfold row normalizedRow
  have hrow := forward_row S slot hinj D hnz hs χ ω₁ ω₂ (pairProfile W₁ W₂ X₁ X₂)
  have heq : (∑ n ∈ D, (restrictedValue S (marked S slot) n * color ω₁ ω₂ n) *
      pairCharacter χ n * pairProfile W₁ W₂ X₁ X₂ n) =
      ∑ n ∈ D, restrictedValue S (marked S slot) n * pairCharacter χ n *
        color ω₁ ω₂ n * pairProfile W₁ W₂ X₁ X₂ n := by
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [heq,hrow]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [profile_multiply]
  have hc := central_normalization (X₁*X₂) (pairNorm d)
    (mul_pos hX₁ hX₂) (pairNorm_pos (divisorPool_nonzero D hnz hd).1
      (divisorPool_nonzero D hnz hd).2)
  have hv : (X₁/(Ideal.absNorm d.1 : ℝ))*(X₂/(Ideal.absNorm d.2 : ℝ)) =
      (X₁*X₂)/pairNorm d := by unfold pairNorm; ring
  rw [hv,hc]
  simp only [extraction,extractedScalar,ordinarySeriesFor,markedSeriesFor,
    Bool.false_eq_true,ite_false,marked_restriction,forwardFactor,one_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

#print axioms forward_row
#print axioms forward_profile
end
end QRH.Cycle092.RegularColoredForward
