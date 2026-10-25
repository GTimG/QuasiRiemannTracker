/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Actual unchanged ordinary profiles and central normalizations under extraction.
The elementary profile and square-root identities follow PR69 Restoration
FiniteRows/InverseRows; its squarefree restoration chain is not imported.
-/
import Candidate.SilPrior.FourthPower.KernelRowExpansion
import Candidate.SilPrior.FourthPower.KernelReflectedMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.KernelRowProfiles
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelAllocationIdentity KernelLabelledSlots KernelRowExpansion
local notation "Id" => Ideal ActualEisensteinCubic.O

def pairProfile (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (n : IdealPair) : ℂ :=
  W₁ ((Ideal.absNorm n.1 : ℝ)/X₁)*W₂ ((Ideal.absNorm n.2 : ℝ)/X₂)

theorem profile_multiply (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (d a : IdealPair) :
    pairProfile W₁ W₂ X₁ X₂ (multiplyPair d a) =
      pairProfile W₁ W₂ (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) a := by
  unfold pairProfile multiplyPair
  simp only [map_mul,Nat.cast_mul]
  rw [div_div_eq_mul_div,div_div_eq_mul_div]
  congr 2 <;> ring

theorem divisorPool_nonzero (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0) {d : IdealPair} (hd : d ∈ divisorPool D) :
    d.1 ≠ 0 ∧ d.2 ≠ 0 := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨n,hn,hpn⟩ := Finset.mem_biUnion.mp hp
  have he := expandedAt_reconstruct (hnz n hn) hpn
  have hz : (multiplyPair p.1 p.2).1 ≠ 0 ∧ (multiplyPair p.1 p.2).2 ≠ 0 :=
    he.symm ▸ hnz n hn
  exact ⟨(mul_ne_zero_iff.mp hz.1).1,(mul_ne_zero_iff.mp hz.2).1⟩

theorem shortened_positive_le {X : ℝ} (hX : 0 < X) {I : Id} (hI : I ≠ 0) :
    0 < X/(Ideal.absNorm I : ℝ) ∧ X/(Ideal.absNorm I : ℝ) ≤ X := by
  have hn := ideal_norm_one_le hI
  exact ⟨div_pos hX (zero_lt_one.trans_le hn),div_le_self hX.le hn⟩

theorem central_normalization (V N : ℝ) (hV : 0 < V) (hN : 0 < N) :
    (Real.sqrt V : ℂ)⁻¹ =
      (Real.sqrt N : ℂ)⁻¹*(Real.sqrt (V/N) : ℂ)⁻¹ := by
  rw [Real.sqrt_div hV.le,Complex.ofReal_div]
  have hn : (Real.sqrt N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  field_simp

def normalizedRow (χ : Character) (D : Finset IdealPair) (r : IdealPair → ℂ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  (Real.sqrt (X₁*X₂) : ℂ)⁻¹ *
    ∑ n ∈ D, r n*pairCharacter χ n*pairProfile W₁ W₂ X₁ X₂ n

def extractedScalar (χ : Character) (k : IdealPair → ℂ) (d : IdealPair) : ℂ :=
  k d*pairCharacter χ d/(Real.sqrt (pairNorm d) : ℂ)

theorem normalized_extraction (χ : Character) (d : IdealPair)
    (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) (A : Finset IdealPair) (k : IdealPair → ℂ)
    (r : IdealPair → ℂ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    (Real.sqrt (X₁*X₂) : ℂ)⁻¹ * (k d*pairCharacter χ d*
      ∑ a ∈ A, r a*pairCharacter χ a*pairProfile W₁ W₂ X₁ X₂ (multiplyPair d a)) =
      extractedScalar χ k d *
        normalizedRow χ A r W₁ W₂ (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  simp_rw [profile_multiply]
  have he : (X₁/(Ideal.absNorm d.1 : ℝ))*(X₂/(Ideal.absNorm d.2 : ℝ)) =
      (X₁*X₂)/pairNorm d := by unfold pairNorm; ring
  unfold extractedScalar normalizedRow
  rw [he,central_normalization (X₁*X₂) (pairNorm d)
    (mul_pos hX₁ hX₂) (pairNorm_pos hd.1 hd.2)]
  ring

theorem extractedScalar_bound (χ : Character) (k : IdealPair → ℂ) (d : IdealPair) :
    ‖extractedScalar χ k d‖ ≤ ‖k d‖/(Real.sqrt (pairNorm d)) := by
  unfold extractedScalar pairCharacter
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_of_le_one_right (norm_nonneg _) (idealCoeff_norm_le_one χ _)

/-- The bound is independent of the physical row character, including its
natural zeros. It is exactly the previously proved central ideal mass. -/
theorem ordinary_extracted_mass (χ : Character) (f : Exponent → ℤ)
    (d : IdealPair) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    ‖extractedScalar χ (fun e => (idealKernel f e.1 e.2 : ℂ)) d‖ ≤
      idealPairWeight f (1/2) d := by
  have hi : 0 < (Ideal.absNorm d.1 : ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hd.1)
  have hj : 0 < (Ideal.absNorm d.2 : ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hd.2)
  have he : (Real.sqrt (pairNorm d))⁻¹ = normWeight (1/2) d.1*normWeight (1/2) d.2 := by
    rw [pairNorm,Real.sqrt_mul hi.le,mul_inv_rev]
    unfold normWeight
    rw [Real.rpow_neg hi.le,Real.rpow_neg hj.le,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow]
    ring
  calc
    _ ≤ ‖(idealKernel f d.1 d.2 : ℂ)‖/(Real.sqrt (pairNorm d)) :=
      extractedScalar_bound χ _ d
    _ = _ := by
      rw [div_eq_mul_inv,he]
      unfold idealPairWeight
      rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
      ring

variable {α : Type*} [Fintype α]

/-- Forward restoration keeps the original common profiles and replaces their
two scales by the exact extracted scales. All marked factors are still present
in the fixed labelled configuration; no row-dependent coefficient is invented. -/
theorem forward_profile_row (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    normalizedRow χ D (restrictedValue S (marked S slot)) W₁ W₂ X₁ X₂ =
      ∑ T : Finset α, ∑ d ∈ divisorPool D,
        extractedScalar χ
          (fun e => (kernelOn S (fun P => forwardFactor (frozen S slot T P)) e.1 e.2 : ℂ)) d *
        normalizedRow χ (residualPool D d) (fun _ => 1) W₁ W₂
          (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  unfold normalizedRow
  rw [forward_row_expansion S slot hinj D hnz hs χ (pairProfile W₁ W₂ X₁ X₂)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro d hd
  have h := normalized_extraction χ d (divisorPool_nonzero D hnz hd) (residualPool D d)
    (fun e => (kernelOn S (fun P => forwardFactor (frozen S slot T P)) e.1 e.2 : ℂ))
    (fun _ => 1) W₁ W₂ X₁ X₂ hX₁ hX₂
  simpa only [normalizedRow,one_mul,Finset.mul_sum] using h

theorem inverse_profile_row (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    normalizedRow χ D (fun _ => 1) W₁ W₂ X₁ X₂ =
      ∑ T : Finset α, ∑ d ∈ divisorPool D,
        extractedScalar χ
          (fun e => (kernelOn S (fun P => inverseFactor (frozen S slot T P)) e.1 e.2 : ℂ)) d *
        normalizedRow χ (residualPool D d) (restrictedValue S (frozen S slot Tᶜ)) W₁ W₂
          (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  unfold normalizedRow
  simp only [one_mul]
  rw [inverse_restricted_row S slot hinj D hnz hs χ (pairProfile W₁ W₂ X₁ X₂)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro d hd
  have h := normalized_extraction χ d (divisorPool_nonzero D hnz hd) (residualPool D d)
    (fun e => (kernelOn S (fun P => inverseFactor (frozen S slot T P)) e.1 e.2 : ℂ))
    (restrictedValue S (frozen S slot Tᶜ)) W₁ W₂ X₁ X₂ hX₁ hX₂
  simpa only [normalizedRow,Finset.mul_sum] using h

end
end Candidate.SilPrior.FourthPower.KernelRowProfiles
