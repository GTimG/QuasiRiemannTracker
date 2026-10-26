/- Copyright (c) 2026 Sil. Apache-2.0.
Exact removal of common ordinary prime occurrences from a fifth-free row.
The correction B/H is applied only away from the surviving marked primes.
No conductor is enlarged and no changed multiplicity threshold is suppressed.
-/
import Candidate.FourthPower.KernelPunctureMass
import Candidate.FourthPower.KernelRowExpansion
import Candidate.FourthPower.KernelPhysicalScalars
import Candidate.FourthPower.KernelRowPools

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.FourthPower.KernelPunctureRows
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelAllocationIdentity KernelRestrictedState KernelRowExpansion KernelPunctureMass
open KernelRowProfiles KernelSelectedMass KernelRowPools
open OAI.IdealMobiusDivisorSum (idealDivisors)
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem correction_truncated : correction*truncatedSeries=1 := by
  calc
    _ = reciprocalSeries*(LocalKernels.base formalX formalY*truncatedSeries) := by
      unfold correction
      ring
    _ = reciprocalSeries*kernelSeries := rfl
    _ = 1 := reciprocal_kernel

def augmented (S H : Finset PrimeIdeal) (live : S → Bool) (P : S) : Bool :=
  live P || decide (P.val ∈ H)

theorem local_identity (S H : Finset PrimeIdeal) (live : S → Bool)
    (hdisjoint : ∀ P : S, P.val ∈ H → live P=false) (P : S) :
    atPrime H P.val*(if live P then (1 : LocalSeries) else truncatedSeries) =
      if augmented S H live P then 1 else truncatedSeries := by
  by_cases h : P.val ∈ H
  · simp [atPrime,augmented,h,hdisjoint P h,correction_truncated]
  · simp [atPrime,augmented,h]

/-- The common puncture is literal avoidance in both ordinary factors. -/
theorem augmented_restriction (S H : Finset PrimeIdeal) (live : S → Bool) (I J : Id) :
    Restricted S (augmented S H live) I J ↔
      Restricted S live I J ∧ ∀ P : S, P.val ∈ H → ¬P.val.val ∣ I*J := by
  simp only [Restricted,augmented,Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hf,ha⟩
    exact ⟨⟨hf,fun P hP => ha P (Or.inl hP)⟩,fun P hP => ha P (Or.inr hP)⟩
  · rintro ⟨⟨hf,hl⟩,hh⟩
    exact ⟨hf,fun P hP => hP.elim (hl P) (hh P)⟩

theorem divisor_identity (S H : Finset PrimeIdeal) (live : S → Bool)
    (hdisjoint : ∀ P : S, P.val ∈ H → live P=false)
    {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) (hs : pairSupport I J ⊆ primeValues S) :
    (∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
      kernelOn S (fun P => atPrime H P.val) d.1 d.2*
        kernelOn S (fun P => if live P then 1 else truncatedSeries)
          (cofactorPair I J d).1 (cofactorPair I J d).2) =
      if Restricted S (augmented S H live) I J then 1 else 0 := by
  rw [divisor_convolution S _ _ hI hJ hs]
  simp_rw [local_identity S H live hdisjoint]
  exact restricted_kernel S (augmented S H live) hI hJ hs

theorem complex_divisor_identity (S H : Finset PrimeIdeal) (live : S → Bool)
    (hdisjoint : ∀ P : S, P.val ∈ H → live P=false)
    (n : IdealPair) (hn : n.1 ≠ 0 ∧ n.2 ≠ 0) (hs : pairSupport n.1 n.2 ⊆ primeValues S) :
    restrictedValue S (augmented S H live) n =
      ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
        (kernelOn S (fun P => atPrime H P.val) d.1 d.2 : ℂ)*
          (kernelOn S (fun P => if live P then 1 else truncatedSeries)
            (cofactorPair n.1 n.2 d).1 (cofactorPair n.1 n.2 d).2 : ℂ) := by
  have hh := congrArg (fun z : ℤ => (z : ℂ)) (divisor_identity S H live hdisjoint hn.1 hn.2 hs)
  push_cast at hh
  by_cases hr : Restricted S (augmented S H live) n.1 n.2
  · simpa only [restrictedValue,ite_eq_left hr] using hh.symm
  · simpa only [restrictedValue,ite_eq_right hr] using hh.symm

theorem residual_value (S : Finset PrimeIdeal) (live : S → Bool)
    (n : IdealPair) (hn : n.1 ≠ 0 ∧ n.2 ≠ 0) (hs : pairSupport n.1 n.2 ⊆ primeValues S) :
    (kernelOn S (fun P => if live P then 1 else truncatedSeries) n.1 n.2 : ℂ) =
      restrictedValue S live n := by
  rw [restricted_kernel S live hn.1 hn.2 hs]
  by_cases hr : Restricted S live n.1 n.2 <;> simp [restrictedValue,hr]

/-- This finite row identity retains the reconstructed original profile.
After reindexing, the residual has the original fifth-free threshold T.
The correction series, rather than an unproved threshold equivalence, pays
for all higher artificial divisor exponents. -/
theorem row_expansion (S H : Finset PrimeIdeal) (live : S → Bool)
    (hdisjoint : ∀ P : S, P.val ∈ H → live P=false) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (f : IdealPair → ℂ) :
    (∑ n ∈ D, restrictedValue S (augmented S H live) n*pairCharacter χ n*f n) =
      ∑ d ∈ divisorPool D,
        (kernelOn S (fun P => atPrime H P.val) d.1 d.2 : ℂ)*pairCharacter χ d*
          ∑ a ∈ residualPool D d, restrictedValue S live a*pairCharacter χ a*f (multiplyPair d a) := by
  calc
    _ = ∑ n ∈ D, ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
        (kernelOn S (fun P => atPrime H P.val) d.1 d.2 : ℂ)*
          (kernelOn S (fun P => if live P then 1 else truncatedSeries)
            (cofactorPair n.1 n.2 d).1 (cofactorPair n.1 n.2 d).2 : ℂ)*pairCharacter χ n*f n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [complex_divisor_identity S H live hdisjoint n (hnz n hn) (hs n hn)]
      simp only [Finset.sum_mul]
    _ = ∑ d ∈ divisorPool D,
        (kernelOn S (fun P => atPrime H P.val) d.1 d.2 : ℂ)*pairCharacter χ d*
          ∑ a ∈ residualPool D d,
            (kernelOn S (fun P => if live P then 1 else truncatedSeries) a.1 a.2 : ℂ)*
              pairCharacter χ a*f (multiplyPair d a) := finite_row_reindex D hnz χ f
        (fun d => (kernelOn S (fun P => atPrime H P.val) d.1 d.2 : ℂ))
        (fun a => (kernelOn S (fun P => if live P then 1 else truncatedSeries) a.1 a.2 : ℂ))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      have has := residualPool_supported S D hnz hs ha
      rw [residual_value S live a ⟨has.1,has.2.1⟩ has.2.2]

/-- Original profiles and frequencies are retained at the exact shortened scales. -/
theorem normalized_row_expansion (S H : Finset PrimeIdeal) (live : S → Bool)
    (hdisjoint : ∀ P : S, P.val ∈ H → live P=false) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    normalizedRow χ D (restrictedValue S (augmented S H live)) W₁ W₂ X₁ X₂ =
      ∑ d ∈ divisorPool D,
        extractedScalar χ (fun e => (kernelOn S (fun P => atPrime H P.val) e.1 e.2 : ℂ)) d*
          normalizedRow χ (residualPool D d) (restrictedValue S live) W₁ W₂
            (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  unfold normalizedRow
  rw [row_expansion S H live hdisjoint D hnz hs χ (pairProfile W₁ W₂ X₁ X₂)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simpa only [normalizedRow,Finset.mul_sum] using
    normalized_extraction χ d (divisorPool_nonzero D hnz hd) (residualPool D d)
      (fun e => (kernelOn S (fun P => atPrime H P.val) e.1 e.2 : ℂ))
      (restrictedValue S live) W₁ W₂ X₁ X₂ hX₁ hX₂

theorem actual_scalar_bound (S H : Finset PrimeIdeal) (χ : Character) (d : IdealPair)
    (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    ‖extractedScalar χ (fun e => (kernelOn S (fun P => atPrime H P.val) e.1 e.2 : ℂ)) d‖ ≤
      idealWeight S (fun P => atPrime H P.val) (1/2) (1/2) d :=
  KernelPhysicalScalars.extracted_central_bound χ S _ d hd

theorem full_rectangle (S H : Finset PrimeIdeal) (live : S → Bool)
    (hdisjoint : ∀ P : S, P.val ∈ H → live P=false)
    (χ : Character) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    normalizedRow χ (supportedRectangle S b X₁ X₂)
      (restrictedValue S (augmented S H live)) W₁ W₂ X₁ X₂ =
      ∑ d ∈ divisorPool (supportedRectangle S b X₁ X₂),
        extractedScalar χ (fun e => (kernelOn S (fun P => atPrime H P.val) e.1 e.2 : ℂ)) d*
          normalizedRow χ (supportedRectangle S b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2))
            (restrictedValue S live) W₁ W₂ (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  rw [normalized_row_expansion S H live hdisjoint _ (fun _ h => supportedRectangle_nonzero h)
    (fun _ h => (Finset.mem_filter.mp h).2) χ W₁ W₂ X₁ X₂ hX₁ hX₂]
  apply Finset.sum_congr rfl
  intro d hd
  rw [residual_rectangle hd]

end
end Candidate.FourthPower.KernelPunctureRows
