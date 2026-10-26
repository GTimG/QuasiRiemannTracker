/- Copyright (c) 2026 Sil. Apache-2.0.
Literal finite physical-row expansions for the new fifth-free kernels.
Only generic divisor reindexing is reused from PR69. Its old squarefree
kernel and its endpoint are not substituted for the present restriction.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.KernelLabelledSlots
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.KernelNaturalSlots
import Submissions.hailey_collet_1252270103.Record1252270103KernelMass.FiniteReindex

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelRowExpansion
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open OAI.IdealMobiusDivisorSum (idealDivisors)
open KernelFormal KernelAllocationIdentity KernelRestrictedState KernelLabelledSlots
local notation "Id" => Ideal ActualEisensteinCubic.O

def pairCharacter (χ : Character) (n : IdealPair) : ℂ := idealCoeff χ (n.1*n.2)

theorem pairCharacter_multiply (χ : Character) (d a : IdealPair) :
    pairCharacter χ (multiplyPair d a) = pairCharacter χ d*pairCharacter χ a :=
  character_pair_multiply (idealCoeff χ).toMonoidHom d a

/-- The extracted whole-character value stays outside the residual row.
The profile is evaluated at the reconstructed original indices exactly. -/
theorem finite_row_reindex (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0) (χ : Character)
    (f k r : IdealPair → ℂ) :
    (∑ n ∈ D, ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
      k d*r (cofactorPair n.1 n.2 d)*pairCharacter χ n*f n) =
      ∑ d ∈ divisorPool D, k d*pairCharacter χ d*
        ∑ a ∈ residualPool D d, r a*pairCharacter χ a*f (multiplyPair d a) := by
  rw [finite_divisor_reindex D hnz
    (fun n d a => k d*r a*pairCharacter χ n*f n)]
  simp_rw [pairCharacter_multiply]
  rw [expandedPairs_grouped D
    (fun d a => k d*r a*(pairCharacter χ d*pairCharacter χ a)*f (multiplyPair d a))]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem ordinary_kernel_one (S : Finset PrimeIdeal) (I J : Id) :
    kernelOn S (fun _ => ordinarySeries) I J=1 := by
  simp [kernelOn,coeff_ordinarySeries]

def restrictedValue (S : Finset PrimeIdeal) (live : S → Bool) (n : IdealPair) : ℂ :=
  if Restricted S live n.1 n.2 then 1 else 0

variable {α : Type*} [Fintype α]

theorem forward_row_expansion (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (f : IdealPair → ℂ) :
    (∑ n ∈ D, restrictedValue S (marked S slot) n*pairCharacter χ n*f n) =
      ∑ T : Finset α, ∑ d ∈ divisorPool D,
        (kernelOn S (fun P => forwardFactor (frozen S slot T P)) d.1 d.2 : ℂ)*
          pairCharacter χ d*∑ a ∈ residualPool D d, pairCharacter χ a*f (multiplyPair d a) := by
  have hp (n : IdealPair) (hn : n ∈ D) :
      restrictedValue S (marked S slot) n =
        ∑ T : Finset α, ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
          (kernelOn S (fun P => forwardFactor (frozen S slot T P)) d.1 d.2 : ℂ) := by
    have h := forward_labelled_identity S slot hinj (hnz n hn).1 (hnz n hn).2 (hs n hn)
    simp only [ordinary_kernel_one,mul_one] at h
    have hc := congrArg (fun z : ℤ => (z : ℂ)) h
    push_cast at hc
    exact hc.symm
  calc
    _ = ∑ n ∈ D, ∑ T : Finset α, ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
        (kernelOn S (fun P => forwardFactor (frozen S slot T P)) d.1 d.2 : ℂ)*
          pairCharacter χ n*f n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hp n hn]
      simp only [Finset.sum_mul]
    _ = ∑ T : Finset α, ∑ n ∈ D, ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
        (kernelOn S (fun P => forwardFactor (frozen S slot T P)) d.1 d.2 : ℂ)*
          pairCharacter χ n*f n := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T _
      simpa only [mul_one,one_mul] using finite_row_reindex D hnz χ f
        (fun d => (kernelOn S (fun P => forwardFactor (frozen S slot T P)) d.1 d.2 : ℂ))
        (fun _ => 1)

/-- The inverse residual is the actual live-label restriction whenever the
residual indices are nonzero and have the prescribed finite prime support. -/
theorem inverse_residual_value (S : Finset PrimeIdeal) (slot : α → S) (T : Finset α)
    {a : IdealPair} (ha : a.1 ≠ 0 ∧ a.2 ≠ 0)
    (hs : pairSupport a.1 a.2 ⊆ primeValues S) :
    (kernelOn S (fun P => if frozen S slot Tᶜ P then 1 else truncatedSeries) a.1 a.2 : ℂ) =
      restrictedValue S (frozen S slot Tᶜ) a := by
  rw [restricted_kernel S (frozen S slot Tᶜ) ha.1 ha.2 hs]
  simp [restrictedValue]

/-- Divisor reindexing preserves nonzero indices and the original finite
prime enclosure on both extracted and residual pairs. -/
theorem residualPool_supported (S : Finset PrimeIdeal) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    {d a : IdealPair} (ha : a ∈ residualPool D d) :
    a.1 ≠ 0 ∧ a.2 ≠ 0 ∧ pairSupport a.1 a.2 ⊆ primeValues S := by
  obtain ⟨p,hp,hpa⟩ := Finset.mem_image.mp ha
  obtain ⟨n,hn,hpn⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hp).1
  have he := expandedAt_reconstruct (hnz n hn) hpn
  have hi : a.1 ∣ n.1 := by
    rw [← he,← hpa]
    exact dvd_mul_left _ _
  have hj : a.2 ∣ n.2 := by
    rw [← he,← hpa]
    exact dvd_mul_left _ _
  have hai := ne_zero_of_dvd_ne_zero (hnz n hn).1 hi
  have haj := ne_zero_of_dvd_ne_zero (hnz n hn).2 hj
  refine ⟨hai,haj,?_⟩
  exact (Finset.union_subset_union
    (primeSupport_subset_of_dvd hai (hnz n hn).1 hi)
    (primeSupport_subset_of_dvd haj (hnz n hn).2 hj)).trans (hs n hn)

theorem inverse_row_expansion (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (f : IdealPair → ℂ) :
    (∑ n ∈ D, pairCharacter χ n*f n) =
      ∑ T : Finset α, ∑ d ∈ divisorPool D,
        (kernelOn S (fun P => inverseFactor (frozen S slot T P)) d.1 d.2 : ℂ)*
          pairCharacter χ d*∑ a ∈ residualPool D d,
            (kernelOn S (fun P => if frozen S slot Tᶜ P then 1 else truncatedSeries) a.1 a.2 : ℂ)*
              pairCharacter χ a*f (multiplyPair d a) := by
  have hp (n : IdealPair) (hn : n ∈ D) :
      (1 : ℂ) = ∑ T : Finset α, ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
        (kernelOn S (fun P => inverseFactor (frozen S slot T P)) d.1 d.2 : ℂ)*
          (kernelOn S (fun P => if frozen S slot Tᶜ P then 1 else truncatedSeries)
            (cofactorPair n.1 n.2 d).1 (cofactorPair n.1 n.2 d).2 : ℂ) := by
    have h := congrArg (fun z : ℤ => (z : ℂ))
      (inverse_labelled_identity S slot hinj (hnz n hn).1 (hnz n hn).2 (hs n hn))
    push_cast at h
    exact h.symm
  calc
    _ = ∑ n ∈ D, ∑ T : Finset α, ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
        (kernelOn S (fun P => inverseFactor (frozen S slot T P)) d.1 d.2 : ℂ)*
          (kernelOn S (fun P => if frozen S slot Tᶜ P then 1 else truncatedSeries)
            (cofactorPair n.1 n.2 d).1 (cofactorPair n.1 n.2 d).2 : ℂ)*pairCharacter χ n*f n := by
      apply Finset.sum_congr rfl
      intro n hn
      conv_lhs => rw [← one_mul (pairCharacter χ n),hp n hn]
      simp only [Finset.sum_mul]
    _ = ∑ T : Finset α, ∑ n ∈ D, ∑ d ∈ idealDivisors n.1 ×ˢ idealDivisors n.2,
        (kernelOn S (fun P => inverseFactor (frozen S slot T P)) d.1 d.2 : ℂ)*
          (kernelOn S (fun P => if frozen S slot Tᶜ P then 1 else truncatedSeries)
            (cofactorPair n.1 n.2 d).1 (cofactorPair n.1 n.2 d).2 : ℂ)*pairCharacter χ n*f n :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T _
      exact finite_row_reindex D hnz χ f
        (fun d => (kernelOn S (fun P => inverseFactor (frozen S slot T P)) d.1 d.2 : ℂ))
        (fun a => (kernelOn S (fun P => if frozen S slot Tᶜ P then 1 else truncatedSeries) a.1 a.2 : ℂ))

/-- Unrestricted rows are an exact sum of rows restricted only at the live
labels. The supplying frozen primes do not become ordinary punctures. -/
theorem inverse_restricted_row (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (D : Finset IdealPair)
    (hnz : ∀ n ∈ D, n.1 ≠ 0 ∧ n.2 ≠ 0)
    (hs : ∀ n ∈ D, pairSupport n.1 n.2 ⊆ primeValues S)
    (χ : Character) (f : IdealPair → ℂ) :
    (∑ n ∈ D, pairCharacter χ n*f n) =
      ∑ T : Finset α, ∑ d ∈ divisorPool D,
        (kernelOn S (fun P => inverseFactor (frozen S slot T P)) d.1 d.2 : ℂ)*
          pairCharacter χ d*∑ a ∈ residualPool D d,
            restrictedValue S (frozen S slot Tᶜ) a*pairCharacter χ a*f (multiplyPair d a) := by
  rw [inverse_row_expansion S slot hinj D hnz hs χ f]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have has := residualPool_supported S D hnz hs ha
  rw [inverse_residual_value S slot T ⟨has.1,has.2.1⟩ has.2.2]

end
end Candidate.FourthPower.KernelRowExpansion
