/- Copyright (c) 2026 Sil. Apache-2.0.
Interpret the local target and residual series as the literal fifth-free
condition and avoidance of live marked prime ideals.
-/
import Candidate.Feedback.FourthPower.KernelAllocationIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.KernelRestrictedState
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelIdeal KernelAllocationIdentity
open OAI.IdealMobiusDivisorSum (idealDivisors)
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

theorem prime_not_dvd_iff (P : PrimeIdeal) {I : Id} (hI : I ≠ 0) :
    ¬P.val ∣ I ↔ valuation I P.val=0 := by
  have he : P.val ∣ I ↔ 1 ≤ valuation I P.val := by
    constructor
    · intro h
      have hh := (dvd_iff_valuation_le P.property.ne_zero hI).mp h P.val
      simpa only [valuation_prime,ite_true] using hh
    · intro h
      apply (dvd_iff_valuation_le P.property.ne_zero hI).mpr
      intro Q
      rw [valuation_prime]
      split_ifs with hQ
      · subst Q
        exact h
      · exact Nat.zero_le _
  rw [he]
  omega

theorem restricted_coefficient (marked : Bool) (i j : ℕ) :
    MvPowerSeries.coeff (exponent i j) (if marked then (1 : LocalSeries) else truncatedSeries) =
      if i+j<5 ∧ (marked=true → i+j=0) then 1 else 0 := by
  cases marked with
  | false => simp [truncated_coefficient_at]
  | true =>
    by_cases he : i+j=0
    · have hi : i=0 := by omega
      have hj : j=0 := by omega
      subst i
      subst j
      norm_num [exponent]
    · have hn : exponent i j ≠ 0 := by
        intro hh
        obtain ⟨hi,hj⟩ := (exponent_eq_zero i j).mp hh
        omega
      simp [MvPowerSeries.coeff_one,hn]
      omega

def Restricted (S : Finset PrimeIdeal) (live : S → Bool) (I J : Id) : Prop :=
  SexticSieve.PowerFree 5 (I*J) ∧ ∀ P : S, live P=true → ¬P.val.val ∣ I*J

theorem restricted_kernel (S : Finset PrimeIdeal) (live : S → Bool)
    {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) (hs : pairSupport I J ⊆ primeValues S) :
    kernelOn S (fun P => if live P then 1 else truncatedSeries) I J =
      if Restricted S live I J then 1 else 0 := by
  have hf : SexticSieve.PowerFree 5 (I*J) ↔
      ∀ P : S, valuation I P.val.val+valuation J P.val.val<5 := by
    rw [powerFree_mul_iff_on_support hI hJ (primeValues S) hs]
    constructor
    · intro h P
      exact h P.val.val (Finset.mem_image.mpr ⟨P.val,P.property,rfl⟩)
    · intro h P hP
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
      exact h ⟨Q,hQ⟩
  have hn (P : S) : ¬P.val.val ∣ I*J ↔ valuation I P.val.val+valuation J P.val.val=0 := by
    rw [prime_not_dvd_iff P.val (mul_ne_zero hI hJ),valuation_mul hI hJ]
  have he : (∀ P : S, valuation I P.val.val+valuation J P.val.val<5 ∧
      (live P=true → valuation I P.val.val+valuation J P.val.val=0)) ↔ Restricted S live I J := by
    constructor
    · intro h
      exact ⟨hf.mpr (fun P => (h P).1),fun P hp => (hn P).mpr ((h P).2 hp)⟩
    · rintro ⟨hfree,havoid⟩ P
      exact ⟨hf.mp hfree P,fun hp => (hn P).mp (havoid P hp)⟩
  unfold kernelOn
  simp_rw [localExponent,restricted_coefficient]
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one,Finset.mem_univ,forall_const,he]

/-- The forward coefficient is precisely the intended restriction. -/
theorem forward_restricted_identity (S : Finset PrimeIdeal) (marked : S → Bool)
    {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) (hs : pairSupport I J ⊆ primeValues S) :
    (∑ a ∈ Fintype.piFinset (fun P => choices (marked P)),
      ∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
        kernelOn S (fun P => forwardFactor (a P)) d.1 d.2*
        kernelOn S (fun _P => ordinarySeries) (cofactorPair I J d).1 (cofactorPair I J d).2) =
      if Restricted S marked I J then 1 else 0 := by
  rw [forward_allocated_identity S marked hI hJ hs,restricted_kernel S marked hI hJ hs]

/-- The residual forbids only live marked primes. Extracted marked primes
retain T, rather than an artificial ordinary puncture. -/
theorem inverse_residual_restricted (S : Finset PrimeIdeal) (marked freeze : S → Bool)
    {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0) (hs : pairSupport I J ⊆ primeValues S) :
    kernelOn S (fun P => inverseResidual (marked P) (freeze P)) I J =
      if Restricted S (fun P => marked P && !freeze P) I J then 1 else 0 :=
  restricted_kernel S (fun P => marked P && !freeze P) hI hJ hs

end
end Candidate.Feedback.FourthPower.KernelRestrictedState
