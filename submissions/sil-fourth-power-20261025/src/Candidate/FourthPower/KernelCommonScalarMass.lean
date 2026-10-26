/- Copyright (c) 2026 Sil. Apache-2.0.
One common positive majorant for every physical character, before taking
the physical norm. The reflected cost uses the whole frozen product.
-/
import Candidate.FourthPower.KernelPhysicalScalars

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelCommonScalarMass
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelAllocationIdentity KernelActualMass KernelPhysicalScalars
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

def weight (inv : Bool) (B : ℝ) (S : Finset PrimeIdeal) (slot : α → S) (d : Id × Id) : ℝ :=
  (2*B)^Fintype.card α *
    frozenMass S (ordinarySeriesFor inv) (markedSeriesFor inv) (1/2) (1/2) (1/2) slot d

theorem weight_nonneg (inv : Bool) (B : ℝ) (hB : 0 ≤ B) (S : Finset PrimeIdeal)
    (slot : α → S) (d : Id × Id) : 0 ≤ weight inv B S slot d :=
  mul_nonneg (by positivity) (frozenMass_nonneg _ _ _ _ _ _ _ _)

/-- This weight has no character, profile, or row index. -/
theorem scalar_le_weight (inv : Bool) (B : ℝ) (hB : 0 ≤ B) (S : Finset PrimeIdeal)
    (χ : Character) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (hP : ∀ i, 0 < P i)
    (hp : ∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i)
    (hβ : ∀ i I, I ∈ pool i → ‖β i I‖ ≤ B)
    (slot : α → S) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    ‖scalar χ S (ordinarySeriesFor inv) (markedSeriesFor inv) pool β P slot d‖ ≤
      weight inv B S slot d :=
  scalar_bound χ S _ _ pool β P B hB hP hp hβ slot d hd

theorem weight_subpower (inv : Bool) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot, weight inv B S slot d) ≤ C*X^ε := by
  have hm : ∃ M : ℝ, 0 < M ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot,
        frozenMass S (ordinarySeriesFor inv) (markedSeriesFor inv) (1/2) (1/2) (1/2) slot d) ≤ M*X^ε := by
    cases inv
    · exact forward_central_subpower ε hε
    · exact inverse_central_subpower ε hε
  obtain ⟨M,hM,hm⟩ := hm
  refine ⟨(2*B+1)^Fintype.card α*M,mul_pos (by positivity) hM,?_⟩
  intro X hX S hS F hinj D hd hs
  unfold weight
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ (2*B)^Fintype.card α*(M*X^ε) :=
      mul_le_mul_of_nonneg_left (hm X hX S hS F hinj D hd hs) (by positivity)
    _ ≤ ((2*B+1)^Fintype.card α*M)*X^ε := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) _)
        (mul_nonneg hM.le (Real.rpow_nonneg (zero_le_one.trans hX) _))

/-- The additional sixth-root reflected ratio is summable with the same
arbitrarily small power, including all supplying frozen marked primes. -/
theorem reflected_weight_subpower (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot,
        weight false B S slot d*(1+criticalRatio S slot d)) ≤ C*X^ε := by
  obtain ⟨M,hM,hm⟩ := forward_central_subpower (α := α) ε hε
  obtain ⟨N,hN,hn⟩ := forward_critical_subpower (α := α) ε hε
  refine ⟨(2*B+1)^Fintype.card α*(M+N),mul_pos (by positivity) (add_pos hM hN),?_⟩
  intro X hX S hS F hinj D hd hs
  have he (slot) (hslot : slot ∈ F) (d) (hdd : d ∈ D slot) :
      weight false B S slot d*(1+criticalRatio S slot d) =
        (2*B)^Fintype.card α*(ForwardCentralMass S slot d+ForwardCriticalMass S slot d) := by
    change ((2*B)^Fintype.card α*ForwardCentralMass S slot d)*(1+criticalRatio S slot d) = _
    rw [← reflected_weight S slot d (hd slot hslot d hdd)]
    ring
  calc
    _ = (2*B)^Fintype.card α*((∑ slot ∈ F, ∑ d ∈ D slot, ForwardCentralMass S slot d)+
        (∑ slot ∈ F, ∑ d ∈ D slot, ForwardCriticalMass S slot d)) := by
      calc
        _ = ∑ slot ∈ F, ∑ d ∈ D slot,
            (2*B)^Fintype.card α*(ForwardCentralMass S slot d+ForwardCriticalMass S slot d) :=
          Finset.sum_congr rfl (fun slot hslot => Finset.sum_congr rfl (fun d hdd => he slot hslot d hdd))
        _ = _ := by simp_rw [← Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ (2*B)^Fintype.card α*((M+N)*X^ε) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [add_mul]
      exact add_le_add (hm X hX S hS F hinj D hd hs) (hn X hX S hS F hinj D hd hs)
    _ ≤ ((2*B+1)^Fintype.card α*(M+N))*X^ε := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) _)
        (mul_nonneg (add_nonneg hM.le hN.le) (Real.rpow_nonneg (zero_le_one.trans hX) _))

end
end Candidate.FourthPower.KernelCommonScalarMass
