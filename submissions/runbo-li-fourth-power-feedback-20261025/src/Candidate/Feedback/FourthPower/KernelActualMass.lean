/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform absolute mass of actual extracted ideal pairs and frozen marked labels.
The kernel at a supplying prime is exactly the marked correction. Arbitrary
finite cutoffs and restrictions are allowed without changing the constant.
-/
import Candidate.Feedback.FourthPower.KernelSelectedLocal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.KernelActualMass
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelAllocationIdentity KernelLabelledSlots KernelSelectedMass KernelSelectedLocal
open KernelForwardMass SieveDescent
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

def frozenMass (S : Finset PrimeIdeal) (A B : LocalSeries) (s t v : ℝ)
    (slot : α → S) (d : Id × Id) : ℝ :=
  idealWeight S (fun P => if marked S slot P then B else A) s t d *
    ∏ i : α, normWeight v (slot i).val.val

theorem frozenMass_nonneg (S : Finset PrimeIdeal) (A B : LocalSeries) (s t v : ℝ)
    (slot : α → S) (d : Id × Id) : 0 ≤ frozenMass S A B s t v slot d := by
  apply mul_nonneg (idealWeight_nonneg _ _ _ _ _)
  exact Finset.prod_nonneg (fun _ _ => by unfold normWeight; positivity)

/-- The fixed-label estimate uses the same kernelOn as the exact row identity,
not a separately declared configuration with an assumed matching weight. -/
theorem fixed_labels_bound (S : Finset PrimeIdeal) (hS : ∀ P ∈ S, Supported P.val)
    (A B : LocalSeries) (s t u v σ C K : ℝ)
    (hσ : 1 < σ) (hC : 0 ≤ C) (hK : 0 ≤ K) (huv : u+v=1)
    (hA : ∀ P ∈ S, ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight A s t P ij) ≤ 1+C*(Ideal.absNorm P.val : ℝ)^(-σ))
    (hB : ∀ P ∈ S, ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight B s t P ij) ≤ K*(Ideal.absNorm P.val : ℝ)^(-u))
    (slot : α → S) (hinj : Function.Injective slot) (D : Finset (Id × Id))
    (hd : ∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (hs : ∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) :
    (∑ d ∈ D, frozenMass S A B s t v slot d) ≤
      Real.exp (C*rootMass σ)*∏ i : α, K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹ := by
  have he (P : S) : K*(Ideal.absNorm P.val.val : ℝ)^(-u)*normWeight v P.val.val =
      K*(Ideal.absNorm P.val.val : ℝ)⁻¹ := by
    have hp : (0 : ℝ) < Ideal.absNorm P.val.val :=
      zero_lt_one.trans_le (ideal_norm_one_le P.val.property.ne_zero)
    unfold normWeight
    rw [mul_assoc,← Real.rpow_add hp,show -u + -v = -1 by linarith [huv],Real.rpow_neg_one]
  have hh := selected_ideal_mass S slot hinj A B s t
    (fun P => 1+C*(Ideal.absNorm P.val.val : ℝ)^(-σ))
    (fun P => K*(Ideal.absNorm P.val.val : ℝ)^(-u))
    (fun P => normWeight v P.val.val)
    (fun P => le_add_of_nonneg_right (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    (fun P => by positivity) (fun P => by unfold normWeight; positivity)
    (fun P T => hA P.val P.property T) (fun P T => hB P.val P.property T) D hd hs
  simp_rw [he] at hh
  have ho : (∏ P : S, (1+C*(Ideal.absNorm P.val.val : ℝ)^(-σ))) ≤ Real.exp (C*rootMass σ) := by
    have hx : (∏ P : S, (1+C*(Ideal.absNorm P.val.val : ℝ)^(-σ))) =
        ∏ P ∈ primeValues S, (1+C*(Ideal.absNorm P : ℝ)^(-σ)) := by
      unfold primeValues
      rw [Finset.prod_image (by intro P _ Q _ h; exact Subtype.val_injective h)]
      exact (Finset.prod_subtype (p := fun P => P ∈ S) S (by simp)
        (fun P : PrimeIdeal => 1+C*(Ideal.absNorm P.val : ℝ)^(-σ))).symm
    rw [hx]
    apply finite_euler_mass σ C hσ hC (primeValues S)
    intro P hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    exact hS Q hQ
  unfold frozenMass
  rw [← Finset.sum_mul]
  exact hh.trans (mul_le_mul_of_nonneg_right ho (Finset.prod_nonneg (fun i _ => by positivity)))

/-- The same C works for every injective marked pool, and every residual
ideal cutoff that may depend on the frozen assignment. -/
theorem selected_subpower (A B : LocalSeries) (s t u v σ C K ε : ℝ)
    (hσ : 1 < σ) (hC : 0 ≤ C) (hK : 0 ≤ K) (huv : u+v=1) (hε : 0 < ε)
    (hA : ∀ P : PrimeIdeal, Supported P.val → ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight A s t P ij) ≤ 1+C*(Ideal.absNorm P.val : ℝ)^(-σ))
    (hB : ∀ P : PrimeIdeal, Supported P.val → ∀ T : Finset (ℕ × ℕ),
      (∑ ij ∈ T, localWeight B s t P ij) ≤ K*(Ideal.absNorm P.val : ℝ)^(-u)) :
    ∃ M : ℝ, 0 < M ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot, frozenMass S A B s t v slot d) ≤ M*X^ε := by
  obtain ⟨M,hM,hbound⟩ := prime_assignments_subpower (α := α) K ε hK hε
  refine ⟨Real.exp (C*rootMass σ)*M,mul_pos (Real.exp_pos _) hM,?_⟩
  intro X hX S hS F hinj D hd hs
  calc
    _ ≤ ∑ slot ∈ F, Real.exp (C*rootMass σ)*∏ i : α,
        K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹ := Finset.sum_le_sum (fun slot hslot =>
      fixed_labels_bound S (fun P hP => (hS P hP).1) A B s t u v σ C K hσ hC hK huv
        (fun P hP T => hA P (hS P hP).1 T) (fun P hP T => hB P (hS P hP).1 T)
        slot (hinj slot hslot) (D slot) (hd slot hslot) (hs slot hslot))
    _ = Real.exp (C*rootMass σ)*(∑ slot ∈ F, ∏ i : α,
        K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (C*rootMass σ)*(∑ slot : α → S, ∏ i : α,
        K*(Ideal.absNorm (slot i).val.val : ℝ)⁻¹) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
        (fun slot _ _ => Finset.prod_nonneg (fun i _ => by positivity))) (Real.exp_pos _).le
    _ ≤ Real.exp (C*rootMass σ)*(M*X^ε) :=
      mul_le_mul_of_nonneg_left (hbound X hX S hS) (Real.exp_pos _).le
    _ = _ := by ring

def ForwardCentralMass (S : Finset PrimeIdeal) (slot : α → S) (d : Id × Id) : ℝ :=
  frozenMass S kernelSeries (LocalKernels.base formalX formalY-kernelSeries) (1/2) (1/2) (1/2) slot d

def ForwardCriticalMass (S : Finset PrimeIdeal) (slot : α → S) (d : Id × Id) : ℝ :=
  frozenMass S kernelSeries (LocalKernels.base formalX formalY-kernelSeries) (2/3) (1/3) (2/3) slot d

def InverseCentralMass (S : Finset PrimeIdeal) (slot : α → S) (d : Id × Id) : ℝ :=
  frozenMass S reciprocalSeries KernelInverseMarkedMass.markedSeries (1/2) (1/2) (1/2) slot d

/-- The complete actual central forward mass, including all frozen labels. -/
theorem forward_central_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot, ForwardCentralMass S slot d) ≤ M*X^ε := by
  apply selected_subpower kernelSeries (LocalKernels.base formalX formalY-kernelSeries)
    (1/2) (1/2) (1/2) (1/2) (5/2) 11 14 ε (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hε
  · intro P _ T
    convert ordinary_local P (1/2) (1/2) (1/2) (by norm_num) le_rfl le_rfl T using 1; norm_num
  · intro P _ T
    exact marked_local P (1/2) (1/2) (1/2) (by norm_num) le_rfl le_rfl T

/-- The reflected critical ratio is paid with actual exponents 2/3,1/3,2/3. -/
theorem forward_critical_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot, ForwardCriticalMass S slot d) ≤ M*X^ε := by
  apply selected_subpower kernelSeries (LocalKernels.base formalX formalY-kernelSeries)
    (2/3) (1/3) (1/3) (2/3) (5/3) 11 14 ε (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hε
  · intro P _ T
    convert ordinary_local P (2/3) (1/3) (1/3) (by norm_num) (by norm_num) le_rfl T using 1; norm_num
  · intro P _ T
    exact marked_local P (2/3) (1/3) (1/3) (by norm_num) (by norm_num) le_rfl T

/-- The infinite inverse local series is fully included, with finite arbitrary
ideal cutoffs. Its supplying primes retain the correct inverse marked series. -/
theorem inverse_central_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ slot ∈ F, Function.Injective slot) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ slot ∈ F, ∀ d ∈ D slot, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ slot ∈ F, ∀ d ∈ D slot, pairSupport d.1 d.2 ⊆ primeValues S) →
      (∑ slot ∈ F, ∑ d ∈ D slot, InverseCentralMass S slot d) ≤ M*X^ε := by
  exact selected_subpower reciprocalSeries KernelInverseMarkedMass.markedSeries
    (1/2) (1/2) (1/2) (1/2) (3/2) 400 10206 ε (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hε inverse_ordinary_local inverse_marked_local

end
end Candidate.Feedback.FourthPower.KernelActualMass
