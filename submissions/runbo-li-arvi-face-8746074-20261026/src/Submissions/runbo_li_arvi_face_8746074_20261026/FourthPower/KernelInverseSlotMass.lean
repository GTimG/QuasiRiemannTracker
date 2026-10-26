/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform central inverse mass for any fixed finite labelled slot type.
Coefficient cutoffs and restrictions are chosen after the common constant.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.KernelInverseMarkedMass

set_option autoImplicit false
namespace Candidate.FourthPower.KernelInverseSlotMass
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103KernelMass
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open SieveDescent SieveCentralReference KernelInverseMarkedMass
local notation "Id" => Ideal ActualEisensteinCubic.O

abbrev Choice (S : Finset PrimeIdeal) (T : S → Finset (ℕ × ℕ)) := Option (Σ P : S, T P)

def choiceWeight (S : Finset PrimeIdeal) (T : S → Finset (ℕ × ℕ)) : Choice S T → ℝ
  | none => 1
  | some q => localMarkedMass ((Ideal.absNorm q.1.val.val : ℝ)^(-(1/2 : ℝ))) q.2.val

theorem choiceWeight_nonneg (S : Finset PrimeIdeal) (T : S → Finset (ℕ × ℕ)) (q : Choice S T) :
    0 ≤ choiceWeight S T q := by
  cases q with
  | none => exact zero_le_one
  | some q => exact localMarkedMass_nonneg (by positivity) q.2.val

theorem marked_pool_mass (δ : ℝ) (hδ : 0 < δ) (X : ℝ) (hX : 0 < X)
    (S : Finset PrimeIdeal)
    (hS : ∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X)
    (T : S → Finset (ℕ × ℕ)) :
    (∑ q : (Σ P : S, T P),
      localMarkedMass ((Ideal.absNorm q.1.val.val : ℝ)^(-(1/2 : ℝ))) q.2.val) ≤
      10206*X^δ*rootMass (1+δ) := by
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ P : S, 10206*(Ideal.absNorm P.val.val : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro P hP
      dsimp only
      rw [Finset.sum_coe_sort (T P)
        (localMarkedMass ((Ideal.absNorm P.val.val : ℝ)^(-(1/2 : ℝ))))]
      exact prime_marked_mass P.val (hS P.val P.property).1 (T P)
    _ = 10206*∑ P ∈ primeValues S, (Ideal.absNorm P : ℝ)⁻¹ := by
      rw [← Finset.mul_sum]
      congr 1
      unfold primeValues
      rw [Finset.sum_image (by intro P hP Q hQ h; exact Subtype.val_injective h)]
      exact (Finset.sum_subtype (p := fun P => P ∈ S) S (by simp)
        (fun P : PrimeIdeal => (Ideal.absNorm P.val : ℝ)⁻¹)).symm
    _ ≤ 10206*(X^δ*rootMass (1+δ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply reciprocal_mass δ hδ X hX (primeValues S)
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
      exact hS Q hQ
    _ = _ := by ring

/-- One epsilon is budgeted for the whole fixed slot family, not once per slot. -/
theorem optional_assignments_subpower {α : Type*} [Fintype α] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ T : S → Finset (ℕ × ℕ),
      (∑ a : α → Choice S T, ∏ i : α, choiceWeight S T (a i)) ≤ C*X^ε := by
  let δ := ε/((Fintype.card α : ℝ)+1)
  have hd : 0 < (Fintype.card α : ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos hε hd
  let B := 10206*rootMass (1+δ)
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (rootMass_nonneg _)
  refine ⟨(B+1)^(Fintype.card α),by positivity,?_⟩
  intro X hX S hS T
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hpool : (∑ q : (Σ P : S, T P),
      localMarkedMass ((Ideal.absNorm q.1.val.val : ℝ)^(-(1/2 : ℝ))) q.2.val) ≤ B*X^δ := by
    convert marked_pool_mass δ hδ X hX0 S hS T using 1
    dsimp only [B]
    ring
  have hone : 1 ≤ X^δ := Real.one_le_rpow hX hδ.le
  have hoption : (∑ q : Choice S T, choiceWeight S T q) ≤ (B+1)*X^δ := by
    rw [Fintype.sum_option]
    change 1+(∑ q : (Σ P : S, T P),
      localMarkedMass ((Ideal.absNorm q.1.val.val : ℝ)^(-(1/2 : ℝ))) q.2.val) ≤ _
    nlinarith
  have hexp : δ*(Fintype.card α : ℝ) ≤ ε := by
    have he : δ*((Fintype.card α : ℝ)+1) = ε := div_mul_cancel₀ ε (ne_of_gt hd)
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hδ.le).trans_eq he
  calc
    _ = ∏ _i : α, ∑ q : Choice S T, choiceWeight S T q :=
      (Fintype.prod_sum (fun _i : α => choiceWeight S T)).symm
    _ ≤ ∏ _i : α, (B+1)*X^δ := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun q _ => choiceWeight_nonneg S T q)
      · intro i _
        exact hoption
    _ = (B+1)^(Fintype.card α)*X^(δ*(Fintype.card α : ℝ)) := by
      rw [Finset.prod_const,Finset.card_univ,mul_pow,
        ← Real.rpow_natCast (X^δ) (Fintype.card α),← Real.rpow_mul hX0.le]
    _ ≤ (B+1)^(Fintype.card α)*X^ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hexp) (by positivity)

/-- Central mass of the actual inverse ideal kernel and all frozen marked kernels.
The same constant controls every finite coefficient cutoff and every subset of
allocations. Identification with the original restricted energy is a separate step. -/
theorem inverse_allocations_subpower {α : Type*} [Fintype α] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ (T : S → Finset (ℕ × ℕ)) (D : Finset (Id × Id)),
      (∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) →
      ∀ A : Finset (D × (α → Choice S T)),
      (∑ a ∈ A, KernelInverseIdealMass.idealMass a.1.val*
        ∏ i : α, choiceWeight S T (a.2 i)) ≤ C*X^ε := by
  obtain ⟨C,hC,hbound⟩ := optional_assignments_subpower (α := α) ε hε
  refine ⟨Real.exp (400*rootMass (3/2))*C,mul_pos (Real.exp_pos _) hC,?_⟩
  intro X hX S hS T D hD hs A
  have hnon (a : D × (α → Choice S T)) :
      0 ≤ KernelInverseIdealMass.idealMass a.1.val*∏ i : α, choiceWeight S T (a.2 i) :=
    mul_nonneg (KernelInverseIdealMass.idealMass_nonneg _)
      (Finset.prod_nonneg (fun _ _ => choiceWeight_nonneg S T _))
  calc
    _ ≤ ∑ a : D × (α → Choice S T), KernelInverseIdealMass.idealMass a.1.val*
        ∏ i : α, choiceWeight S T (a.2 i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun a _ _ => hnon a)
    _ = (∑ d ∈ D, KernelInverseIdealMass.idealMass d)*
        (∑ b : α → Choice S T, ∏ i : α, choiceWeight S T (b i)) := by
      rw [Fintype.sum_prod_type,Finset.sum_mul]
      simp_rw [← Finset.mul_sum]
      exact Finset.sum_coe_sort D (fun d => KernelInverseIdealMass.idealMass d*
        (∑ b : α → Choice S T, ∏ i : α, choiceWeight S T (b i)))
    _ ≤ Real.exp (400*rootMass (3/2))*(C*X^ε) :=
      mul_le_mul (KernelInverseIdealMass.inverse_ideal_mass S (fun P hP => (hS P hP).1) D hD hs)
        (hbound X hX S hS T)
        (Finset.sum_nonneg (fun b _ => Finset.prod_nonneg (fun i _ => choiceWeight_nonneg S T _)))
        (Real.exp_pos _).le
    _ = _ := by ring

end
end Candidate.FourthPower.KernelInverseSlotMass
