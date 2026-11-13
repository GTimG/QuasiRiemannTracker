/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Collide
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseAssignedCount

/-!
# Inverse.Restore.SmallSlots — small slots below the child deletion gate (small/big split)

The child source has the deletion gate `N(mod δ') < Z^ell` on every slot; the restored child's
slots with `Z^ell` below a constant `c_q` fail it. A gap `(2^j c, 2^{j+1} c]` free of slot scales
(**`exists_gap`**, pigeonhole over `K+1` dyadic windows) separates the slots into small ones
(`Z^ell ≤ 2^j c`, primes of norm `≤ 2^{j+1} c`) and big ones (`Z^ell > 2^{j+1} c`, primes of norm
`> 2^{j+1} c`): their pools are disjoint, so the injective slot product factors
(**`injSlots_split`**), and the small factor is bounded pointwise by `∏ #L i`
(**`norm_injSlots_le`**).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-- A dyadic window `(2^j c, 2^{j+1} c]`, `j ≤ #I`, containing none of the values `v i`. -/
theorem exists_gap {σ : Type*} (I : Finset σ) (v : σ → ℝ) (c : ℝ) (hc : 0 < c) :
    ∃ j : ℕ, j ≤ I.card ∧ ∀ i ∈ I, ¬ (2^j * c < v i ∧ v i ≤ 2^(j+1) * c) := by
  by_contra hcon
  push_neg at hcon
  have h : ∀ j ∈ Finset.range (I.card + 1), ∃ i ∈ I, 2^j * c < v i ∧ v i ≤ 2^(j+1) * c :=
    fun j hj => hcon j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  obtain ⟨i0, hi0, -⟩ := h 0 (Finset.mem_range.mpr (Nat.succ_pos _))
  choose f hfI hfv using h
  let g : ℕ → σ := fun j => if hj : j ∈ Finset.range (I.card + 1) then f j hj else i0
  have hg : ∀ j (hj : j ∈ Finset.range (I.card + 1)), g j = f j hj := fun j hj => dif_pos hj
  have hmaps : ∀ j ∈ Finset.range (I.card + 1), g j ∈ I := fun j hj => by rw [hg j hj]; exact hfI j hj
  have hinj : Set.InjOn g (Finset.range (I.card + 1) : Set ℕ) := by
    intro j hj j' hj' hjj
    have hj1 := hfv j hj
    have hj2 := hfv j' hj'
    rw [← hg j hj, hjj, hg j' hj'] at hj1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (2:ℝ)^(j+1) * c ≤ 2^j' * c :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlt) hc.le
      linarith [hj1.2, hj2.1]
    · have : (2:ℝ)^(j'+1) * c ≤ 2^j * c :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlt) hc.le
      linarith [hj1.1, hj2.2]
  have hcard := Finset.card_le_card_of_injOn g hmaps hinj
  rw [Finset.card_range] at hcard
  omega

/-- The injective slot product over slots with pairwise disjoint small/big pools factors. -/
theorem injSlots_split (u : O) {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι → Prop)
    [DecidablePred s] (L : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (X : ι → ℝ)
    (hdis : ∀ i j, s i → ¬ s j → Disjoint (L i) (L j)) :
    injSlots u L β X =
      injSlots u (fun i : {i // s i} => L i.1) (fun i => β i.1) (fun i => X i.1) *
        injSlots u (fun i : {i // ¬ s i} => L i.1) (fun i => β i.1) (fun i => X i.1) := by
  set f : ι → Ideal O → ℂ := fun i P => CanonicalRowCompletion.idealRowHom u P *
    Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
      (L i) (β i) (X i) P with hf
  unfold injSlots
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  let e := Equiv.piEquivPiSubtypeProd s (fun _ : ι => Ideal O)
  refine Finset.sum_bij' (fun x _ => e x) (fun p _ => e.symm p) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Fintype.mem_piFinset] at hx
    rw [Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
    exact ⟨fun i => hx i.1, fun i => hx i.1⟩
  · intro p hp
    rw [Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset] at hp
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : s i
    · have := hp.1 ⟨i, hi⟩
      simpa [e, Equiv.piEquivPiSubtypeProd, hi] using this
    · have := hp.2 ⟨i, hi⟩
      simpa [e, Equiv.piEquivPiSubtypeProd, hi] using this
  · intro x _; exact e.symm_apply_apply x
  · intro p _; exact e.apply_symm_apply p
  · intro x hx
    rw [Fintype.mem_piFinset] at hx
    have he1 : (e x).1 = fun i : {i // s i} => x i.1 := rfl
    have he2 : (e x).2 = fun i : {i // ¬ s i} => x i.1 := rfl
    have hinj : Function.Injective x ↔ Function.Injective (e x).1 ∧ Function.Injective (e x).2 := by
      rw [he1, he2]
      constructor
      · intro h
        exact ⟨fun i j hij => Subtype.ext (h hij), fun i j hij => Subtype.ext (h hij)⟩
      · rintro ⟨h1, h2⟩ i j hij
        by_cases hi : s i <;> by_cases hj : s j
        · exact congrArg Subtype.val (h1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
        · have hxj := hx j
          rw [← hij] at hxj
          exact ((Finset.disjoint_left.mp (hdis i j hi hj) (hx i)) hxj).elim
        · have hxi := hx i
          rw [hij] at hxi
          exact ((Finset.disjoint_left.mp (hdis j i hj hi) (hx j)) hxi).elim
        · exact congrArg Subtype.val (h2 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
    have hprod : (∏ i, f i (x i)) =
        (∏ i : {i // s i}, f i.1 (x i.1)) * ∏ i : {i // ¬ s i}, f i.1 (x i.1) :=
      (Fintype.prod_subtype_mul_prod_subtype s (fun i => f i (x i))).symm
    by_cases h : Function.Injective x
    · obtain ⟨h1, h2⟩ := hinj.mp h
      rw [if_pos h, if_pos h1, if_pos h2, hprod, he1, he2]
    · rw [if_neg h]
      by_cases h1 : Function.Injective (e x).1
      · by_cases h2 : Function.Injective (e x).2
        · exact absurd (hinj.mpr ⟨h1, h2⟩) h
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]

/-- Pointwise bound of the injective slot product by the number of tuples. -/
theorem norm_injSlots_le (u : O) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (X : ι → ℝ) (hX : ∀ i, 1 ≤ X i)
    (hβ : ∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) :
    ‖injSlots u L β X‖ ≤ ∏ i, ((L i).card : ℝ) := by
  unfold injSlots
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ x ∈ Fintype.piFinset L, ‖(if Function.Injective x then
      ∏ i, CanonicalRowCompletion.idealRowHom u (x i) *
        Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
          (L i) (β i) (X i) (x i) else 0)‖ ≤ 1 := by
    intro x _
    split_ifs
    · rw [norm_prod]
      apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      intro i _
      rw [norm_mul]
      have h1 := CanonicalRowCompletion.idealRowHom_norm u (x i)
      have h2 := Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff_bound
        (L i) (β i) (X i) 1 (hX i) zero_le_one (hβ i) (x i)
      calc ‖CanonicalRowCompletion.idealRowHom u (x i)‖ *
            ‖Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
              (L i) (β i) (X i) (x i)‖ ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    · simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Fintype.card_piFinset]
  push_cast
  exact le_rfl

/-- `#L ≤ 128 B` for a list of nonzero ideals of norm `≤ B` (baseline `list_card_le`). -/
theorem card_le_of_norm_le (L : Finset (Ideal O)) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ P ∈ L, P ≠ 0 ∧ (P.absNorm : ℝ) ≤ B) : (L.card : ℝ) ≤ 128 * B :=
  SevenEighths.DetectorDictionaryInverseAssignedCount.list_card_le L hB h

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.exists_gap
#print axioms Qrh.MarkedAnchor.Inverse.Restore.injSlots_split
#print axioms Qrh.MarkedAnchor.Inverse.Restore.norm_injSlots_le
