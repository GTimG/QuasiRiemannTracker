/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Recur

/-!
# Inverse.Restore.Split — splitting an exact-image injective mark

If `T.card = I.card` (injective tuples onto `T`) and `B ⊆ T`, every tuple onto `T` splits into
the slots `F` sent onto `B` and the slots `I \ F` sent onto `T \ B`:

`primeMarkInj I L a T = ∑_{F ⊆ I, |F| = |B|} primeMarkInj F L a B · primeMarkInj (I \ F) L a (T \ B)`
(`primeMarkInj_split`). This regroups `mCol - gCol` (where `col_union` produces the doubled
primes `B ⊆ T` of the frozen `j ≥ 2` powers) by the set `F` of frozen slots.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators

variable {σ ι : Type*} [DecidableEq ι]

theorem erase_sdiff_erase_of_mem (T B : Finset ι) (p : ι) (hp : p ∈ B) :
    T.erase p \ B.erase p = T \ B := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_erase]
  by_cases hx : x = p
  · subst hx; simp [hp]
  · simp [hx]

/-- **Splitting an exact-image injective mark** along `B ⊆ T`. -/
theorem primeMarkInj_split (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ) :
    ∀ (T B : Finset ι), B ⊆ T → T.card = I.card →
      primeMarkInj I L a T =
        ∑ F ∈ I.powerset.filter (fun F => F.card = B.card),
          primeMarkInj F L a B * primeMarkInj (I \ F) L a (T \ B) := by
  induction I using Finset.induction_on with
  | empty =>
    intro T B hBT hT
    have hT0 : T = ∅ := Finset.card_eq_zero.mp (by simpa using hT)
    subst hT0
    have hB0 : B = ∅ := Finset.subset_empty.mp hBT
    subst hB0
    simp [Finset.filter_singleton, primeMarkInj_empty_slots]
  | @insert i0 I hi0 ih =>
    intro T B hBT hT
    rw [Finset.card_insert_of_notMem hi0] at hT
    rw [primeMarkInj_insert I i0 hi0, Finset.sum_filter, Finset.sum_filter,
      Finset.sum_powerset_insert hi0]
    have hsplitL : ∀ p ∈ L i0,
        (if p ∈ T then a i0 p * primeMarkInj I L a (T.erase p) else 0) =
          (if p ∈ T \ B then a i0 p * primeMarkInj I L a (T.erase p) else 0) +
          (if p ∈ B then a i0 p * primeMarkInj I L a (T.erase p) else 0) := by
      intro p _
      by_cases hpB : p ∈ B
      · have : p ∉ T \ B := fun h => (Finset.mem_sdiff.mp h).2 hpB
        rw [if_pos (hBT hpB), if_neg this, if_pos hpB, zero_add]
      · by_cases hpT : p ∈ T
        · rw [if_pos hpT, if_pos (Finset.mem_sdiff.mpr ⟨hpT, hpB⟩), if_neg hpB, add_zero]
        · rw [if_neg hpT, if_neg (fun h => hpT (Finset.mem_sdiff.mp h).1), if_neg hpB,
            add_zero]
    rw [Finset.sum_congr rfl hsplitL, Finset.sum_add_distrib]
    congr 1
    · -- slot `i0` sent outside `B`: `i0 ∉ F`
      have hR : ∀ F ∈ I.powerset,
          (if F.card = B.card then primeMarkInj F L a B *
            primeMarkInj (insert i0 I \ F) L a (T \ B) else 0) =
          ∑ p ∈ L i0, (if F.card = B.card then
            (if p ∈ T \ B then a i0 p * (primeMarkInj F L a B *
              primeMarkInj (I \ F) L a ((T \ B).erase p)) else 0) else 0) := by
        intro F hF
        have hi0F : i0 ∉ F := fun h => hi0 (Finset.mem_powerset.mp hF h)
        have hi0IF : i0 ∉ I \ F := fun h => hi0 (Finset.mem_sdiff.mp h).1
        rw [Finset.insert_sdiff_of_notMem _ hi0F, primeMarkInj_insert (I \ F) i0 hi0IF,
          Finset.sum_filter, Finset.mul_sum]
        split_ifs with hc
        · apply Finset.sum_congr rfl
          intro p _
          split_ifs <;> ring
        · simp
      rw [Finset.sum_congr rfl hR, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p ∈ T \ B
      · rw [if_pos hp]
        have hBTp : B ⊆ T.erase p := by
          intro x hx
          refine Finset.mem_erase.mpr ⟨?_, hBT hx⟩
          rintro rfl; exact (Finset.mem_sdiff.mp hp).2 hx
        have hcard : (T.erase p).card = I.card := by
          rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp hp).1, hT]; simp
        rw [ih (T.erase p) B hBTp hcard, Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro F _
        rw [Finset.erase_sdiff_comm]
        split_ifs <;> ring
      · simp only [hp, if_false, ite_self, Finset.sum_const_zero]
    · -- slot `i0` sent into `B`: `F = insert i0 F'`
      have hR : ∀ F ∈ I.powerset,
          (if (insert i0 F).card = B.card then primeMarkInj (insert i0 F) L a B *
            primeMarkInj (insert i0 I \ insert i0 F) L a (T \ B) else 0) =
          ∑ p ∈ L i0, (if p ∈ B then (if F.card = (B.erase p).card then
            a i0 p * (primeMarkInj F L a (B.erase p) *
              primeMarkInj (I \ F) L a (T \ B)) else 0) else 0) := by
        intro F hF
        have hi0F : i0 ∉ F := fun h => hi0 (Finset.mem_powerset.mp hF h)
        have hsd : insert i0 I \ insert i0 F = I \ F := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
          constructor
          · rintro ⟨h1 | h1, h2, h3⟩
            · exact absurd h1 h2
            · exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩
            exact ⟨Or.inr h1, fun h => hi0 (h ▸ h1), h3⟩
        rw [hsd, Finset.card_insert_of_notMem hi0F, primeMarkInj_insert F i0 hi0F,
          Finset.sum_filter, Finset.sum_mul]
        split_ifs with hc
        · apply Finset.sum_congr rfl
          intro p _
          by_cases hpB : p ∈ B
          · rw [if_pos hpB, if_pos hpB, if_pos]
            · ring
            · rw [Finset.card_erase_of_mem hpB, ← hc]; simp
          · rw [if_neg hpB, if_neg hpB, zero_mul]
        · symm
          apply Finset.sum_eq_zero
          intro p _
          by_cases hpB : p ∈ B
          · rw [if_pos hpB, if_neg]
            intro h
            apply hc
            rw [h, Finset.card_erase_of_mem hpB]
            have : 0 < B.card := Finset.card_pos.mpr ⟨p, hpB⟩
            omega
          · rw [if_neg hpB]
      rw [Finset.sum_congr rfl hR, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p ∈ B
      · rw [if_pos hp]
        have hcard : (T.erase p).card = I.card := by
          rw [Finset.card_erase_of_mem (hBT hp), hT]; simp
        rw [ih (T.erase p) (B.erase p) (Finset.erase_subset_erase p hBT) hcard, Finset.mul_sum,
          Finset.sum_filter, erase_sdiff_erase_of_mem T B p hp]
        apply Finset.sum_congr rfl
        intro F _
        rw [if_pos hp]
      · simp only [hp, if_false, Finset.sum_const_zero]

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.primeMarkInj_split
