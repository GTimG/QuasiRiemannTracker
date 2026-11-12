/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Sep
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.InjTuple

/-!
# Inverse.Restore.TupleSum — the twisted slot sum as an injective tuple sum

* `logPhase_sum`: `logPhase τ (∑ f) = ∏ logPhase τ f`.
* `sum_mark_prod`: `∑_{T ⊆ U, |T| = |I|} mark_I(T) · ∏_T g = ∑_{d ∈ injPi I L} (∏_i a_i(d_i)) ·
  [img d ⊆ U] ∏_{img d} g` (only the exact image survives).
* **`twSlots_eq_tuple`**: `twSlots c n U I L a Hp τ = logPhase τ (-log Hp) · ∑_{d ∈ injPi I L}
  [img d ⊆ U] ∏_i a_i(d_i) · c(d_i) · logPhase τ (log n(d_i))` — the per-prime slot weights of the
  restored child (the constant `logPhase τ (-log Hp)` is unimodular).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths.InverseMoment

variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

omit [DecidableEq σ] [DecidableEq ι] in
theorem logPhase_sum (τ : ℝ) {α : Type*} (s : Finset α) (f : α → ℝ) :
    FourierBridge.logPhase τ (∑ x ∈ s, f x) = ∏ x ∈ s, FourierBridge.logPhase τ (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [FourierBridge.logPhase]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx, FourierBridge.logPhase_add, ih]

/-- Only the exact image of an injective tuple carries its mark. -/
theorem sum_mark_prod (U : Finset ι) (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (g : ι → ℂ) :
    ∑ T ∈ U.powerset.filter (fun T => T.card = I.card), primeMarkInj I L a T * ∏ P ∈ T, g P =
      ∑ d ∈ injPi I L, (∏ i ∈ I.attach, a i.1 (d i.1 i.2)) *
        (if tupleImage I d ⊆ U then ∏ P ∈ tupleImage I d, g P else 0) := by
  simp_rw [markInj_tuple_indicator I L a, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hcard := tupleImage_card hd
  have hiff : ∀ T ∈ U.powerset.filter (fun T => T.card = I.card),
      (tupleImage I d ⊆ T ↔ tupleImage I d = T) := by
    intro T hT
    have hTc := (Finset.mem_filter.mp hT).2
    constructor
    · intro hsub
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hTc, hcard])
    · rintro rfl; exact le_rfl
  calc ∑ T ∈ U.powerset.filter (fun T => T.card = I.card),
        (∏ i ∈ I.attach, a i.1 (d i.1 i.2)) * (if tupleImage I d ⊆ T then 1 else 0) *
          ∏ P ∈ T, g P
      = ∑ T ∈ U.powerset.filter (fun T => T.card = I.card),
          (∏ i ∈ I.attach, a i.1 (d i.1 i.2)) *
            (if tupleImage I d = T then ∏ P ∈ T, g P else 0) := by
        apply Finset.sum_congr rfl
        intro T hT
        by_cases hs : tupleImage I d ⊆ T
        · rw [if_pos hs, if_pos ((hiff T hT).mp hs)]; ring
        · rw [if_neg hs, if_neg (fun h => hs ((hiff T hT).mpr h))]; ring
    _ = (∏ i ∈ I.attach, a i.1 (d i.1 i.2)) *
          (if tupleImage I d ⊆ U then ∏ P ∈ tupleImage I d, g P else 0) := by
        rw [← Finset.mul_sum, Finset.sum_ite_eq]
        congr 1
        have hmem : tupleImage I d ∈ U.powerset.filter (fun T => T.card = I.card) ↔
            tupleImage I d ⊆ U := by
          simp only [Finset.mem_filter, Finset.mem_powerset, hcard, and_true]
        by_cases h : tupleImage I d ⊆ U
        · rw [if_pos (hmem.mpr h), if_pos h]
        · rw [if_neg (fun h' => h (hmem.mp h')), if_neg h]

/-- The product over the image of an injective tuple is the product along the tuple. -/
theorem prod_tupleImage {I : Finset σ} {L : σ → Finset ι} {d : ∀ i ∈ I, ι} (hd : d ∈ injPi I L)
    (g : ι → ℂ) : ∏ P ∈ tupleImage I d, g P = ∏ i ∈ I.attach, g (d i.1 i.2) := by
  unfold tupleImage
  rw [Finset.prod_image]
  intro i _ j _ hij
  exact Subtype.ext ((mem_injPi.mp hd).2 i.1 i.2 j.1 j.2 hij)

/-- **The twisted slot sum as an injective tuple sum.** -/
theorem twSlots_eq_tuple (c : ι → ℂ) (n : ι → ℝ) (hn : ∀ i, 0 < n i) (U : Finset ι)
    (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ) (Hp τ : ℝ) (hHp : 0 < Hp) :
    twSlots c n U I L a Hp τ = FourierBridge.logPhase τ (-Real.log Hp) *
      ∑ d ∈ injPi I L, (if tupleImage I d ⊆ U then
        ∏ i ∈ I.attach, (a i.1 (d i.1 i.2) * (c (d i.1 i.2) *
          FourierBridge.logPhase τ (Real.log (n (d i.1 i.2))))) else 0) := by
  have hT : ∀ T : Finset ι, (∏ i ∈ T, c i) *
      FourierBridge.logPhase τ (Real.log ((∏ i ∈ T, n i) / Hp)) =
      FourierBridge.logPhase τ (-Real.log Hp) *
        ∏ P ∈ T, (c P * FourierBridge.logPhase τ (Real.log (n P))) := by
    intro T
    have hpos : 0 < ∏ i ∈ T, n i := Finset.prod_pos (fun i _ => hn i)
    rw [Real.log_div hpos.ne' hHp.ne', Real.log_prod (fun i _ => (hn i).ne'), sub_eq_neg_add,
      FourierBridge.logPhase_add, logPhase_sum, Finset.prod_mul_distrib]
    ring
  unfold twSlots
  simp_rw [hT]
  have h2 : ∀ T : Finset ι, primeMarkInj I L a T * (FourierBridge.logPhase τ (-Real.log Hp) *
      ∏ P ∈ T, (c P * FourierBridge.logPhase τ (Real.log (n P)))) =
      FourierBridge.logPhase τ (-Real.log Hp) * (primeMarkInj I L a T *
        ∏ P ∈ T, (c P * FourierBridge.logPhase τ (Real.log (n P)))) := fun T => by ring
  simp_rw [h2]
  rw [← Finset.mul_sum, sum_mark_prod]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs with h
  · rw [prod_tupleImage hd, ← Finset.prod_mul_distrib]
  · rw [mul_zero]

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.twSlots_eq_tuple
