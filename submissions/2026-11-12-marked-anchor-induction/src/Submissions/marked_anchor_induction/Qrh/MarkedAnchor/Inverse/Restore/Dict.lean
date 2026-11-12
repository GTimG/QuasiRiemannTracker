/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.TupleSum
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Collide

/-!
# Inverse.Restore.Dict — pool-index tuples as injective ideal tuples

The injective tuple sum of `TupleSum.twSlots_eq_tuple` runs over pool indices; the child source
bounds `Collide.injSlots` over ideals. Along an embedding `val : ι ↪ Ideal O` (pool index ↦ prime
ideal) with lists `L' j = (lists j).map val`:

**`injSlots_eq_tuple`**: if on every list prime the normalized child slot term is a constant `κ j`
times the pool-index weight `w j P`, then `injSlots u L' β' X = (∏ κ) · ∑_{d ∈ injPi I lists}
∏_i w_i(d_i)`. (Slots are indexed by the subtype of `I`.)
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

theorem injSlots_eq_tuple {σ ι : Type} [DecidableEq σ] [DecidableEq ι] (val : ι ↪ Ideal O)
    (I : Finset σ) (lists : σ → Finset ι) (w : σ → ι → ℂ) (u : O)
    (β' : {i // i ∈ I} → Ideal O → ℂ) (X : {i // i ∈ I} → ℝ) (κ : {i // i ∈ I} → ℂ)
    (hw : ∀ j : {i // i ∈ I}, ∀ P ∈ lists j.1,
      CanonicalRowCompletion.idealRowHom u (val P) *
        Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
          ((lists j.1).map val) (β' j) (X j) (val P) = κ j * w j.1 P) :
    injSlots u (fun j => (lists j.1).map val) β' X =
      (∏ j, κ j) * ∑ d ∈ injPi I lists, ∏ i ∈ I.attach, w i.1 (d i.1 i.2) := by
  unfold injSlots
  rw [← Finset.sum_filter, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun d _ => fun j : {i // i ∈ I} => val (d j.1 j.2))
  · intro d hd
    obtain ⟨hpi, hinj⟩ := mem_injPi.mp hd
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun j => Finset.mem_map_of_mem val (Finset.mem_pi.mp hpi j.1 j.2), ?_⟩
    intro j j' h
    exact Subtype.ext (hinj j.1 j.2 j'.1 j'.2 (val.injective h))
  · intro d₁ _ d₂ _ h
    funext i hi
    exact val.injective (congrFun h ⟨i, hi⟩)
  · intro x hx
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨hxL, hxi⟩ := hx
    have hch : ∀ j : {i // i ∈ I}, ∃ P ∈ lists j.1, val P = x j :=
      fun j => Finset.mem_map.mp (hxL j)
    let d : ∀ i ∈ I, ι := fun i hi => Classical.choose (hch ⟨i, hi⟩)
    have hd1 : ∀ i (hi : i ∈ I), d i hi ∈ lists i := fun i hi =>
      (Classical.choose_spec (hch ⟨i, hi⟩)).1
    have hd2 : ∀ i (hi : i ∈ I), val (d i hi) = x ⟨i, hi⟩ := fun i hi =>
      (Classical.choose_spec (hch ⟨i, hi⟩)).2
    refine ⟨d, ?_, ?_⟩
    · rw [mem_injPi]
      refine ⟨Finset.mem_pi.mpr hd1, ?_⟩
      intro i hi j hj h
      have := hxi (by rw [← hd2 i hi, ← hd2 j hj, h] : x ⟨i, hi⟩ = x ⟨j, hj⟩)
      exact congrArg Subtype.val this
    · funext j
      exact hd2 j.1 j.2
  · intro d hd
    obtain ⟨hpi, _⟩ := mem_injPi.mp hd
    rw [← Finset.univ_eq_attach, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    exact (hw j (d j.1 j.2) (Finset.mem_pi.mp hpi j.1 j.2)).symm

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.injSlots_eq_tuple
