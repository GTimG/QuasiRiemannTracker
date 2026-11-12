/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.InjMark

/-!
# Inverse.Inj.Mark — the laws of the injective prime mark

`primeMarkInj I L a A` (`Inverse/InjMark.lean`) is the marked-squarefree analogue of the baseline
`primeMark`. The baseline column calculus uses only the empty/priority/residual laws, which hold
for the injective mark as well:

* `primeMarkInj_empty`, `primeMarkInj_insert` (`i ∉ I`: expansion along the slot `i`, the chosen
  prime is erased from the column for the remaining slots);
* `primeMarkInj_congr` (depends on the lists only through `L i ∩ A`);
* `primeMarkInj_residual_lists`: `markInj I L (B \ A) = markInj I (L \ A) B`;
* `primeMarkInj_priority`: `markInj I (A ∪ B) = ∑_{J ⊆ I} markInj J A · markInj (I \ J) (B \ A)`;
* `primeMarkInj_norm_le`: `‖markInj I L a A‖ ≤ |A|^|I|` for coefficients of norm `≤ 1`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators
open Qrh.MarkedAnchor.Inverse

section Laws
variable {σ ι : Type*} [DecidableEq ι]

theorem primeMarkInj_empty (L : σ → Finset ι) (a : σ → ι → ℂ) (A : Finset ι) :
    primeMarkInj (∅ : Finset σ) L a A = 1 := by
  unfold primeMarkInj
  rw [Finset.pi_empty]
  simp

theorem primeMarkInj_insert (I : Finset σ) (i : σ) (hi : i ∉ I)
    (L : σ → Finset ι) (a : σ → ι → ℂ) (C : Finset ι) :
    primeMarkInj (insert i I) L a C =
      ∑ x ∈ L i, (if x ∈ C then a i x else 0) * primeMarkInj I L a (C.erase x) := by
  unfold primeMarkInj
  rw [Finset.sum_filter, Finset.pi_insert hi]
  have hdisj : ∀ x ∈ L i, ∀ y ∈ L i, x ≠ y →
      Disjoint ((I.pi L).image (Finset.Pi.cons I i x)) ((I.pi L).image (Finset.Pi.cons I i y)) := by
    intro x _ y _ hxy
    rw [Finset.disjoint_left]
    intro f hf hf'
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp hf'
    have h := congrFun (congrFun hq' i) (Finset.mem_insert_self i I)
    rw [Finset.Pi.cons_same, Finset.Pi.cons_same] at h
    exact hxy h.symm
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.sum_image (fun q _ q' _ h => Finset.Pi.cons_injective hi h), Finset.sum_filter,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  -- the product over `insert i I`
  have hprod : ∀ g : σ → ι → ℂ,
      (∏ k ∈ (insert i I).attach, g k.1 (Finset.Pi.cons I i x q k.1 k.2)) =
        g i x * ∏ k ∈ I.attach, g k.1 (q k.1 k.2) := by
    intro g
    rw [Finset.attach_insert, Finset.prod_insert, Finset.prod_image]
    · simp only [Finset.Pi.cons_same]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      congr 1
      exact Finset.Pi.cons_ne (by rintro rfl; exact hi k.2)
    · exact fun _ _ _ _ h => Subtype.ext (Subtype.mk.inj h)
    · simpa only [Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq, true_and,
        Subtype.exists, exists_prop, exists_eq_right] using hi
  have hcons_ne (k : σ) (hk : k ∈ I) :
      Finset.Pi.cons I i x q k (Finset.mem_insert_of_mem hk) = q k hk :=
    Finset.Pi.cons_ne (by rintro rfl; exact hi hk)
  -- injectivity of the extended tuple
  have hinj_iff :
      (∀ k (hk : k ∈ insert i I) l (hl : l ∈ insert i I),
        Finset.Pi.cons I i x q k hk = Finset.Pi.cons I i x q l hl → k = l) ↔
      ((∀ k (hk : k ∈ I) l (hl : l ∈ I), q k hk = q l hl → k = l) ∧ ∀ k (hk : k ∈ I), q k hk ≠ x) := by
    constructor
    · intro h
      refine ⟨fun k hk l hl hkl => ?_, fun k hk hkx => ?_⟩
      · apply h k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl)
        rw [hcons_ne k hk, hcons_ne l hl, hkl]
      · have := h k (Finset.mem_insert_of_mem hk) i (Finset.mem_insert_self i I)
          (by rw [hcons_ne k hk, Finset.Pi.cons_same, hkx])
        exact hi (this ▸ hk)
    · rintro ⟨h, hxq⟩ k hk l hl hkl
      rcases Finset.mem_insert.mp hk with rfl | hk'
      · rcases Finset.mem_insert.mp hl with rfl | hl'
        · rfl
        · rw [Finset.Pi.cons_same] at hkl
          have h2 : Finset.Pi.cons I k x q l hl = q l hl' := Finset.Pi.cons_ne (by rintro rfl; exact hi hl')
          exact absurd (hkl.trans h2).symm (hxq l hl')
      · rcases Finset.mem_insert.mp hl with rfl | hl'
        · have h2 : Finset.Pi.cons I l x q k hk = q k hk' := Finset.Pi.cons_ne (by rintro rfl; exact hi hk')
          rw [Finset.Pi.cons_same, h2] at hkl
          exact absurd hkl (hxq k hk')
        · have h1 : Finset.Pi.cons I i x q k hk = q k hk' := Finset.Pi.cons_ne (by rintro rfl; exact hi hk')
          have h2 : Finset.Pi.cons I i x q l hl = q l hl' := Finset.Pi.cons_ne (by rintro rfl; exact hi hl')
          exact h k hk' l hl' (h1.symm.trans (hkl.trans h2))
  rw [hprod (fun k y => if y ∈ C then a k y else 0)]
  by_cases hxC : x ∈ C
  swap
  · simp [hxC]
  rw [if_pos hxC]
  by_cases hq : (∀ k (hk : k ∈ I) l (hl : l ∈ I), q k hk = q l hl → k = l)
  · rw [if_pos hq]
    by_cases hx : ∀ k (hk : k ∈ I), q k hk ≠ x
    · rw [if_pos (hinj_iff.mpr ⟨hq, hx⟩)]
      congr 1
      refine Finset.prod_congr rfl (fun k _ => ?_)
      have hne := hx k.1 k.2
      by_cases hkC : q k.1 k.2 ∈ C
      · rw [if_pos hkC, if_pos (Finset.mem_erase.mpr ⟨hne, hkC⟩)]
      · rw [if_neg hkC, if_neg (fun h => hkC (Finset.mem_of_mem_erase h))]
    · rw [if_neg (fun h => hx (hinj_iff.mp h).2)]
      push_neg at hx
      obtain ⟨k, hk, hkx⟩ := hx
      symm
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finset.mem_attach I ⟨k, hk⟩)
      simp [hkx]
  · rw [if_neg (fun h => hq (hinj_iff.mp h).1), if_neg hq, mul_zero]

theorem primeMarkInj_congr' (I : Finset σ) (a : σ → ι → ℂ) :
    ∀ (L L' : σ → Finset ι) (C C' : Finset ι), (∀ i ∈ I, L i ∩ C = L' i ∩ C') →
      primeMarkInj I L a C = primeMarkInj I L' a C' := by
  induction I using Finset.induction_on with
  | empty => intro L L' C C' _; rw [primeMarkInj_empty, primeMarkInj_empty]
  | insert i I hi ih =>
    intro L L' C C' h
    rw [primeMarkInj_insert I i hi, primeMarkInj_insert I i hi]
    have hi' := h i (Finset.mem_insert_self i I)
    have hsum (M : Finset ι) (D : Finset ι) (f : ι → ℂ) :
        (∑ x ∈ M, (if x ∈ D then a i x else 0) * f x) = ∑ x ∈ M ∩ D, a i x * f x := by
      rw [← Finset.sum_filter_add_sum_filter_not M (· ∈ D)]
      rw [Finset.sum_eq_zero (s := M.filter (fun x => x ∉ D)) (fun x hx => by
        rw [if_neg (Finset.mem_filter.mp hx).2, zero_mul]), add_zero, Finset.filter_mem_eq_inter]
      exact Finset.sum_congr rfl (fun x hx => by rw [if_pos (Finset.mem_inter.mp hx).2])
    rw [hsum, hsum, hi']
    refine Finset.sum_congr rfl (fun x hx => ?_)
    congr 1
    apply ih
    intro j hj
    have := h j (Finset.mem_insert_of_mem hj)
    rw [Finset.inter_erase, Finset.inter_erase, this]

theorem primeMarkInj_congr (I : Finset σ) (L L' : σ → Finset ι) (a : σ → ι → ℂ) (C : Finset ι)
    (h : ∀ i ∈ I, L i ∩ C = L' i ∩ C) : primeMarkInj I L a C = primeMarkInj I L' a C :=
  primeMarkInj_congr' I a L L' C C h

theorem primeMarkInj_residual_lists (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMarkInj I L a (B \ A) = primeMarkInj I (fun i => L i \ A) a B := by
  apply primeMarkInj_congr'
  intro i _
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem primeMarkInj_priority (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ) :
    ∀ A B : Finset ι, primeMarkInj I L a (A ∪ B) =
      ∑ J ∈ I.powerset, primeMarkInj J L a A * primeMarkInj (I \ J) L a (B \ A) := by
  induction I using Finset.induction_on with
  | empty =>
    intro A B
    simp [primeMarkInj_empty]
  | insert i I hi ih =>
    intro A B
    rw [primeMarkInj_insert I i hi, Finset.sum_powerset_insert hi]
    have hsplit (x : ι) : (if x ∈ A ∪ B then a i x else 0) =
        (if x ∈ A then a i x else 0) + (if x ∈ B \ A then a i x else 0) := by
      by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> simp [hA, hB]
    have hterm (x : ι) (hx : x ∈ L i) :
        (if x ∈ A ∪ B then a i x else 0) * primeMarkInj I L a ((A ∪ B).erase x) =
          (∑ J ∈ I.powerset, ((if x ∈ A then a i x else 0) * primeMarkInj J L a (A.erase x)) *
              primeMarkInj (I \ J) L a (B \ A)) +
          ∑ J ∈ I.powerset, primeMarkInj J L a A *
            ((if x ∈ B \ A then a i x else 0) * primeMarkInj (I \ J) L a ((B \ A).erase x)) := by
      rw [Finset.erase_union_distrib, ih, hsplit, add_mul, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl (fun J _ => ?_)
        by_cases hA : x ∈ A
        · have he : (B.erase x \ A.erase x) = B \ A := by
            ext y
            simp only [Finset.mem_sdiff, Finset.mem_erase]
            constructor
            · rintro ⟨⟨_, hy⟩, hya⟩
              exact ⟨hy, fun h => hya ⟨fun e => (e ▸ hA |> fun _ => by subst e; exact absurd h (by
                simp_all)), h⟩⟩
            · rintro ⟨hy, hya⟩
              exact ⟨⟨fun e => hya (e ▸ hA), hy⟩, fun h => hya h.2⟩
          rw [he, if_pos hA]; ring
        · rw [if_neg hA]; ring
      · refine Finset.sum_congr rfl (fun J _ => ?_)
        by_cases hBA : x ∈ B \ A
        · have hA : x ∉ A := (Finset.mem_sdiff.mp hBA).2
          have heA : A.erase x = A := Finset.erase_eq_of_notMem hA
          have he : (B.erase x \ A.erase x) = (B \ A).erase x := by
            rw [heA]; ext y; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
          rw [he, heA]; ring
        · rw [if_neg hBA]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (s := L i)]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl (fun J hJ => ?_)
      have hiJ : i ∉ J := fun h => hi (Finset.mem_powerset.mp hJ h)
      have h1 : insert i I \ J = insert i (I \ J) := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        by_cases hy : y = i
        · subst hy; simp [hiJ]
        · simp [hy]
      rw [← Finset.mul_sum, ← primeMarkInj_insert (I \ J) i (fun h => hi (Finset.mem_sdiff.mp h).1), h1]
    · refine Finset.sum_congr rfl (fun J hJ => ?_)
      have hiJ : i ∉ J := fun h => hi (Finset.mem_powerset.mp hJ h)
      have h2 : insert i I \ insert i J = I \ J := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        by_cases hy : y = i
        · subst hy; simp [hi]
        · simp [hy]
      rw [← Finset.sum_mul, ← primeMarkInj_insert J i hiJ, h2]

theorem primeMarkInj_norm_le (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (ha : ∀ i ∈ I, ∀ x ∈ L i, ‖a i x‖ ≤ 1) :
    ∀ C : Finset ι, ‖primeMarkInj I L a C‖ ≤ (C.card : ℝ) ^ I.card := by
  induction I using Finset.induction_on with
  | empty => intro C; simp [primeMarkInj_empty]
  | insert i I hi ih =>
    intro C
    have ha' : ∀ j ∈ I, ∀ x ∈ L j, ‖a j x‖ ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [primeMarkInj_insert I i hi, Finset.card_insert_of_notMem hi, pow_succ]
    refine (norm_sum_le _ _).trans ?_
    have hx (x : ι) (hx : x ∈ L i) : ‖(if x ∈ C then a i x else 0) * primeMarkInj I L a (C.erase x)‖ ≤
        (if x ∈ C then 1 else 0) * (C.card : ℝ) ^ I.card := by
      rw [norm_mul]
      by_cases hxC : x ∈ C
      · rw [if_pos hxC, if_pos hxC, one_mul]
        refine (mul_le_mul_of_nonneg_right (ha i (Finset.mem_insert_self i I) x hx)
          (norm_nonneg _)).trans ?_
        rw [one_mul]
        refine (ih ha' (C.erase x)).trans ?_
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Finset.card_erase_le) _
      · simp [hxC]
    refine (Finset.sum_le_sum hx).trans ?_
    rw [← Finset.sum_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)

end Laws

/-! ## Wrappers for a given `DecidableEq σ` instance (the baseline column calculus) -/

section Inst
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem primeMarkInj_priority' (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A B : Finset ι) : primeMarkInj I L a (A ∪ B) =
      ∑ J ∈ I.powerset, primeMarkInj J L a A * primeMarkInj (I \ J) L a (B \ A) := by
  convert primeMarkInj_priority I L a A B using 4
  ext
  simp

end Inst

end
end Qrh.MarkedAnchor.Inverse.Inj
