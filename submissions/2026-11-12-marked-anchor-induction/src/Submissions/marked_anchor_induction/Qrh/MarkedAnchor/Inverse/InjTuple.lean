/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.InjMark

/-!
# Inverse.InjTuple — laws of the injective mark, injective tuples, injective canonical rows

The selection (`Select/*`) and the second Poisson step (`Poisson/*`) run with the injective mark
`primeMarkInj` on possibly overlapping lists.

* `injPi R L` (defined in `InjMark`): the injective tuples of `R.pi L`; `primeMarkInj_eq_injPi`.
* `sum_pi_insert`, `sum_injPi_insert`: peeling one slot off a (injective) tuple sum.
* `markInj_insert` (recursion `M_{x∪I}(A) = ∑_{y ∈ L x} [y∈A] a_x(y) M_I(A \ {y})`),
  `markInj_empty`, `markInj_norm_le` (`‖M_I(A)‖ ≤ #A^#I`), `markInj_priority`
  (`M_I(A ∪ B) = ∑_{J ⊆ I} M_J(A) M_{I\J}(B \ A)`), `markInj_congr`.
* `tupleImage`, `markInj_tuple_split` (`M_S(U) = ∑_{d inj on R} ∏ a(d) [img d ⊆ U]
  M_{S\R}(U \ img d)`), `markInj_tuple_indicator`, `tupleImage_card`, `tupleImage_norm`.
* `canonRowInj`, `columnEnergyInj`: the baseline `finiteCanonicalMarkedRow` /
  `normalizedColumnEnergy` with the injective mark.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths OAI.SevenEighths.InverseMoment

local notation "O" => OAI.ActualEisensteinCubic.O

section Laws
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

-- `TupleInj`, `injPi`, `mem_injPi`, `injPi_subset` are defined in `InjMark` (they are used by
-- `ChildBoundInj`).

theorem primeMarkInj_eq_injPi (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) :
    primeMarkInj I L a A = ∑ p ∈ injPi I L, ∏ i ∈ I.attach,
      (if p i.1 i.2 ∈ A then a i.1 (p i.1 i.2) else 0) := by
  unfold primeMarkInj injPi TupleInj
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_pi]

/-- Peeling one slot off a tuple sum. -/
theorem sum_pi_insert {M : Type*} [AddCommMonoid M] {x : σ} {R : Finset σ} (hx : x ∉ R)
    (L : σ → Finset ι) (G : (∀ i ∈ insert x R, ι) → M) :
    ∑ p ∈ (insert x R).pi L, G p = ∑ y ∈ L x, ∑ q ∈ R.pi L, G (Finset.Pi.cons R x y q) := by
  have h₁ : ∀ y ∈ L x, ∀ z ∈ L x, y ≠ z →
      Disjoint ((R.pi L).image (Finset.Pi.cons R x y)) ((R.pi L).image (Finset.Pi.cons R x z)) := by
    intro y _ z _ h
    simp only [Finset.disjoint_iff_ne, Finset.mem_image]
    rintro _ ⟨p₂, _, eq₂⟩ _ ⟨p₃, _, eq₃⟩ eq
    have : Finset.Pi.cons R x y p₂ x (Finset.mem_insert_self _ _) =
        Finset.Pi.cons R x z p₃ x (Finset.mem_insert_self _ _) := by rw [eq₂, eq₃, eq]
    rw [Finset.Pi.cons_same, Finset.Pi.cons_same] at this
    exact h this
  rw [Finset.pi_insert hx, Finset.sum_biUnion h₁]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_image (fun p₁ _ p₂ _ eq => Finset.Pi.cons_injective hx eq)]

theorem cons_of_mem {x : σ} {R : Finset σ} (hx : x ∉ R) (y : ι) (q : ∀ i ∈ R, ι) (i : σ)
    (hi : i ∈ R) (h : i ∈ insert x R) : Finset.Pi.cons R x y q i h = q i hi :=
  Finset.Pi.cons_ne (by rintro rfl; exact hx hi)

theorem tupleInj_cons {x : σ} {R : Finset σ} (hx : x ∉ R) (y : ι) (q : ∀ i ∈ R, ι) :
    TupleInj (Finset.Pi.cons R x y q) ↔ TupleInj q ∧ ∀ i (hi : i ∈ R), q i hi ≠ y := by
  constructor
  · intro h
    refine ⟨fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j
      (Finset.mem_insert_of_mem hj)
        (by rw [cons_of_mem hx y q i hi, cons_of_mem hx y q j hj]; exact hij), fun i hi hiy => ?_⟩
    have := h i (Finset.mem_insert_of_mem hi) x (Finset.mem_insert_self _ _)
      (by rw [cons_of_mem hx y q i hi, Finset.Pi.cons_same]; exact hiy)
    exact hx (this ▸ hi)
  · rintro ⟨hq, hy⟩ i hi j hj hij
    rcases Finset.mem_insert.mp hi with hix | hi'
    · subst hix
      rcases Finset.mem_insert.mp hj with hjx | hj'
      · exact hjx.symm
      · rw [Finset.Pi.cons_same, cons_of_mem hx y q j hj'] at hij
        exact absurd hij.symm (hy j hj')
    · rcases Finset.mem_insert.mp hj with hjx | hj'
      · subst hjx
        rw [Finset.Pi.cons_same, cons_of_mem hx y q i hi'] at hij
        exact absurd hij (hy i hi')
      · rw [cons_of_mem hx y q i hi', cons_of_mem hx y q j hj'] at hij
        exact hq i hi' j hj' hij

/-- Peeling one slot off an injective tuple sum. -/
theorem sum_injPi_insert {M : Type*} [AddCommMonoid M] {x : σ} {R : Finset σ} (hx : x ∉ R)
    (L : σ → Finset ι) (G : (∀ i ∈ insert x R, ι) → M) :
    ∑ d ∈ injPi (insert x R) L, G d =
      ∑ y ∈ L x, ∑ q ∈ (injPi R L).filter (fun q => ∀ i (hi : i ∈ R), q i hi ≠ y),
        G (Finset.Pi.cons R x y q) := by
  unfold injPi
  rw [Finset.sum_filter, sum_pi_insert hx]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.filter_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : TupleInj (Finset.Pi.cons R x y q)
  · rw [if_pos h, if_pos ((tupleInj_cons hx y q).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((tupleInj_cons hx y q).mpr h'))]

theorem prod_attach_cons {M : Type*} [CommMonoid M] {x : σ} {R : Finset σ} (hx : x ∉ R)
    (y : ι) (q : ∀ i ∈ R, ι) (F : σ → ι → M) :
    ∏ i ∈ (insert x R).attach, F i.1 (Finset.Pi.cons R x y q i.1 i.2) =
      F x y * ∏ i ∈ R.attach, F i.1 (q i.1 i.2) := by
  rw [Finset.attach_insert, Finset.prod_insert, Finset.prod_image]
  · simp only [Finset.Pi.cons_same]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [cons_of_mem hx y q i.1 i.2]
  · exact fun _ _ _ _ => Subtype.ext ∘ Subtype.mk.inj
  · simpa only [Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq, true_and,
      Subtype.exists, exists_prop, exists_eq_right] using hx

theorem injPi_empty (L : σ → Finset ι) :
    injPi (∅ : Finset σ) L = {Finset.Pi.empty (fun _ => ι)} := by
  unfold injPi
  rw [Finset.pi_empty, Finset.filter_singleton, if_pos]
  intro i hi
  exact absurd hi (Finset.notMem_empty i)

@[simp] theorem markInj_empty (L : σ → Finset ι) (a : σ → ι → ℂ) (A : Finset ι) :
    primeMarkInj (∅ : Finset σ) L a A = 1 := by
  rw [primeMarkInj_eq_injPi, injPi_empty, Finset.sum_singleton, Finset.attach_empty,
    Finset.prod_empty]

/-- The recursion of the injective mark. -/
theorem markInj_insert {x : σ} {I : Finset σ} (hx : x ∉ I) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMarkInj (insert x I) L a A =
      ∑ y ∈ L x, (if y ∈ A then a x y else 0) * primeMarkInj I L a (A.erase y) := by
  rw [primeMarkInj_eq_injPi, sum_injPi_insert hx]
  apply Finset.sum_congr rfl
  intro y _
  rw [primeMarkInj_eq_injPi, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  rw [prod_attach_cons hx y q (fun i z => if z ∈ A then a i z else 0)]
  by_cases hav : ∀ i (hi : i ∈ I), q i hi ≠ y
  · rw [if_pos hav]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    have hne : q i.1 i.2 ≠ y := hav i.1 i.2
    simp only [Finset.mem_erase, hne, ne_eq, not_false_eq_true, true_and]
  · rw [if_neg hav]
    obtain ⟨i, hi, hiy⟩ : ∃ i, ∃ hi : i ∈ I, q i hi = y := by
      by_contra h
      exact hav (fun i hi e => h ⟨i, hi, e⟩)
    have hz : (∏ j ∈ I.attach, if q j.1 j.2 ∈ A.erase y then a j.1 (q j.1 j.2) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_attach _ ⟨i, hi⟩) (by simp [hiy])
    rw [hz, mul_zero]

theorem markInj_norm_le (L : σ → Finset ι) (a : σ → ι → ℂ) :
    ∀ I : Finset σ, (∀ i ∈ I, ∀ P ∈ L i, ‖a i P‖ ≤ 1) → ∀ A : Finset ι,
      ‖primeMarkInj I L a A‖ ≤ (A.card : ℝ)^I.card := by
  intro I
  induction I using Finset.induction with
  | empty => intro _ A; simp
  | insert x I hx ih =>
    intro ha A
    have hI : ∀ i ∈ I, ∀ P ∈ L i, ‖a i P‖ ≤ 1 :=
      fun i hi => ha i (Finset.mem_insert_of_mem hi)
    rw [markInj_insert hx, Finset.card_insert_of_notMem hx, pow_succ]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y ∈ L x, ‖(if y ∈ A then a x y else 0) * primeMarkInj I L a (A.erase y)‖
        ≤ ∑ y ∈ L x, (if y ∈ A then (A.card : ℝ)^I.card else 0) := by
          apply Finset.sum_le_sum
          intro y hy
          split_ifs with hyA
          · rw [norm_mul]
            have h1 := ha x (Finset.mem_insert_self _ _) y hy
            have h3 : ((A.erase y).card : ℝ)^I.card ≤ (A.card : ℝ)^I.card :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Finset.card_erase_le) _
            calc ‖a x y‖ * ‖primeMarkInj I L a (A.erase y)‖ ≤ 1 * (A.card : ℝ)^I.card :=
                  mul_le_mul h1 ((ih hI (A.erase y)).trans h3) (norm_nonneg _) zero_le_one
              _ = _ := one_mul _
          · simp
      _ = ((L x).filter (· ∈ A)).card * (A.card : ℝ)^I.card := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A.card : ℝ)^I.card * A.card := by
          rw [mul_comm]
          gcongr
          exact fun y hy => (Finset.mem_filter.mp hy).2

/-- The priority law of the injective mark. -/
theorem markInj_priority (L : σ → Finset ι) (a : σ → ι → ℂ) :
    ∀ (I : Finset σ) (A B : Finset ι), primeMarkInj I L a (A ∪ B) =
      ∑ J ∈ I.powerset, primeMarkInj J L a A * primeMarkInj (I \ J) L a (B \ A) := by
  intro I
  induction I using Finset.induction with
  | empty => intro A B; simp
  | insert x I hx ih =>
    intro A B
    rw [markInj_insert hx, Finset.sum_powerset_insert hx]
    have hsplit : ∀ y, (if y ∈ A ∪ B then a x y else 0) =
        (if y ∈ A then a x y else 0) + (if y ∈ B \ A then a x y else 0) := by
      intro y
      by_cases hA : y ∈ A <;> by_cases hB : y ∈ B <;> simp [hA, hB]
    simp only [hsplit, add_mul, Finset.sum_add_distrib]
    -- the part `y ∈ A`
    have hApart : ∑ y ∈ L x, (if y ∈ A then a x y else 0) * primeMarkInj I L a ((A ∪ B).erase y) =
        ∑ J ∈ I.powerset, primeMarkInj (insert x J) L a A *
          primeMarkInj (insert x I \ insert x J) L a (B \ A) := by
      have h1 : ∀ y ∈ L x, (if y ∈ A then a x y else 0) * primeMarkInj I L a ((A ∪ B).erase y) =
          ∑ J ∈ I.powerset, ((if y ∈ A then a x y else 0) * primeMarkInj J L a (A.erase y)) *
            primeMarkInj (I \ J) L a (B \ A) := by
        intro y _
        by_cases hyA : y ∈ A
        · have hAB : (A ∪ B).erase y = A.erase y ∪ B.erase y := Finset.erase_union_distrib _ _ _
          have hBA : B.erase y \ A.erase y = B \ A := by
            ext z
            by_cases hz : z = y
            · subst hz; simp [hyA]
            · simp [Finset.mem_sdiff, Finset.mem_erase, hz]
          rw [hAB, ih, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro J _
          rw [hBA]
          ring
        · simp [hyA]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      have hxJ : x ∉ J := fun h => hx (Finset.mem_powerset.mp hJ h)
      rw [← Finset.sum_mul, ← markInj_insert hxJ, Finset.insert_sdiff_insert,
        Finset.sdiff_insert_of_notMem hx]
    -- the part `y ∈ B \ A`
    have hBpart : ∑ y ∈ L x, (if y ∈ B \ A then a x y else 0) *
          primeMarkInj I L a ((A ∪ B).erase y) =
        ∑ J ∈ I.powerset, primeMarkInj J L a A * primeMarkInj (insert x I \ J) L a (B \ A) := by
      have h1 : ∀ y ∈ L x, (if y ∈ B \ A then a x y else 0) *
            primeMarkInj I L a ((A ∪ B).erase y) =
          ∑ J ∈ I.powerset, primeMarkInj J L a A *
            ((if y ∈ B \ A then a x y else 0) * primeMarkInj (I \ J) L a ((B \ A).erase y)) := by
        intro y _
        by_cases hyBA : y ∈ B \ A
        · have hyA : y ∉ A := (Finset.mem_sdiff.mp hyBA).2
          have hAB : (A ∪ B).erase y = A ∪ B.erase y := by
            rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hyA]
          have hBA : B.erase y \ A = (B \ A).erase y := by
            ext z; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
          rw [hAB, ih, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro J _
          rw [hBA]
          ring
        · simp [hyBA]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      have hxJ : x ∉ I \ J := fun h => hx (Finset.mem_sdiff.mp h).1
      have hxJ' : x ∉ J := fun h => hx (Finset.mem_powerset.mp hJ h)
      rw [← Finset.mul_sum, ← markInj_insert hxJ, Finset.insert_sdiff_of_notMem _ hxJ']
    rw [hApart, hBpart, add_comm]

theorem markInj_congr (S : Finset σ) (L : σ → Finset ι) (a a' : σ → ι → ℂ)
    (h : ∀ i ∈ S, ∀ P ∈ L i, a' i P = a i P) : primeMarkInj S L a' = primeMarkInj S L a := by
  funext U
  rw [primeMarkInj_eq_injPi, primeMarkInj_eq_injPi]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.prod_congr rfl
  intro i _
  rw [h i.1 i.2 _ (Finset.mem_pi.mp (mem_injPi.mp hd).1 i.1 i.2)]

/-! ## Tuple images -/

/-- The image of a slot tuple. -/
def tupleImage (R : Finset σ) (d : ∀ i ∈ R, ι) : Finset ι :=
  R.attach.image (fun i => d i.1 i.2)

theorem mem_tupleImage {R : Finset σ} {d : ∀ i ∈ R, ι} {z : ι} :
    z ∈ tupleImage R d ↔ ∃ i, ∃ hi : i ∈ R, d i hi = z := by
  unfold tupleImage
  simp only [Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨⟨i, hi⟩, h⟩; exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨⟨i, hi⟩, h⟩

theorem notMem_tupleImage {R : Finset σ} {d : ∀ i ∈ R, ι} {z : ι} :
    z ∉ tupleImage R d ↔ ∀ i (hi : i ∈ R), d i hi ≠ z := by
  rw [mem_tupleImage]
  push_neg
  rfl

theorem tupleImage_cons {x : σ} {R : Finset σ} (hx : x ∉ R) (y : ι) (q : ∀ i ∈ R, ι) :
    tupleImage (insert x R) (Finset.Pi.cons R x y q) = insert y (tupleImage R q) := by
  ext z
  rw [mem_tupleImage, Finset.mem_insert, mem_tupleImage]
  constructor
  · rintro ⟨i, hi, h⟩
    rcases Finset.mem_insert.mp hi with hix | hi'
    · subst hix
      left
      rw [Finset.Pi.cons_same] at h
      exact h.symm
    · right
      exact ⟨i, hi', by rw [← h, cons_of_mem hx y q i hi']⟩
  · rintro (rfl | ⟨i, hi, h⟩)
    · exact ⟨x, Finset.mem_insert_self _ _, Finset.Pi.cons_same _ _ _ _ _⟩
    · exact ⟨i, Finset.mem_insert_of_mem hi, by rw [cons_of_mem hx y q i hi]; exact h⟩

theorem tupleImage_empty (d : ∀ i ∈ (∅ : Finset σ), ι) : tupleImage ∅ d = (∅ : Finset ι) := by
  unfold tupleImage
  rw [Finset.attach_empty, Finset.image_empty]

/-- An injective tuple has `#R` distinct values. -/
theorem tupleImage_card {R : Finset σ} {L : σ → Finset ι} {d : ∀ i ∈ R, ι} (hd : d ∈ injPi R L) :
    (tupleImage R d).card = R.card := by
  unfold tupleImage
  rw [Finset.card_image_of_injective, Finset.card_attach]
  intro i j hij
  exact Subtype.ext ((mem_injPi.mp hd).2 i.1 i.2 j.1 j.2 hij)

theorem tupleImage_subset {R : Finset σ} {L : σ → Finset ι} {d : ∀ i ∈ R, ι} (hd : d ∈ R.pi L)
    (E : Finset ι) (hE : ∀ i ∈ R, L i ⊆ E) : tupleImage R d ⊆ E := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := mem_tupleImage.mp hz
  exact hE i hi (Finset.mem_pi.mp hd i hi)

/-- **Tuple split.** Selecting the slots `R ⊆ S` of an injective mark: one prime per selected
slot (an injective tuple `d`), the residual slots `S \ R` injective on `U \ img d`. -/
theorem markInj_tuple_split (S : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ) (U : Finset ι) :
    ∀ R : Finset σ, R ⊆ S → primeMarkInj S L a U = ∑ d ∈ injPi R L,
      (∏ i ∈ R.attach, a i.1 (d i.1 i.2)) *
        ((if tupleImage R d ⊆ U then 1 else 0) *
          primeMarkInj (S \ R) L a (U \ tupleImage R d)) := by
  intro R
  induction R using Finset.induction with
  | empty =>
    intro _
    rw [injPi_empty, Finset.sum_singleton, tupleImage_empty, Finset.attach_empty,
      Finset.prod_empty, Finset.sdiff_empty, Finset.sdiff_empty, if_pos (Finset.empty_subset _)]
    ring
  | insert x R hx ih =>
    intro hR
    have hxS : x ∈ S := hR (Finset.mem_insert_self _ _)
    have hRS : R ⊆ S := (Finset.subset_insert _ _).trans hR
    have hSR : S \ R = insert x (S \ insert x R) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨hz, hzR⟩
        by_cases hzx : z = x
        · exact Or.inl hzx
        · exact Or.inr ⟨hz, fun h => h.elim hzx hzR⟩
      · rintro (rfl | ⟨hz, h⟩)
        · exact ⟨hxS, hx⟩
        · exact ⟨hz, fun h' => h (Or.inr h')⟩
    have hxn : x ∉ S \ insert x R := by simp
    rw [ih hRS, sum_injPi_insert hx]
    simp only [hSR, markInj_insert hxn, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    rw [prod_attach_cons hx y q a, tupleImage_cons hx y q]
    by_cases hav : ∀ i (hi : i ∈ R), q i hi ≠ y
    · rw [if_pos hav]
      have hyq : y ∉ tupleImage R q := notMem_tupleImage.mpr hav
      have hU : (U \ tupleImage R q).erase y = U \ insert y (tupleImage R q) := by
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
        tauto
      rw [hU]
      by_cases hyU : y ∈ U
      · by_cases hsub : tupleImage R q ⊆ U
        · have hins : insert y (tupleImage R q) ⊆ U := Finset.insert_subset hyU hsub
          rw [if_pos hsub, if_pos (Finset.mem_sdiff.mpr ⟨hyU, hyq⟩), if_pos hins]
          ring
        · have hins : ¬ insert y (tupleImage R q) ⊆ U :=
            fun h => hsub ((Finset.subset_insert _ _).trans h)
          rw [if_neg hsub, if_neg hins]
          ring
      · have hy' : y ∉ U \ tupleImage R q := fun h => hyU (Finset.mem_sdiff.mp h).1
        have hins : ¬ insert y (tupleImage R q) ⊆ U :=
          fun h => hyU (h (Finset.mem_insert_self _ _))
        rw [if_neg hy', if_neg hins]
        ring
    · rw [if_neg hav]
      have hyq : y ∈ tupleImage R q := by
        by_contra h
        exact hav (notMem_tupleImage.mp h)
      have hy' : y ∉ U \ tupleImage R q := fun h => (Finset.mem_sdiff.mp h).2 hyq
      rw [if_neg hy']
      ring

theorem markInj_tuple_indicator (R : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (U : Finset ι) :
    primeMarkInj R L a U = ∑ d ∈ injPi R L,
      (∏ i ∈ R.attach, a i.1 (d i.1 i.2)) * (if tupleImage R d ⊆ U then 1 else 0) := by
  rw [markInj_tuple_split R L a U R le_rfl]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sdiff_self, markInj_empty, mul_one]

/-- On pairwise disjoint lists the injective mark is the full mark (local-instance form). -/
theorem markInj_eq_primeMark (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (hdis : (I : Set σ).PairwiseDisjoint L) : primeMarkInj I L a = primeMark I L a := by
  funext A
  rw [primeMarkInj_eq_injPi, primeMark_eq_tuple_sum, injPi, Finset.filter_true_of_mem]
  intro d hd i hi j hj hij
  by_contra hne
  have hpi := Finset.mem_pi.mp hd i hi
  have hpj := Finset.mem_pi.mp hd j hj
  rw [hij] at hpi
  exact Finset.disjoint_left.mp (hdis (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hne) hpi hpj

end Laws

/-! ## Canonical rows and energies with the injective mark -/

section Rows
variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

/-- Baseline `finiteCanonicalMarkedRow` with the injective mark. -/
def canonRowInj (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  SecondPassArithmetic.fixedChildRow p hp hcop hg pool Ψ m
    (fun U => primeMarkInj slots lists a U * W (FirstPassCubeLabels.primeProductNorm p U / X)) f k

/-- Baseline `normalizedColumnEnergy` with the injective mark. -/
def columnEnergyInj (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (labels : Finset (Ideal O)) (rows : Finset O)
    (D : Ideal O → ℝ) (W : ℝ → ℂ) (X Z F : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖((Z^(-F/2) : ℝ) : ℂ) *
      canonRowInj p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f) k slots lists a W X‖^2

/-- On pairwise disjoint lists the injective energy is the baseline energy. -/
theorem columnEnergyInj_eq [DecidableEq σ] (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (hdis : (slots : Set σ).PairwiseDisjoint lists) (labels : Finset (Ideal O)) (rows : Finset O)
    (D : Ideal O → ℝ) (W : ℝ → ℂ) (X Z F : ℝ) :
    columnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F =
      InverseInitialClippedColumns.normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a
        labels rows D W X Z F := by
  unfold columnEnergyInj canonRowInj InverseInitialClippedColumns.normalizedColumnEnergy
    finiteCanonicalMarkedRow
  rw [markInj_eq_primeMark slots lists a hdis]

end Rows

end
end Qrh.MarkedAnchor.Inverse
