/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.InjMark
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Column

/-!
# Inverse.Restore.Inj — the injective marked column and its slot recursion

The slot lists may overlap and the child carries the injective mark
`primeMarkInj` (`Inverse/InjMark`). Instead of the tuple expansion of `Restore/Expand` (which
needs disjoint lists), the column satisfies a pi-free recursion over
the slots: one required prime `p` of slot `i0` is split off and ERASED from the pool (the
remaining tuple must avoid it, which is exactly injectivity):

* `primeMarkInj_eq_restrict`: only tuples inside `A` contribute.
* `primeMarkInj_insert`: `primeMarkInj (insert i0 I) L a A = ∑_{p ∈ L i0, p ∈ A} a i0 p ·
  primeMarkInj I L a (A.erase p)` (no disjointness).
* `markedColInj` (`∑_{A ⊆ pool} (∏_A c) · primeMarkInj · Φ(∏_A n / X)`), `markedColInj_empty`
  (no slots: the plain column `Euler.col`), **`markedColInj_insert`**:
  `markedColInj pool (insert i0 I) X = ∑_{p ∈ L i0 ∩ pool} a i0 p · c p ·
  markedColInj (pool.erase p) I (X / n p)`.
* **`mobiusChildRowInj_eq_markedColInj`**: the positive injective child row is a marked column
  with the weights `Column.childWeight`, norms `Column.primeN`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.FirstCauchyArithmetic (supportMobius)
open OAI.ConcreteTraceCRT (eisEmbedding)
open Qrh.MarkedAnchor.Inverse.Poisson

local notation "O" => ActualEisensteinCubic.O

section Mark
variable {σ ι : Type*} [DecidableEq ι]

/-- Only tuples inside `A` contribute to the injective mark. -/
theorem primeMarkInj_eq_restrict (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) :
    primeMarkInj I L a A =
      ∑ d ∈ (I.pi (fun i => (L i).filter (· ∈ A))).filter
          (fun d => ∀ i (hi : i ∈ I) j (hj : j ∈ I), d i hi = d j hj → i = j),
        ∏ i ∈ I.attach, a i.1 (d i.1 i.2) := by
  unfold primeMarkInj
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_pi] at hd ⊢
    exact ⟨fun i hi => (hd.1 i hi).1, hd.2⟩
  · intro d hd
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_pi, not_and] at hd
    obtain ⟨⟨hdL, hdinj⟩, hnot⟩ := hd
    have : ∃ i, ∃ hi : i ∈ I, d i hi ∉ A := by
      by_contra hall
      push_neg at hall
      exact hnot (fun i hi => ⟨hdL i hi, hall i hi⟩) hdinj
    obtain ⟨i, hi, hiA⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_attach I ⟨i, hi⟩)
    simp [hiA]
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_pi] at hd
    apply Finset.prod_congr rfl
    intro i _
    rw [if_pos (hd.1 i.1 i.2).2]

/-- The attached product over `insert i0 I` of a consed tuple. -/
theorem prod_attach_cons {β : Type*} [CommMonoid β] (I : Finset σ) (i0 : σ) (hi0 : i0 ∉ I)
    (p : ι) (d : ∀ i ∈ I, ι) (g : σ → ι → β) :
    ∏ x ∈ (insert i0 I).attach, g x.1 (Finset.Pi.cons I i0 p d x.1 x.2) =
      g i0 p * ∏ x ∈ I.attach, g x.1 (d x.1 x.2) := by
  have key : ∀ (s : Finset σ) (e : ∀ i ∈ s, ι),
      ∏ x ∈ s.attach, g x.1 (e x.1 x.2) = ∏ x ∈ s, (if h : x ∈ s then g x (e x h) else 1) := by
    intro s e
    rw [← Finset.prod_attach s]
    apply Finset.prod_congr rfl
    intro x _
    rw [dif_pos x.2]
  rw [key, key, Finset.prod_insert hi0, dif_pos (Finset.mem_insert_self _ _),
    Finset.Pi.cons_same]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  have hne : i0 ≠ x := fun h => hi0 (h ▸ hx)
  rw [dif_pos (Finset.mem_insert_of_mem hx), dif_pos hx, Finset.Pi.cons_ne hne]

/-- Sum over the tuples of `insert i0 I`. -/
theorem sum_pi_insert' {β : Type*} [AddCommMonoid β] (I : Finset σ) (i0 : σ) (hi0 : i0 ∉ I)
    (L : σ → Finset ι) (f : (∀ i ∈ insert i0 I, ι) → β) :
    ∑ d ∈ (insert i0 I).pi L, f d = ∑ p ∈ L i0, ∑ d ∈ I.pi L, f (Finset.Pi.cons I i0 p d) := by
  rw [Finset.pi_insert hi0, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_image]
    intro x _ y _ h
    exact Finset.Pi.cons_injective hi0 h
  · intro p _ p' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro d hd hd'
    simp only [Finset.mem_image] at hd hd'
    obtain ⟨d1, _, rfl⟩ := hd
    obtain ⟨d2, _, h⟩ := hd'
    have := congrFun (congrFun h i0) (Finset.mem_insert_self i0 I)
    rw [Finset.Pi.cons_same, Finset.Pi.cons_same] at this
    exact hne this.symm

/-- Injectivity of a consed tuple. -/
theorem cons_inj_iff (I : Finset σ) (i0 : σ) (hi0 : i0 ∉ I) (p : ι) (d : ∀ i ∈ I, ι) :
    (∀ i (hi : i ∈ insert i0 I) j (hj : j ∈ insert i0 I),
        Finset.Pi.cons I i0 p d i hi = Finset.Pi.cons I i0 p d j hj → i = j) ↔
      ((∀ i (hi : i ∈ I) j (hj : j ∈ I), d i hi = d j hj → i = j) ∧
        ∀ i (hi : i ∈ I), d i hi ≠ p) := by
  have hne : ∀ i ∈ I, i0 ≠ i := fun i hi h => hi0 (h ▸ hi)
  constructor
  · intro h
    refine ⟨fun i hi j hj hij => ?_, fun i hi hip => ?_⟩
    · apply h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
      rw [Finset.Pi.cons_ne (hne i hi), Finset.Pi.cons_ne (hne j hj)]
      exact hij
    · have := h i0 (Finset.mem_insert_self i0 I) i (Finset.mem_insert_of_mem hi)
        (by rw [Finset.Pi.cons_same, Finset.Pi.cons_ne (hne i hi)]; exact hip.symm)
      exact hne i hi this
  · rintro ⟨hinj, hav⟩ i hi j hj hij
    by_cases hi' : i = i0
    · subst hi'
      by_cases hj' : j = i
      · exact hj'.symm
      · have hjI : j ∈ I := (Finset.mem_insert.mp hj).resolve_left hj'
        rw [Finset.Pi.cons_same, Finset.Pi.cons_ne (hne j hjI)] at hij
        exact absurd hij.symm (hav j hjI)
    · have hiI : i ∈ I := (Finset.mem_insert.mp hi).resolve_left hi'
      by_cases hj' : j = i0
      · subst hj'
        rw [Finset.Pi.cons_same, Finset.Pi.cons_ne (hne i hiI)] at hij
        exact absurd hij (hav i hiI)
      · have hjI : j ∈ I := (Finset.mem_insert.mp hj).resolve_left hj'
        rw [Finset.Pi.cons_ne (hne i hiI), Finset.Pi.cons_ne (hne j hjI)] at hij
        exact hinj i hiI j hjI hij

/-- **Slot recursion of the injective mark** (no disjointness). -/
theorem primeMarkInj_insert (I : Finset σ) (i0 : σ) (hi0 : i0 ∉ I) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMarkInj (insert i0 I) L a A =
      ∑ p ∈ (L i0).filter (· ∈ A), a i0 p * primeMarkInj I L a (A.erase p) := by
  rw [primeMarkInj_eq_restrict, Finset.sum_filter, sum_pi_insert' I i0 hi0]
  apply Finset.sum_congr rfl
  intro p hp
  have hpA : p ∈ A := (Finset.mem_filter.mp hp).2
  rw [primeMarkInj_eq_restrict, Finset.sum_filter, Finset.mul_sum]
  -- both sides over tuples avoiding `p`
  have hL : ∀ d ∈ I.pi (fun i => (L i).filter (· ∈ A)),
      (if (∀ i (hi : i ∈ insert i0 I) j (hj : j ∈ insert i0 I),
          Finset.Pi.cons I i0 p d i hi = Finset.Pi.cons I i0 p d j hj → i = j)
        then ∏ x ∈ (insert i0 I).attach, a x.1 (Finset.Pi.cons I i0 p d x.1 x.2) else 0) =
      if ((∀ i (hi : i ∈ I) j (hj : j ∈ I), d i hi = d j hj → i = j) ∧
          ∀ i (hi : i ∈ I), d i hi ≠ p)
        then a i0 p * ∏ x ∈ I.attach, a x.1 (d x.1 x.2) else 0 := by
    intro d _
    rw [prod_attach_cons I i0 hi0 p d a]
    exact if_congr (cons_inj_iff I i0 hi0 p d) rfl rfl
  rw [Finset.sum_congr rfl hL]
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro d hd
    simp only [Finset.mem_pi, Finset.mem_filter] at hd ⊢
    intro i hi
    exact ⟨(hd i hi).1, Finset.mem_of_mem_erase (hd i hi).2⟩
  · intro d hd
    simp only [Finset.mem_sdiff, Finset.mem_pi, Finset.mem_filter, not_forall] at hd
    obtain ⟨hdA, i, hi, hnot⟩ := hd
    have hdi : d i hi = p := by
      by_contra hne
      exact hnot ⟨(hdA i hi).1, Finset.mem_erase.mpr ⟨hne, (hdA i hi).2⟩⟩
    rw [if_neg]
    rintro ⟨_, hav⟩
    exact hav i hi hdi
  · intro d hd
    simp only [Finset.mem_pi, Finset.mem_filter] at hd
    have hav : ∀ i (hi : i ∈ I), d i hi ≠ p := fun i hi => Finset.ne_of_mem_erase (hd i hi).2
    by_cases hinj : ∀ i (hi : i ∈ I) j (hj : j ∈ I), d i hi = d j hj → i = j
    · rw [if_pos hinj, if_pos ⟨hinj, hav⟩]
    · rw [if_neg hinj, if_neg (fun h => hinj h.1), mul_zero]

theorem primeMarkInj_empty_slots (L : σ → Finset ι) (a : σ → ι → ℂ) (A : Finset ι) :
    primeMarkInj (∅ : Finset σ) L a A = 1 := by
  simp [primeMarkInj]

end Mark

section Col
variable {σ ι : Type*} [DecidableEq ι]

/-- The injective marked profiled column. -/
def markedColInj (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (pool : Finset ι) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (X : ℝ) : ℂ :=
  ∑ A ∈ pool.powerset, (∏ i ∈ A, c i) * primeMarkInj slots lists a A * Φ ((∏ i ∈ A, n i) / X)

theorem markedColInj_empty (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (pool : Finset ι)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (X : ℝ) :
    markedColInj c n Φ pool (∅ : Finset σ) lists a X = col c n Φ pool X := by
  unfold markedColInj col
  simp only [primeMarkInj_empty_slots, mul_one]

/-- **Slot recursion of the injective marked column**: the required prime is erased from the
pool. -/
theorem markedColInj_insert (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (pool : Finset ι)
    (I : Finset σ) (i0 : σ) (hi0 : i0 ∉ I) (lists : σ → Finset ι) (a : σ → ι → ℂ) (X : ℝ) :
    markedColInj c n Φ pool (insert i0 I) lists a X =
      ∑ p ∈ (lists i0).filter (· ∈ pool),
        a i0 p * c p * markedColInj c n Φ (pool.erase p) I lists a (X / n p) := by
  unfold markedColInj
  simp_rw [primeMarkInj_insert I i0 hi0, Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ pool
  · rw [if_pos hp]
    have hpool : pool = insert p (pool.erase p) := (Finset.insert_erase hp).symm
    rw [hpool, Finset.sum_powerset_insert (Finset.notMem_erase p pool)]
    have h0 : ∑ A ∈ (pool.erase p).powerset, (∏ i ∈ A, c i) *
        (if p ∈ A then a i0 p * primeMarkInj I lists a (A.erase p) else 0) *
        Φ ((∏ i ∈ A, n i) / X) = 0 := by
      apply Finset.sum_eq_zero
      intro A hA
      have : p ∉ A := fun h => Finset.notMem_erase p pool (Finset.mem_powerset.mp hA h)
      rw [if_neg this]; ring
    rw [h0, zero_add, ← hpool]
    apply Finset.sum_congr rfl
    intro A hA
    have hpA : p ∉ A := fun h => Finset.notMem_erase p pool (Finset.mem_powerset.mp hA h)
    rw [if_pos (Finset.mem_insert_self p A), Finset.erase_insert hpA,
      Finset.prod_insert hpA, Finset.prod_insert hpA]
    have hs : n p * (∏ i ∈ A, n i) / X = (∏ i ∈ A, n i) / (X / n p) := by
      rw [div_div_eq_mul_div]; ring
    rw [hs]; ring
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro A hA
    have : p ∉ A := fun h => hp (Finset.mem_powerset.mp hA h)
    rw [if_neg this]; ring

end Col

section Row
variable {ι : Type} [DecidableEq ι] (p : ι → O)

/-- The positive injective physical child row is an injective marked column. -/
theorem mobiusChildRowInj_eq_markedColInj [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (pool : Finset ι) (ψ : O →* ℂ) (m : O)
    {σ : Type} (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ)
    (Xc : ℝ) (y : O) :
    mobiusChildRowInj p hg pool ψ m slots lists a Φ Xc false y =
      markedColInj (childWeight p hg ψ m y) (primeN p) Φ pool slots lists a Xc := by
  unfold mobiusChildRowInj markedColInj
  apply Finset.sum_congr rfl
  intro A _
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [supportMobius_eq_pow p hp hinj, map_prod, rowCoprimeMask_eq_prod,
    finiteSquarefreeRow_eq_prod, sqrt_primeProductNorm, primeProductNorm_eq_prod]
  unfold childWeight
  rw [Finset.prod_neg]
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Complex.ofReal_prod,
    Complex.ofReal_inv]
  ring

end Row

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.markedColInj_insert
#print axioms Qrh.MarkedAnchor.Inverse.Restore.mobiusChildRowInj_eq_markedColInj
