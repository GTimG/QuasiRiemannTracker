/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Inj

/-!
# Inverse.Restore.Recur — exact-image tuple columns (pi-free, overlapping lists)

For a slot set `I` the injective tuples with image EXACTLY a set `T` (`T.card = I.card`) carry
the weight `primeMarkInj I L a T`. Two column objects, indexed by the admissible tuple primes
`U` and the column pool `S`:

* `gCol U S I X = ∑_{T ⊆ U, |T| = |I|} mark_I(T) · (∏_T c) · col (S \ T) (X / ∏_T n)` — the
  physical object: the required slot primes are AVOIDED by the column
  (`markedColInj_eq_gCol`: the injective marked column is `gCol S S`);
* `mCol U S I X = ∑_{T ⊆ U, |T| = |I|} mark_I(T) · (∏_T c) · col S (X / ∏_T n)` — the main
  term: the column is the full pool, independent of the tuple (this is what the child source
  bounds after profile separation).

Both satisfy the same pi-free slot recursion (`gCol_insert`, `mCol_insert`, from
`sum_card_insert`); `col_union` is the finite Euler identity
`col (S ∪ T) Y = ∑_{B ⊆ T} (∏_B c) · col S (Y / ∏_B n)` used for `mCol - gCol`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators

variable {σ ι : Type*} [DecidableEq ι]

/-- The exact-image recursion: split off the prime of slot `i0`. -/
theorem sum_card_insert (U : Finset ι) (I : Finset σ) (i0 : σ) (hi0 : i0 ∉ I)
    (L : σ → Finset ι) (a : σ → ι → ℂ) (h : Finset ι → ℂ) :
    ∑ T ∈ U.powerset.filter (fun T => T.card = (insert i0 I).card),
        primeMarkInj (insert i0 I) L a T * h T =
      ∑ p ∈ (L i0).filter (· ∈ U), a i0 p *
        ∑ T ∈ (U.erase p).powerset.filter (fun T => T.card = I.card),
          primeMarkInj I L a T * h (insert p T) := by
  rw [Finset.card_insert_of_notMem hi0]
  have e1 : ∀ T ∈ U.powerset.filter (fun T => T.card = I.card + 1),
      primeMarkInj (insert i0 I) L a T * h T =
        ∑ p ∈ L i0, (if p ∈ T then a i0 p * primeMarkInj I L a (T.erase p) * h T else 0) := by
    intro T _
    rw [primeMarkInj_insert I i0 hi0, Finset.sum_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp
  rw [Finset.sum_congr rfl e1, Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hpU : p ∈ U
  · rw [if_pos hpU, ← Finset.sum_filter, Finset.mul_sum]
    symm
    apply Finset.sum_nbij' (fun T' => insert p T') (fun T => T.erase p)
    · intro T' hT'
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT' ⊢
      have hpT' : p ∉ T' := fun h => Finset.notMem_erase p U (hT'.1 h)
      refine ⟨⟨Finset.insert_subset hpU (hT'.1.trans (Finset.erase_subset p U)), ?_⟩,
        Finset.mem_insert_self p T'⟩
      rw [Finset.card_insert_of_notMem hpT', hT'.2]
    · intro T hT
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT ⊢
      refine ⟨Finset.erase_subset_erase p hT.1.1, ?_⟩
      rw [Finset.card_erase_of_mem hT.2, hT.1.2]; simp
    · intro T' hT'
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT'
      exact Finset.erase_insert (fun h => Finset.notMem_erase p U (hT'.1 h))
    · intro T hT
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT
      exact Finset.insert_erase hT.2
    · intro T' hT'
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT'
      have hpT' : p ∉ T' := fun h => Finset.notMem_erase p U (hT'.1 h)
      rw [Finset.erase_insert hpT']
      ring
  · rw [if_neg hpU]
    apply Finset.sum_eq_zero
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    have : p ∉ T := fun h => hpU (hT.1 h)
    rw [if_neg this]

/-- The physical exact-image column: required primes avoided by the column. -/
def gCol (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (U S : Finset ι) (I : Finset σ)
    (L : σ → Finset ι) (a : σ → ι → ℂ) (X : ℝ) : ℂ :=
  ∑ T ∈ U.powerset.filter (fun T => T.card = I.card),
    primeMarkInj I L a T * ((∏ i ∈ T, c i) * col c n Φ (S \ T) (X / ∏ i ∈ T, n i))

/-- The main exact-image column: full column pool. -/
def mCol (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (U S : Finset ι) (I : Finset σ)
    (L : σ → Finset ι) (a : σ → ι → ℂ) (X : ℝ) : ℂ :=
  ∑ T ∈ U.powerset.filter (fun T => T.card = I.card),
    primeMarkInj I L a T * ((∏ i ∈ T, c i) * col c n Φ S (X / ∏ i ∈ T, n i))

theorem sum_card_empty {β : Type*} [AddCommMonoid β] (U : Finset ι) (f : Finset ι → β) :
    ∑ T ∈ U.powerset.filter (fun T => T.card = (∅ : Finset σ).card), f T = f ∅ := by
  rw [Finset.sum_eq_single_of_mem ∅ (by simp)]
  intro T hT hne
  simp only [Finset.card_empty, Finset.mem_filter, Finset.mem_powerset,
    Finset.card_eq_zero] at hT
  exact absurd hT.2 hne

theorem gCol_empty (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (U S : Finset ι) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (X : ℝ) : gCol c n Φ U S (∅ : Finset σ) L a X = col c n Φ S X := by
  unfold gCol
  rw [sum_card_empty]
  simp [primeMarkInj_empty_slots]

theorem mCol_empty (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (U S : Finset ι) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (X : ℝ) : mCol c n Φ U S (∅ : Finset σ) L a X = col c n Φ S X := by
  unfold mCol
  rw [sum_card_empty]
  simp [primeMarkInj_empty_slots]

theorem gCol_insert (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (U S : Finset ι) (I : Finset σ)
    (i0 : σ) (hi0 : i0 ∉ I) (L : σ → Finset ι) (a : σ → ι → ℂ) (X : ℝ) :
    gCol c n Φ U S (insert i0 I) L a X =
      ∑ p ∈ (L i0).filter (· ∈ U), a i0 p * c p *
        gCol c n Φ (U.erase p) (S.erase p) I L a (X / n p) := by
  unfold gCol
  rw [sum_card_insert U I i0 hi0 L a]
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Finset.mem_filter, Finset.mem_powerset] at hT
  have hpT : p ∉ T := fun h => Finset.notMem_erase p U (hT.1 h)
  rw [Finset.prod_insert hpT, Finset.prod_insert hpT, Finset.sdiff_insert,
    Finset.erase_sdiff_comm, div_div, mul_comm (n p)]
  ring

theorem mCol_insert (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (U S : Finset ι) (I : Finset σ)
    (i0 : σ) (hi0 : i0 ∉ I) (L : σ → Finset ι) (a : σ → ι → ℂ) (X : ℝ) :
    mCol c n Φ U S (insert i0 I) L a X =
      ∑ p ∈ (L i0).filter (· ∈ U), a i0 p * c p *
        mCol c n Φ (U.erase p) S I L a (X / n p) := by
  unfold mCol
  rw [sum_card_insert U I i0 hi0 L a]
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Finset.mem_filter, Finset.mem_powerset] at hT
  have hpT : p ∉ T := fun h => Finset.notMem_erase p U (hT.1 h)
  rw [Finset.prod_insert hpT, Finset.prod_insert hpT, div_div, mul_comm (n p)]
  ring

/-- The injective marked column is the exact-image column with avoided required primes. -/
theorem markedColInj_eq_gCol (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (I : Finset σ)
    (L : σ → Finset ι) (a : σ → ι → ℂ) :
    ∀ (S : Finset ι) (X : ℝ), markedColInj c n Φ S I L a X = gCol c n Φ S S I L a X := by
  induction I using Finset.induction_on with
  | empty =>
    intro S X
    rw [markedColInj_empty, gCol_empty]
  | @insert i0 I hi0 ih =>
    intro S X
    rw [markedColInj_insert c n Φ S I i0 hi0, gCol_insert c n Φ S S I i0 hi0]
    apply Finset.sum_congr rfl
    intro p _
    rw [ih]

/-- Finite Euler identity: adjoining a disjoint set `T` to the column pool. -/
theorem col_union (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (S T : Finset ι) (hST : Disjoint S T)
    (hn : ∀ q ∈ T, n q ≠ 0) (Y : ℝ) :
    col c n Φ (S ∪ T) Y = ∑ B ∈ T.powerset, (∏ i ∈ B, c i) * col c n Φ S (Y / ∏ i ∈ B, n i) := by
  induction T using Finset.induction_on generalizing Y with
  | empty => simp
  | @insert q T hqT ih =>
    have hST' : Disjoint S T := Finset.disjoint_of_subset_right (Finset.subset_insert q T) hST
    have hqS : q ∉ S := fun h => Finset.disjoint_left.mp hST h (Finset.mem_insert_self q T)
    have hn' : ∀ r ∈ T, n r ≠ 0 := fun r hr => hn r (Finset.mem_insert_of_mem hr)
    have hU : S ∪ insert q T = insert q (S ∪ T) := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    have hqU : q ∉ S ∪ T := by
      simp only [Finset.mem_union, not_or]; exact ⟨hqS, hqT⟩
    rw [hU, col_insert c n Φ (S ∪ T) q hqU (hn q (Finset.mem_insert_self q T)), ih hST' hn',
      ih hST' hn', Finset.sum_powerset_insert hqT, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro B hB
    have hqB : q ∉ B := fun h => hqT (Finset.mem_powerset.mp hB h)
    rw [Finset.prod_insert hqB, Finset.prod_insert hqB, div_div, mul_comm (n q)]
    ring

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.markedColInj_eq_gCol
#print axioms Qrh.MarkedAnchor.Inverse.Restore.mCol_insert
#print axioms Qrh.MarkedAnchor.Inverse.Restore.col_union
