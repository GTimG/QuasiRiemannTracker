/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Mark
import Submissions.hailey_collet_1252270103.Record12518109Gain.Upstream.Route.RepeatedSlots

/-!
# Inverse.Inj.Coloring — injective column marks from colored disjoint lists

The native branch of the injective oracle: HC's finite coloring identity
(`RepeatedPrimeSlots.sum_colored_products`) at the level of the column mark,

  `∑_{col : A → S} primeMark S (L ∩ col⁻¹) a U = |S|^(|A|-|S|) · primeMarkInj S L a U`,

(`coloring_mark`), where the colored lists `L i ∩ col⁻¹(i)` are pairwise disjoint
(`colored_disjoint`). Linear in the mark, it passes to the canonical rows
(`fixedChildRow_mark_sum`), and Cauchy-Schwarz over the colorings bounds the injective column
energy by `(|S|^|S|)^2` times a uniform bound on the energies of disjoint sub-lists
(`Inj.Oracle`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths.InverseMoment
open Qrh.MarkedAnchor.Inverse

section Color
variable {A σ : Type*} [Fintype A] [DecidableEq A]

/-- The lists colored by `col`: slot `i` keeps the primes of color `i`. -/
def coloredLists (S : Finset σ) (L : σ → Finset A) (col : A → S) : σ → Finset A :=
  fun i => (L i).filter (fun x => ((col x : S) : σ) = i)

theorem coloredLists_subset (S : Finset σ) (L : σ → Finset A) (col : A → S) (i : σ) :
    coloredLists S L col i ⊆ L i := Finset.filter_subset _ _

theorem colored_disjoint (S : Finset σ) (L : σ → Finset A) (col : A → S) :
    (S : Set σ).PairwiseDisjoint (coloredLists S L col) := by
  intro i _ j _ hij
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx hx'
  exact hij ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hx').2)

/-- The coefficient of HC's coloring identity. -/
def colorCoeff (S : Finset σ) (L : σ → Finset A) (a : σ → A → ℂ) (U : Finset A) :
    S → A → ℂ :=
  fun i x => if x ∈ L i.1 ∧ x ∈ U then a i.1 x else 0

theorem primeMark_colored (S : Finset σ) (L : σ → Finset A) (a : σ → A → ℂ) (U : Finset A)
    (col : A → S) :
    primeMark S (coloredLists S L col) a U =
      ∏ i : S, ∑ x : A, if col x = i then colorCoeff S L a U i x else 0 := by
  unfold primeMark
  rw [← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  unfold primeSlot coloredLists colorCoeff
  rw [Finset.sum_filter, ← Finset.sum_subset (Finset.subset_univ (L i.1))]
  · refine Finset.sum_congr rfl (fun x hx => ?_)
    by_cases hc : col x = i
    · rw [if_pos (congrArg Subtype.val hc), if_pos hc]
      by_cases hU : x ∈ U
      · rw [if_pos hU, if_pos ⟨hx, hU⟩]
      · rw [if_neg hU, if_neg (fun h => hU h.2)]
    · rw [if_neg (fun h => hc (Subtype.ext h)), if_neg hc]
  · intro x _ hx
    simp [colorCoeff, hx]

theorem primeMarkInj_eq_fun_sum (S : Finset σ) (L : σ → Finset A) (a : σ → A → ℂ)
    (U : Finset A) :
    primeMarkInj S L a U =
      ∑ x : S → A, if Function.Injective x then ∏ i, colorCoeff S L a U i (x i) else 0 := by
  unfold primeMarkInj
  rw [Finset.sum_filter]
  refine Finset.sum_bij_ne_zero (fun p _ _ => fun i : S => p i.1 i.2) ?_ ?_ ?_ ?_
  · intro _ _ _; exact Finset.mem_univ _
  · intro p hp _ p' hp' _ h
    funext j hj
    exact congrFun h ⟨j, hj⟩
  · intro x _ hx
    have hinj : Function.Injective x := by
      by_contra h; exact hx (if_neg h)
    rw [if_pos hinj] at hx
    have hmem (i : S) : x i ∈ L i.1 := by
      by_contra h
      apply hx
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [colorCoeff, h])
    refine ⟨fun j hj => x ⟨j, hj⟩, Finset.mem_pi.mpr (fun j hj => hmem ⟨j, hj⟩), ?_, rfl⟩
    have hp : ∀ i (hi : i ∈ S) j (hj : j ∈ S), x ⟨i, hi⟩ = x ⟨j, hj⟩ → i = j :=
      fun i hi j hj h => congrArg Subtype.val (hinj h)
    rw [if_pos hp]
    intro h0
    apply hx
    rw [← h0, ← Finset.univ_eq_attach]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    unfold colorCoeff
    by_cases hU : x i ∈ U
    · rw [if_pos hU, if_pos ⟨hmem i, hU⟩]
    · rw [if_neg hU, if_neg (fun h => hU h.2)]
  · intro p hp _
    have hiff : (∀ i (hi : i ∈ S) j (hj : j ∈ S), p i hi = p j hj → i = j) ↔
        Function.Injective (fun i : S => p i.1 i.2) :=
      ⟨fun h i j hij => Subtype.ext (h i.1 i.2 j.1 j.2 hij),
        fun h i hi j hj hij => congrArg Subtype.val (@h ⟨i, hi⟩ ⟨j, hj⟩ hij)⟩
    by_cases hinj : ∀ i (hi : i ∈ S) j (hj : j ∈ S), p i hi = p j hj → i = j
    · rw [if_pos hinj, if_pos (hiff.mp hinj), ← Finset.univ_eq_attach]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have hm : p i.1 i.2 ∈ L i.1 := Finset.mem_pi.mp hp i.1 i.2
      unfold colorCoeff
      by_cases hU : p i.1 i.2 ∈ U
      · rw [if_pos hU, if_pos ⟨hm, hU⟩]
      · rw [if_neg hU, if_neg (fun h => hU h.2)]
    · rw [if_neg hinj, if_neg (fun h => hinj (hiff.mpr h))]

/-- **Coloring identity for the column mark.** -/
theorem coloring_mark (S : Finset σ) (L : σ → Finset A) (a : σ → A → ℂ) (U : Finset A) :
    ∑ col : A → S, primeMark S (coloredLists S L col) a U =
      ((Fintype.card S ^ (Fintype.card A - Fintype.card S) : ℕ) : ℂ) * primeMarkInj S L a U := by
  simp_rw [primeMark_colored]
  have h := RepeatedPrimeSlots.sum_colored_products (A := A) (I := S) (colorCoeff S L a U)
  rw [primeMarkInj_eq_fun_sum]
  convert h

end Color

/-! ## Cauchy-Schwarz over a finite family -/

theorem norm_sum_sq_le_card {Color : Type*} [Fintype Color] (v : Color → ℂ) :
    ‖∑ c, v c‖^2 ≤ (Fintype.card Color : ℝ) * ∑ c, ‖v c‖^2 := by
  apply ((sq_le_sq₀ (norm_nonneg _)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr (norm_sum_le _ _)).trans
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun (_ : Color) => (1 : ℝ))
    (fun c => ‖v c‖)

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.coloring_mark
