/- Copyright (c) 2026 Sil. Apache-2.0.
Exact reverse collision completion. The injective marked polynomial equals
the full canonical product minus patterns with strictly fewer live labels.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelCollisionEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelCollisionInverse
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths.Record12518109GainDeletion KernelCollisionEnergy

variable {I A : Type*} [Fintype I] [Fintype A]

def patternPolynomial (r : Setoid I) (a : I → A → ℂ) : ℂ :=
  injectiveTuplePolynomial (fun q : Quotient r => fun p => ∏ i ∈ collisionBlock r q, a i p)

theorem pattern_fiber (r : Setoid I) (a : I → A → ℂ) :
    patternPolynomial r a = ∑ x : I → A, if Setoid.ker x=r then ∏ i, a i (x i) else 0 := by
  have h := (kernelTupleEquiv (A := A) r).sum_comp
    (fun x : {x : I → A // Setoid.ker x=r} => ∏ i, a i (x.val i))
  have hp : patternPolynomial r a =
      ∑ p : {p : Quotient r → A // Function.Injective p}, ∏ i, a i (p.val (Quotient.mk r i)) := by
    unfold patternPolynomial injectiveTuplePolynomial
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (F := inferInstance) (p := fun p : Quotient r → A => Function.Injective p)
      _ (by simp)]
    apply Finset.sum_congr rfl
    intro p _
    exact (product_over_collision_blocks r a p.val).symm
  rw [hp]
  calc
    _ = ∑ x : {x : I → A // Setoid.ker x=r}, ∏ i, a i (x.val i) := h
    _ = _ := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_subtype (F := inferInstance) (p := fun x : I → A => Setoid.ker x=r)
        _ (by simp)]

theorem pattern_bottom (a : I → A → ℂ) :
    patternPolynomial ⊥ a = injectiveTuplePolynomial a := by
  rw [pattern_fiber]
  simp only [Setoid.ker_eq_bot_iff,injectiveTuplePolynomial]

theorem complete_collisions (a : I → A → ℂ) :
    injectiveTuplePolynomial a = (∏ i, ∑ p, a i p) -
      ∑ r ∈ (Finset.univ : Finset (Setoid I)).erase ⊥, patternPolynomial r a := by
  apply eq_sub_iff_add_eq.mpr
  have h := Finset.sum_erase_add (Finset.univ : Finset (Setoid I))
    (fun r => patternPolynomial r a) (Finset.mem_univ (⊥ : Setoid I))
  rw [pattern_bottom] at h
  have he : (∑ r : Setoid I, patternPolynomial r a) = ∏ i, ∑ p, a i p :=
    (product_sum_collision_blocks a).symm
  rw [he] at h
  simpa only [add_comm] using h

omit [Fintype A] in
theorem fewer_quotient_labels (r : Setoid I) (hr : r ≠ ⊥) :
    Fintype.card (Quotient r) < Fintype.card I := by
  apply Fintype.card_lt_of_surjective_not_injective (Quotient.mk r) Quotient.mk_surjective
  intro h
  apply hr
  apply Setoid.ext
  intro i j
  change r i j ↔ i=j
  exact ⟨fun hij => h (Quotient.sound hij),fun hij => hij ▸ r.refl i⟩

omit [Fintype A] in
theorem fewer_singleton_labels (r : Setoid I) (hr : r ≠ ⊥) :
    Fintype.card {q // singletonBlock r q} < Fintype.card I :=
  (Fintype.card_subtype_le _).trans_lt (fewer_quotient_labels r hr)

/-- Actual frozen block coefficients, live labels and the exact induced holes. -/
theorem freeze_collision_blocks (r : Setoid I) (a : I → A → ℂ) :
    patternPolynomial r a =
      ∑ t : {q // ¬singletonBlock r q} → A, if Function.Injective t then
        (∏ q : {q // ¬singletonBlock r q}, ∏ i ∈ collisionBlock r q.val, a i (t q))*
          injectiveTuplePolynomial (fun q : {q // singletonBlock r q} => fun p =>
            if ∀ j : {q // ¬singletonBlock r q}, p ≠ t j then
              a (singletonRepresentative r q) p else 0)
      else 0 := by
  unfold patternPolynomial
  rw [injectiveTuplePolynomial_split (singletonBlock r)]
  apply Finset.sum_congr (by ext; simp)
  intro t _
  split_ifs
  · apply congrArg₂ (·*·)
    · apply Finset.prod_congr (by ext; simp)
      intro q _
      rfl
    · unfold injectiveTuplePolynomial
      apply Finset.sum_congr (by ext; simp)
      intro x _
      split_ifs
      · apply Finset.prod_congr (by ext; simp)
        intro q _
        dsimp only
        rw [singletonBlock_eq]
        simp
      · rfl
  · rfl

end
end Candidate.FourthPower.KernelCollisionInverse
