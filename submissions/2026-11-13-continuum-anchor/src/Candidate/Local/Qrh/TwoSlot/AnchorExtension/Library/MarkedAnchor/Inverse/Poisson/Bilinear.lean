/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.SideRow
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Projector

/-!
# Inverse.Poisson.Bilinear — cross phase and residual projector on the physical pair

`∑_{A,B ⊆ R, A∩B=∅} QCP(A,B) χ_A(-1) conj α(A) β(B)
   = ∑_{χ,η} crossCoeff χ η ∑_{t ⊆ R} (-1)^|t| conj(∑_{a'} conj ray_χ(t∪a') χ_{t∪a'}(-1) α(t∪a'))
                                            · (∑_{b'} ray_η(t∪b') β(t∪b'))`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic
open MixedCrossSeparation (quadraticCrossPhase)
open OAI.RayFourExpansion (RayCharacter rayCharacter crossCoeff)

local notation "O" => ActualEisensteinCubic.O

theorem star_row_neg_one {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) :
    star (finiteSquarefreeRow P hgood S (-1)) = finiteSquarefreeRow P hgood S (-1) := by
  have h2 : finiteSquarefreeRow P hgood S (-1) ^ 2 = 1 := by
    rw [← row_pow, show ((-1 : O) ^ 2) = 1 by ring]
    simp only [finiteSquarefreeRow, map_one, Finset.prod_const_one]
  rw [row_star]
  calc finiteSquarefreeRow P hgood S (-1) ^ 5
      = finiteSquarefreeRow P hgood S (-1) * (finiteSquarefreeRow P hgood S (-1) ^ 2) ^ 2 := by
        ring
    _ = _ := by rw [h2]; ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hp hcop hc in
theorem pair_bilinear_expand (R : Finset ι) (α β : Finset ι → ℂ) :
    (∑ A ∈ R.powerset, ∑ B ∈ R.powerset,
      if Disjoint A B then quadraticCrossPhase p hg A B *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) * star (α A) * β B else 0) =
      ∑ χ : RayCharacter, ∑ η : RayCharacter, crossCoeff χ η *
        ∑ t ∈ R.powerset, (-1 : ℂ) ^ t.card *
          (star (∑ a' ∈ (R \ t).powerset,
              star (rayCharacter χ (∏ i ∈ t ∪ a', p i)) *
                finiteSquarefreeRow (fun i => Ideal.span {p i}) hg (t ∪ a') (-1) * α (t ∪ a')) *
            ∑ b' ∈ (R \ t).powerset, rayCharacter η (∏ i ∈ t ∪ b', p i) * β (t ∪ b')) := by
  let Fχ : RayCharacter → Finset ι → ℂ := fun χ A =>
    star (rayCharacter χ (∏ i ∈ A, p i)) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) * α A
  let Gη : RayCharacter → Finset ι → ℂ := fun η B => rayCharacter η (∏ i ∈ B, p i) * β B
  have hterm : ∀ A B : Finset ι, (if Disjoint A B then quadraticCrossPhase p hg A B *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) * star (α A) * β B else 0) =
      ∑ χ : RayCharacter, ∑ η : RayCharacter, crossCoeff χ η *
        (if Disjoint A B then star (Fχ χ A) * Gη η B else 0) := by
    intro A B
    by_cases hd : Disjoint A B
    · rw [if_pos hd, RayFourExpansion.quadraticCrossPhase_character_expansion p hp hcop hg hc
        A B hd]
      simp only [if_pos hd, Finset.sum_mul, Fχ, Gη, star_mul, star_star,
        star_row_neg_one]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro η _
      ring
    · simp [hd]
  have hproj : ∀ χ η : RayCharacter,
      (∑ A ∈ R.powerset, ∑ B ∈ R.powerset,
        if Disjoint A B then star (Fχ χ A) * Gη η B else 0) =
      ∑ t ∈ R.powerset, (-1 : ℂ) ^ t.card *
        (star (∑ a' ∈ (R \ t).powerset, Fχ χ (t ∪ a')) *
          ∑ b' ∈ (R \ t).powerset, Gη η (t ∪ b')) := by
    intro χ η
    rw [disjoint_pair_projector R (fun A => star (Fχ χ A)) (Gη η)]
    simp only [star_sum]
  calc (∑ A ∈ R.powerset, ∑ B ∈ R.powerset,
        if Disjoint A B then quadraticCrossPhase p hg A B *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) * star (α A) * β B else 0)
      = ∑ A ∈ R.powerset, ∑ B ∈ R.powerset, ∑ χ : RayCharacter, ∑ η : RayCharacter,
          crossCoeff χ η * (if Disjoint A B then star (Fχ χ A) * Gη η B else 0) := by
        apply Finset.sum_congr rfl; intro A _
        apply Finset.sum_congr rfl; intro B _
        exact hterm A B
    _ = ∑ A ∈ R.powerset, ∑ χ : RayCharacter, ∑ B ∈ R.powerset, ∑ η : RayCharacter,
          crossCoeff χ η * (if Disjoint A B then star (Fχ χ A) * Gη η B else 0) := by
        apply Finset.sum_congr rfl; intro A _
        exact Finset.sum_comm
    _ = ∑ χ : RayCharacter, ∑ A ∈ R.powerset, ∑ B ∈ R.powerset, ∑ η : RayCharacter,
          crossCoeff χ η * (if Disjoint A B then star (Fχ χ A) * Gη η B else 0) :=
        Finset.sum_comm
    _ = ∑ χ : RayCharacter, ∑ A ∈ R.powerset, ∑ η : RayCharacter, ∑ B ∈ R.powerset,
          crossCoeff χ η * (if Disjoint A B then star (Fχ χ A) * Gη η B else 0) := by
        apply Finset.sum_congr rfl; intro χ _
        apply Finset.sum_congr rfl; intro A _
        exact Finset.sum_comm
    _ = ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ A ∈ R.powerset, ∑ B ∈ R.powerset,
          crossCoeff χ η * (if Disjoint A B then star (Fχ χ A) * Gη η B else 0) := by
        apply Finset.sum_congr rfl; intro χ _
        exact Finset.sum_comm
    _ = _ := by
        apply Finset.sum_congr rfl; intro χ _
        apply Finset.sum_congr rfl; intro η _
        simp only [← Finset.mul_sum]
        rw [hproj χ η]

end
end Qrh.MarkedAnchor.Inverse.Poisson
