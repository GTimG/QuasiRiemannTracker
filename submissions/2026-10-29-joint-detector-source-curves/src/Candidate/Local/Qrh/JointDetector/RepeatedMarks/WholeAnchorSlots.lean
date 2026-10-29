/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Cycle61.Moment.WholeSourceFamily
import Candidate.Cycle63.Marked.NaturalSlotAnchor
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootHoleSlots

namespace Qrh.JointDetector.RepeatedMarks.WholeAnchorSlots
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentExceptionalPair
open CenteredMomentCommonMaskExpansion OAI.SevenEighths.Cycle61Moment
open OAI.SevenEighths.Cycle63MarkedPlain
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceAnchor (η₀ : Character) : WholeSourceIndex M H → Character :=
  Sum.elim (fun _ => η₀) (fun j =>
    (η₀.product (relativeCharacter M H hH η₀ j.1).inverse.inverse).product
      (HeckeRayQuotient.character M H hH j.2))

theorem relative_modulus (η₀ : Character) (θ : RayQuotient.Characters M H) :
    (relativeCharacter M H hH η₀ θ).modulus = M ⊓ η₀.modulus := rfl

/-- A conductor deletion can be removed when its bad primes already have
zero coefficient in the common source weights. -/
theorem excluded_slot_of_weight_support (χ : Character) (R : Ideal O) (hR : R≠0)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ)
    (hsupport : ∀ I ∈ pool, ¬IsCoprime I R → β I=0) :
    naturalSlot (excluded χ R) pool β P=naturalSlot χ pool β P := by
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [excluded_ideal _ _ hR]
  by_cases hc : IsCoprime I R
  · rw [if_pos hc]
  · rw [if_neg hc,hsupport I hI hc,mul_zero,mul_zero]

private theorem support_coprime {η₀ : Character} {θ : RayQuotient.Characters M H}
    {I R : Ideal O} (hR : R ∣ M ⊓ η₀.modulus)
    (hn : idealCoeff (relativeCharacter M H hH η₀ θ) I≠0) : IsCoprime I R := by
  have h := ((idealCoeff_ne_zero_iff _ _).mp hn).2
  rw [relative_modulus] at h
  exact h.of_isCoprime_of_dvd_right hR

/-- All zero-dictionary labels preserve the exact original relative slot.
No fixed bad-prime sectors are removed from the physical response. -/
theorem common_slot (η η₀ : Character) (u : O) (hu : u≠0)
    (j : WholeSourceIndex M H) (θ : RayQuotient.Characters M H)
    (pool : Finset (Ideal O)) (weight : Ideal O→ℂ) (P : ℝ) :
    naturalSlot (naturalRow (wholeSourceBase M H hH η₀ η j) u hu).character pool
      (fun I => idealCoeff (relativeCharacter M H hH (sourceAnchor M H hH η₀ j) θ) I*weight I) P =
    naturalSlot (naturalRow η u hu).character pool
      (fun I => idealCoeff (relativeCharacter M H hH η₀ θ) I*weight I) P := by
  cases j with
  | inl j => rfl
  | inr j =>
    let ν₁ := (relativeCharacter M H hH η₀ j.1).inverse.inverse
    let ν₂ := HeckeRayQuotient.character M H hH j.2
    let F := naturalRow η u hu
    let G := naturalRow (η.product ν₁) u hu
    let K := naturalRow ((η.product ν₁).product ν₂) u hu
    change naturalSlot K.character pool
      (fun I => idealCoeff (relativeCharacter M H hH ((η₀.product ν₁).product ν₂) θ) I*weight I) P = _
    rw [shifted_anchor_slot M H hH (η.product ν₁) (η₀.product ν₁) ν₂ u G K θ]
    rw [excluded_slot_of_weight_support G.character ν₂.modulus ν₂.modulus_ne_bot pool _ P (by
      intro I hI hc
      have hz : idealCoeff (relativeCharacter M H hH (η₀.product ν₁) θ) I=0 := by
        by_contra hn
        apply hc
        exact support_coprime M H hH (by change M ∣ M ⊓ _; exact Ideal.dvd_iff_le.mpr inf_le_left) hn
      rw [hz,zero_mul])]
    rw [shifted_anchor_slot M H hH η η₀ ν₁ u F G θ]
    apply excluded_slot_of_weight_support F.character ν₁.modulus ν₁.modulus_ne_bot pool _ P
    intro I hI hc
    have hz : idealCoeff (relativeCharacter M H hH η₀ θ) I=0 := by
      by_contra hn
      apply hc
      exact support_coprime M H hH (by change (M ⊓ η₀.modulus) ∣ (M ⊓ η₀.modulus); rfl) hn
    rw [hz,zero_mul]


theorem naturalSlot_excluded_weight (χ : Character) (root : Ideal O) (hroot : root≠0)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    naturalSlot (excluded χ root) pool β P =
      naturalSlot χ pool (fun I => β I * if IsCoprime I root then 1 else 0) P := by
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [excluded_ideal _ _ hroot]
  split_ifs <;> simp_all

/-- The common moving sixth-root hole remains in every original slot and
in every dictionary presentation; no prime-sector deletion is imposed. -/
theorem common_slot_root (η η₀ : Character) (u : O) (hu : u≠0)
    (j : WholeSourceIndex M H) (θ : RayQuotient.Characters M H)
    (root : Ideal O) (hroot : root≠0)
    (pool : Finset (Ideal O)) (weight : Ideal O→ℂ) (P : ℝ) :
    naturalSlot (excluded (naturalRow (wholeSourceBase M H hH η₀ η j) u hu).character root) pool
      (fun I => idealCoeff (relativeCharacter M H hH (sourceAnchor M H hH η₀ j) θ) I*weight I) P =
    naturalSlot (excluded (naturalRow η u hu).character root) pool
      (fun I => idealCoeff (relativeCharacter M H hH η₀ θ) I*weight I) P := by
  rw [naturalSlot_excluded_weight _ root hroot,naturalSlot_excluded_weight _ root hroot]
  simpa only [mul_assoc] using common_slot M H hH η η₀ u hu j θ pool
    (fun I => weight I * if IsCoprime I root then 1 else 0) P

end
end Qrh.JointDetector.RepeatedMarks.WholeAnchorSlots

#print axioms Qrh.JointDetector.RepeatedMarks.WholeAnchorSlots.common_slot_root
