/- Copyright (c) 2026 Sil. Apache-2.0.
Finite first Möbius/ray projection, retaining the exact Nu^-1 weight.
Only a transparently stated matrix bound is used by this algebraic
mechanism; the next module supplies it from RawSideBounds.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedFirstRawKernel

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedFirstRawProjector
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily RayFourExpansion
open CenteredMomentFirstColumns
local notation "Id" => Ideal HeckeFamily.O

theorem scaled_norm_sum {κ : Type*} (S : Finset κ) (c f : κ → ℂ) (r : ℝ) (hr : 0 ≤ r) :
    r*‖∑i∈S,c i*f i‖ ≤ ∑i∈S,‖c i‖*(r*‖f i‖) := by
  apply (mul_le_mul_of_nonneg_left (norm_sum_le S (fun i => c i*f i)) hr).trans_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_mul]
  ring

theorem ray_projector (r H : ℝ) (hr : 0 ≤ r) (hH : 0 ≤ H)
    (u : Id) (matrix : RayCharacter → RayCharacter → ℂ)
    (hmat : ∀χ ξ,r*‖matrix χ ξ‖ ≤ H/(u.absNorm:ℝ)) :
    r*‖∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*matrix χ ξ‖ ≤
      256*H/(u.absNorm:ℝ) := by
  have hn : 0 ≤ H/(u.absNorm:ℝ) := div_nonneg hH (Nat.cast_nonneg _)
  calc
    _ ≤ ∑χ : RayCharacter,r*‖∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*matrix χ ξ‖ := by
      simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left
        (norm_sum_le Finset.univ (fun χ : RayCharacter => ∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*matrix χ ξ)) hr
    _ ≤ ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*(r*‖matrix χ ξ‖) :=
      Finset.sum_le_sum (fun χ _ => scaled_norm_sum Finset.univ (pairCoeff firstPhaseTable χ) (matrix χ) r hr)
    _ ≤ ∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*(H/(u.absNorm:ℝ)) :=
      Finset.sum_le_sum (fun χ _ => Finset.sum_le_sum (fun ξ _ =>
        mul_le_mul_of_nonneg_left (hmat χ ξ) (norm_nonneg _)))
    _ = (∑χ : RayCharacter,∑ξ : RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖)*(H/(u.absNorm:ℝ)) := by
      simp only [Finset.sum_mul]
    _ ≤ 256*(H/(u.absNorm:ℝ)) := mul_le_mul_of_nonneg_right firstPhaseTable_mass hn
    _ = _ := by ring

theorem mobius_ray_projector (Ls : Finset Id) (r H : ℝ) (hr : 0 ≤ r) (hH : 0 ≤ H)
    (phase : ℂ) (hphase : ‖phase‖ ≤ 1) (matrix : Id → RayCharacter → RayCharacter → ℂ)
    (hmat : ∀u∈Ls,(UniqueFactorizationMonoid.moebius u:ℂ)≠0 →
      ∀χ ξ,r*‖matrix u χ ξ‖ ≤ H/(u.absNorm:ℝ)) :
    r*‖∑u∈Ls,(UniqueFactorizationMonoid.moebius u:ℂ)*phase*
      ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*matrix u χ ξ‖ ≤
      256*H*∑u∈Ls,‖(UniqueFactorizationMonoid.moebius u:ℂ)‖/(u.absNorm:ℝ) := by
  apply (scaled_norm_sum Ls (fun u => (UniqueFactorizationMonoid.moebius u:ℂ)*phase)
    (fun u => ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*matrix u χ ξ) r hr).trans
  calc
    _ ≤ ∑u∈Ls,‖(UniqueFactorizationMonoid.moebius u:ℂ)‖*(256*H/(u.absNorm:ℝ)) := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases hμ : (UniqueFactorizationMonoid.moebius u:ℂ)=0
      · simp only [hμ,zero_mul,norm_zero,mul_zero,le_refl]
      · have hp : ‖(UniqueFactorizationMonoid.moebius u:ℂ)*phase‖ ≤ ‖(UniqueFactorizationMonoid.moebius u:ℂ)‖ := by
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) hphase
        exact mul_le_mul hp (ray_projector r H hr hH u (matrix u) (hmat u hu hμ))
          (mul_nonneg hr (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring

end
end Candidate.FourthPower.RepairedFirstRawProjector
