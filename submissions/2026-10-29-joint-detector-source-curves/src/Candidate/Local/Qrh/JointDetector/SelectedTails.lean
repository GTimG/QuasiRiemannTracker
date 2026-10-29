/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Tail

/-!
# Selected-pair tails for the actual radial transform

The actual `paperRadialFourier` lattice-tail theorem is uniform over all pair
scales above a common positive lower scale. Summing over arbitrary selected
rows costs their cardinality times the squared dual mass. The coefficients
inside each frequency sum retain arbitrary signs and phases.
-/

namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

/-- Absolute selected-pair tail for the actual radial transform.

To apply the physical cutoff, take `K₀` to be the common lower pair scale
and prove that each omitted frequency satisfies `T ≤ K₀ * |h|²`.
The factor `(#R) * ∑ |z|²` is independent of frequency and pair scales.
-/
theorem selected_pair_radial_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {R : Type*} [Fintype R] (W : 𝓢(ℝ, ℂ))
        (frequencies : Set O) (K₀ T Γ : ℝ),
      0 < K₀ → 0 ≤ T → 0 ≤ Γ →
      (∀ h ∈ frequencies, T ≤ K₀ * ‖eisEmbedding h‖ ^ 2) →
      ∀ (scale : R → R → ℝ), (∀ r t, K₀ ≤ scale r t) →
      ∀ (q : R → R → O → ℂ), (∀ r t h, h ∈ frequencies → ‖q r t h‖ ≤ Γ) →
      ∀ z : R → ℂ,
      ‖∑ r, ∑ t, (z r * star (z t)) *
          (∑' h : frequencies, q r t h.val *
            paperRadialFourier W (scale r t * ‖eisEmbedding h.val‖ ^ 2))‖ ≤
        Γ * (Fintype.card R : ℝ) * (∑ r, ‖z r‖ ^ 2) *
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 K₀) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, htail⟩ := CenteredMomentTail.uniform_sector_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro R _ W frequencies K₀ T Γ hK₀ hT hΓ hfreq scale hscale q hq z
  let budget := Γ * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
    ((min 1 K₀) ^ 2 * (1 + T) ^ A)
  let tail : R → R → ℂ := fun r t => ∑' h : frequencies,
    q r t h.val * paperRadialFourier W (scale r t * ‖eisEmbedding h.val‖ ^ 2)
  have hbudget : 0 ≤ budget := by
    dsimp [budget]
    exact div_nonneg
      (mul_nonneg hΓ (mul_nonneg hC.le (apply_nonneg _ _))) (by positivity)
  have hpair (r t : R) : ‖tail r t‖ ≤ budget := by
    have h := htail W frequencies K₀ T Γ hK₀ hT hΓ hfreq
      (scale r t) (hscale r t) (q r t) (fun _ => 1) (hq r t) (by simp)
    simpa only [one_mul] using h
  have hmass : (∑ r, ‖z r‖) ^ 2 ≤
      (Fintype.card R : ℝ) * ∑ r, ‖z r‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset R) (fun _ => (1 : ℝ)) (fun r => ‖z r‖)
  change ‖∑ r, ∑ t, (z r * star (z t)) * tail r t‖ ≤ _
  calc
    _ ≤ ∑ r, ∑ t, ‖(z r * star (z t)) * tail r t‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum fun r _ => norm_sum_le _ _
    _ ≤ ∑ r, ∑ t, ‖z r‖ * ‖z t‖ * budget := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro t _
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hpair r t) (by positivity)
    _ = budget * (∑ r, ‖z r‖) ^ 2 := by
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_assoc]
    _ ≤ budget * ((Fintype.card R : ℝ) * ∑ r, ‖z r‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmass hbudget
    _ = _ := by dsimp [budget]; ring

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.selected_pair_radial_tail
