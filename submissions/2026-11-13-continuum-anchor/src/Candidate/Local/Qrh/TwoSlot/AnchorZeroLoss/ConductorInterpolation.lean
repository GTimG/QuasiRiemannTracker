/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Conductor interpolation for a capacity which is the minimum of two affine
prices. Different count branches may pay the two endpoints. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.PositiveGap.Return.Conductor

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss

/-- Only the capacity's two affine components are interpolated. The row function
may use a finite count envelope, with different minimizers at its endpoints. -/
theorem min_capacity_interval (f : ℝ → ℝ → ℝ) (c₁ c₂ : ℝ → ℝ)
    {lo hi d M : ℝ} (hd : d ∈ Set.Icc lo hi)
    (hanti : ∀ x a b : ℝ, a ≤ b → f x b ≤ f x a)
    (h₁ : ∃ A S : ℝ, ∀ x : ℝ, f x (c₁ x) = A+x*S)
    (h₂ : ∃ A S : ℝ, ∀ x : ℝ, f x (c₂ x) = A+x*S)
    (hlo : f lo (min (c₁ lo) (c₂ lo)) ≤ M)
    (hhi : f hi (min (c₁ hi) (c₂ hi)) ≤ M) :
    f d (min (c₁ d) (c₂ d)) ≤ M := by
  obtain ⟨A₁,S₁,h₁⟩ := h₁
  obtain ⟨A₂,S₂,h₂⟩ := h₂
  have hleft : f d (c₁ d) ≤ M :=
    QRH.PositiveGap.Return.affine_interval_le (f := fun x => f x (c₁ x)) h₁ hd
      ((hanti lo _ _ (min_le_left _ _)).trans hlo)
      ((hanti hi _ _ (min_le_left _ _)).trans hhi)
  have hright : f d (c₂ d) ≤ M :=
    QRH.PositiveGap.Return.affine_interval_le (f := fun x => f x (c₂ x)) h₂ hd
      ((hanti lo _ _ (min_le_right _ _)).trans hlo)
      ((hanti hi _ _ (min_le_right _ _)).trans hhi)
  rcases le_total (c₁ d) (c₂ d) with h | h
  · simpa only [min_eq_left h] using hleft
  · simpa only [min_eq_right h] using hright

end Qrh.TwoSlot.AnchorZeroLoss
