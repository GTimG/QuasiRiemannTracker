/- Copyright (c) 2026 Sil. Apache-2.0.
Unit part of the fourth-power transfer. Nonunit local vanishing is separate. -/
import Mathlib.NumberTheory.GaussSum
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.GaussUnits

open AddChar MulChar
open scoped BigOperators

variable {R K : Type*} [CommRing R] [Fintype R] [Field K]

/-- This is the actual finite Fourier sum, with arbitrary frequency. -/
noncomputable def row (χ : MulChar R K) (ψ : AddChar R K) (k : R) : K :=
  ∑ a : R, χ a * ψ (k*a)

theorem shift (χ : MulChar R K) (ψ : AddChar R K) (k : R) (u : Rˣ) :
    row χ ψ (k*u) = (χ u)⁻¹ * row χ ψ k := by
  have h := gaussSum_mulShift_eq χ (ψ.mulShift k) u
  simpa only [row, gaussSum, AddChar.mulShift_apply, inv_apply_eq_inv', mul_assoc] using h

theorem inverse_fourth (z : K) (hz : z^6 = 1) : (z^4)⁻¹ = z^2 := by
  apply inv_eq_of_mul_eq_one_right
  calc
    z^4*z^2 = z^6 := by ring
    _ = 1 := hz

theorem value_sixth (χ : MulChar R K) (hχ : χ^6 = 1) (u : Rˣ) :
    (χ u)^6 = 1 := by
  rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
  simp [MulChar.one_apply, u.isUnit]

/-- The exact fourth-power frequency identity for every unit, with no
nontriviality assumption on the multiplicative or additive character. -/
theorem fourth_power (χ : MulChar R K) (ψ : AddChar R K)
    (hχ : χ^6 = 1) (k : R) (u : Rˣ) :
    row χ ψ (k*(u:R)^4) = (χ u)^2 * row χ ψ k := by
  have h := shift χ ψ k (u^4)
  rw [Units.val_pow_eq_pow_val, map_pow, inverse_fourth _ (value_sixth χ hχ u)] at h
  exact h

end Candidate.SilPrior.FourthPower.GaussUnits
