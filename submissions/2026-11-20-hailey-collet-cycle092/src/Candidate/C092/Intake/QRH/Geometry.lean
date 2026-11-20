/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.Constants

/-!
# Exact physical geometry and exponent cancellation

This file proves the rational geometry stated in Q.1/P8 for every conductor
in the directed interval. It also proves the exponent identity in Q.4.
No analytic source estimate or physical cover is assumed or constructed here.
-/

set_option autoImplicit false

namespace QRH.Cycle090

noncomputable section

/-- The common slot width in Q.1. -/
def ell : ℝ := 11 / 3 - 4 * theta

/-- The first physical length as a function of the conductor. -/
def xLength (h : ℝ) : ℝ := 1 + ell - h

/-- The second physical length, distinguished from ordinary source labels. -/
def yLength (h : ℝ) : ℝ := h - 2 * ell

/-- The physical normalization exponent in Q.4. -/
def kPhys (h : ℝ) : ℝ := 5 / 6 - xLength h / 3 - ell / 6

/-- The averaged-floor price used in P.4 and inherited by Q.1. -/
def floorPrice (h D : ℝ) : ℝ :=
  51 / 100 - 49 * h / 150 + 51 * ell / 100 + 33 * D / 50

/-- The defining width recovers the target boundary. -/
theorem theta_from_ell : theta = 11 / 12 - ell / 4 := by
  unfold ell
  ring

/-- The physical lengths have the exact total width required by B(199). -/
theorem physical_length_sum (h : ℝ) : xLength h + yLength h = 1 - ell := by
  unfold xLength yLength
  ring

/-- Exact cancellation of the normalization and signed Gram exponents (Q.4). -/
theorem physical_exponent_identity (h : ℝ) :
    kPhys h + xLength h / 2 + (yLength h - xLength h) / 12 = theta := by
  unfold kPhys xLength yLength ell
  ring

/-- The extra exponent in B(199) is exactly `5ℓ - 1`. -/
theorem gram_extra_identity (h : ℝ) :
    1 + 3 * ell - 2 * (xLength h + yLength h) = 5 * ell - 1 := by
  rw [physical_length_sum]
  ring

/-- The extra Gram exponent is strictly negative throughout the interval. -/
theorem gram_extra_negative (h : ℝ) :
    1 + 3 * ell - 2 * (xLength h + yLength h) < 0 := by
  rw [gram_extra_identity]
  norm_num [ell, theta]

/-- The actual signed signal exponent, rather than merely its length labels, exceeds `0.1`. -/
theorem signed_signal_positive {h : ℝ} (hhi : h ≤ hUpper) :
    (1 / 10 : ℝ) < theta - kPhys h := by
  norm_num [hUpper, theta, kPhys, xLength, ell] at hhi ⊢
  linarith

/-- Linear geometric guards from P8 at every Q conductor, before padding. -/
theorem physical_geometry {h : ℝ} (hlo : hLower ≤ h) (hhi : h ≤ hUpper) :
    (1 / 2 : ℝ) < h ∧ ell < xLength h ∧ xLength h < yLength h ∧
    yLength h < 1 / 2 ∧ 0 < 2 * xLength h - yLength h - ell ∧
    5 * ell < 1 ∧ (1 / 10 : ℝ) < xLength h := by
  norm_num [hLower, hUpper] at hlo hhi
  norm_num [ell, theta, xLength, yLength]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- The true padded support satisfies the original conductor and height guards. -/
theorem padded_geometry {h : ℝ} (hlo : hLower ≤ h) (hhi : h ≤ hUpper) :
    0 < h + rowPad ∧ h + rowPad < 173 / 200 ∧
    h + rowPad < 2 * yLength h ∧
    (1 / 5 : ℝ) < ell / (h + rowPad) ∧
    yLength h / (1 / 200) < 99 ∧
    5 * (h + rowPad) / 288 < 1 / 50 := by
  have hp0 : 0 < rowPad := allowances_pos.2.1
  have hp1 := rowPad_small
  have hh0 : 0 < h := lt_of_lt_of_le conductor_interval.1 hlo
  have hsum : 0 < h + rowPad := add_pos hh0 hp0
  norm_num [hLower, hUpper] at hlo hhi
  refine ⟨hsum, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · norm_num [yLength, ell, theta]
    linarith
  · apply (lt_div_iff₀ hsum).2
    norm_num [ell, theta]
    linarith
  · norm_num [yLength, ell, theta]
    linarith
  · linarith

/-- The actual row-padding convention gives support through `h + F_pad`. -/
theorem actual_support {h t D : ℝ} (ht : t ≤ rowPad / 4)
    (hD : D ≤ h + rowPad / 2 + 2 * t) : D ≤ h + rowPad := by
  linarith

/-- The small-row and independent principal comparison have the stated strict room. -/
theorem small_and_principal {h e : ℝ}
    (hlo : hLower ≤ h) (hhi : h ≤ hUpper)
    (he0 : 0 < e) (he1 : e ≤ 1 / 1000) :
    (1 / 4000 : ℝ) < yLength h / 20 - e * (1 + h) ∧
    (1 / 4000 : ℝ) < h / 600 - e := by
  have hh0 : 0 < h := lt_of_lt_of_le conductor_interval.1 hlo
  have hprod : e * (1 + h) ≤ (1 / 1000 : ℝ) * (1 + hUpper) :=
    mul_le_mul he1 (by linarith) (by linarith) (by norm_num)
  norm_num [hLower, hUpper, yLength, ell, theta] at hlo hhi hprod ⊢
  constructor <;> linarith

/-- The averaged-floor price retains more than `10⁻³` after its two stated fees. -/
theorem floor_price_margin {h D : ℝ}
    (_hlo : hLower ≤ h) (hhi : h ≤ hUpper) (hD : D ≤ h + rowPad) :
    floorPrice h D + 1 / 100000 + 1 / 1000000000000 + 1 / 1000 < theta := by
  have hp := rowPad_small
  norm_num [hUpper, floorPrice, ell, theta] at hhi ⊢
  linarith

end

end QRH.Cycle090
