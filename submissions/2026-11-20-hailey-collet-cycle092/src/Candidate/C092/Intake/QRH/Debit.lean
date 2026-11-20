/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Mathlib.Tactic

/-!
# Appendix Q: normalized conductor debit

This file proves the real inequalities in (Q2), including the exterior case.
The analytic estimate and the box-specific bounds are explicit hypotheses.
No finite certificate, source estimate, or zero-free theorem is assumed here.
-/

namespace QRH.Cycle090

noncomputable section

/-- The positive part of a real exponent. -/
def positivePart (x : ℝ) : ℝ := max 0 x

/-- Appendix Q.1's debit in the conductor units `U = Z ^ D`. -/
def normalizedDebit (B ε hLower : ℝ) : ℝ := (max 0 B + ε) / hLower

/-- The literal capped capacity `C(D)` in (Q1), with its positive source cost exposed. -/
def cappedCapacity (cap y sourceCost D : ℝ) : ℝ :=
  min (cap * D) ((2 * y - (1 + sourceCost) * D) / (2 + 10 * sourceCost))

/-- The conductor-dependent terms of (Q1); `base` contains all terms fixed in `D`. -/
def conductorPrice (base d p R capacity D : ℝ) : ℝ :=
  base - 9 / 100 * D - d * p * capacity / 2 + 3 * D * R / 4

/-- The rectangular slope lower bound `S` in Appendix Q.1. -/
def boxSlope (densityUpper cap : ℝ) : ℝ :=
  3 / 4 * (1 - densityUpper) - 9 / 100 - densityUpper * cap / 4

/-- The minimum of the native and affine capacities has upper secant slope `cap`. -/
theorem cappedCapacity_increment_le {cap y sourceCost D h : ℝ}
    (hcap : 0 ≤ cap) (hs : 0 ≤ sourceCost) (hDh : D ≤ h) :
    cappedCapacity cap y sourceCost h - cappedCapacity cap y sourceCost D ≤
      cap * (h - D) := by
  unfold cappedCapacity
  rcases le_total (cap * D)
      ((2 * y - (1 + sourceCost) * D) / (2 + 10 * sourceCost)) with hleft | hright
  · rw [min_eq_left hleft]
    have htop := min_le_left (cap * h)
      ((2 * y - (1 + sourceCost) * h) / (2 + 10 * sourceCost))
    nlinarith
  · rw [min_eq_right hright]
    have htop := min_le_right (cap * h)
      ((2 * y - (1 + sourceCost) * h) / (2 + 10 * sourceCost))
    have hnum : 2 * y - (1 + sourceCost) * h ≤
        2 * y - (1 + sourceCost) * D := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + sourceCost) (sub_nonneg.mpr hDh)]
    have hquot := div_le_div_of_nonneg_right hnum
      (by linarith : 0 ≤ 2 + 10 * sourceCost)
    have hgap := mul_nonneg hcap (sub_nonneg.mpr hDh)
    linarith

/-- The count baseline and capacity secant prove the rectangular slope used in (Q2). -/
theorem conductorPrice_secant_lower {base d p R cap b capacityD capacityH D h : ℝ}
    (hd : 0 ≤ d) (hp : 0 ≤ p) (hpUpper : p ≤ 1 / 2) (hdb : d ≤ b)
    (hcap : 0 ≤ cap) (hR : 1 - d ≤ R) (hDh : D ≤ h)
    (hCapacity : capacityH - capacityD ≤ cap * (h - D)) :
    boxSlope b cap * (h - D) ≤
      conductorPrice base d p R capacityH h - conductorPrice base d p R capacityD D := by
  have hdp : d * p ≤ b / 2 := by
    have h := mul_le_mul_of_nonneg_left hpUpper hd
    nlinarith
  have hdpCap := mul_le_mul_of_nonneg_right hdp hcap
  have hcoefficient : boxSlope b cap ≤ 3 * R / 4 - 9 / 100 - d * p * cap / 2 := by
    unfold boxSlope
    nlinarith
  have hsl := mul_le_mul_of_nonneg_right hcoefficient (sub_nonneg.mpr hDh)
  have hpayment := mul_le_mul_of_nonneg_left hCapacity
    (by positivity : 0 ≤ d * p / 2)
  unfold conductorPrice
  nlinarith

/-- A lower secant slope transports a checked top excess into the envelope in (Q2). -/
theorem price_envelope_of_secant {priceTop priceAt target B S h D : ℝ}
    (hTop : priceTop - target ≤ B)
    (hSlope : S * (h - D) ≤ priceTop - priceAt) :
    priceAt - target ≤ B - S * (h - D) := by
  linarith

/-- A nonnegative allocated fee gives a nonnegative normalized debit. -/
theorem normalizedDebit_nonneg {B ε hLower : ℝ}
    (hε : 0 ≤ ε) (hLower_pos : 0 < hLower) :
    0 ≤ normalizedDebit B ε hLower := by
  unfold normalizedDebit
  exact div_nonneg (add_nonneg (le_max_left 0 B) hε) (le_of_lt hLower_pos)

/-- Normalizing at a lower conductor endpoint pays the actual top excess. -/
theorem normalizedDebit_clears_top {B ε hLower h : ℝ}
    (hε : 0 ≤ ε) (hLower_pos : 0 < hLower) (hLower_le : hLower ≤ h) :
    B + ε ≤ h * normalizedDebit B ε hLower := by
  have hq := normalizedDebit_nonneg (B := B) hε hLower_pos
  have heq : hLower * normalizedDebit B ε hLower = max 0 B + ε := by
    unfold normalizedDebit
    field_simp [ne_of_gt hLower_pos]
  calc
    B + ε ≤ max 0 B + ε := by linarith [le_max_right 0 B]
    _ = hLower * normalizedDebit B ε hLower := heq.symm
    _ ≤ h * normalizedDebit B ε hLower := mul_le_mul_of_nonneg_right hLower_le hq

/-- A top debit and a slope lower bound pay every nonnegative lower conductor. -/
theorem positivePart_affine_debit {B ε S h D q : ℝ}
    (hD : 0 ≤ D) (hDh : D ≤ h) (hq : 0 ≤ q) (hSq : q ≤ S)
    (hTop : B + ε ≤ h * q) :
    positivePart (B + ε - S * (h - D)) ≤ D * q := by
  unfold positivePart
  apply max_le
  · exact mul_nonneg hD hq
  · have hslope := mul_le_mul_of_nonneg_right hSq (sub_nonneg.mpr hDh)
    nlinarith

/-- The first comparison in (Q2) transports a real price bound to its positive part. -/
theorem positivePart_price_envelope {E t B ε S h D : ℝ}
    (hE : E - t ≤ B - S * (h - D)) :
    positivePart (E - t + ε) ≤ positivePart (B + ε - S * (h - D)) := by
  unfold positivePart
  exact max_le_max (le_refl 0) (by linarith)

/-- Equation (Q2), with all conductor, fee, and analytic-envelope hypotheses visible. -/
theorem normalized_debit_Q2 {E t B ε S h D hLower : ℝ}
    (hε : 0 ≤ ε) (hLower_pos : 0 < hLower) (hLower_le : hLower ≤ h)
    (hD : 0 ≤ D) (hDh : D ≤ h)
    (hSq : normalizedDebit B ε hLower ≤ S)
    (hE : E - t ≤ B - S * (h - D)) :
    positivePart (E - t + ε) ≤ D * normalizedDebit B ε hLower := by
  exact le_trans (positivePart_price_envelope hE)
    (positivePart_affine_debit hD hDh
      (normalizedDebit_nonneg hε hLower_pos) hSq
      (normalizedDebit_clears_top hε hLower_pos hLower_le))

/-- The complete scalar (Q1)–(Q2) implication, using the literal capped price. -/
theorem normalized_physical_debit_Q2
    {base d p R cap b y sourceCost t B ε h D hLower : ℝ}
    (hd : 0 ≤ d) (hp : 0 ≤ p) (hpUpper : p ≤ 1 / 2) (hdb : d ≤ b)
    (hcap : 0 ≤ cap) (hs : 0 ≤ sourceCost) (hR : 1 - d ≤ R)
    (hε : 0 ≤ ε) (hLower_pos : 0 < hLower) (hLower_le : hLower ≤ h)
    (hD : 0 ≤ D) (hDh : D ≤ h)
    (hSq : normalizedDebit B ε hLower ≤ boxSlope b cap)
    (hTop : conductorPrice base d p R (cappedCapacity cap y sourceCost h) h - t ≤ B) :
    positivePart
        (conductorPrice base d p R (cappedCapacity cap y sourceCost D) D - t + ε) ≤
      D * normalizedDebit B ε hLower := by
  apply normalized_debit_Q2 hε hLower_pos hLower_le hD hDh hSq
  apply price_envelope_of_secant hTop
  exact conductorPrice_secant_lower hd hp hpUpper hdb hcap hR hDh
    (cappedCapacity_increment_le hcap hs hDh)

/-- A strictly paid top and nonnegative slope pay the whole exterior interval. -/
theorem exterior_positivePart_eq_zero {E t B ε S h D : ℝ}
    (hB : B < -ε) (hS : 0 ≤ S) (hDh : D ≤ h)
    (hE : E - t ≤ B - S * (h - D)) :
    positivePart (E - t + ε) = 0 := by
  unfold positivePart
  apply max_eq_left
  have hslope : 0 ≤ S * (h - D) := mul_nonneg hS (sub_nonneg.mpr hDh)
  linarith

/-- For a nonnegative cleared margin, divide its lower bound by the upper denominator. -/
theorem cleared_margin_nonnegative {M A J JUpper : ℝ}
    (hM : 0 ≤ M) (hMA : M ≤ A) (hJ : 0 < J) (hJUpper : J ≤ JUpper) :
    M / JUpper ≤ A / J := by
  have hUpper : 0 < JUpper := lt_of_lt_of_le hJ hJUpper
  have hratio : 0 ≤ M / JUpper := div_nonneg hM (le_of_lt hUpper)
  have hmul := mul_le_mul_of_nonneg_left hJUpper hratio
  have heq : (M / JUpper) * JUpper = M := by
    field_simp [ne_of_gt hUpper]
  apply (le_div_iff₀ hJ).mpr
  nlinarith

/-- For a nonpositive cleared margin, divide its lower bound by the lower denominator. -/
theorem cleared_margin_nonpositive {M A JLower J : ℝ}
    (hM : M ≤ 0) (hMA : M ≤ A) (hLower : 0 < JLower) (hJLower : JLower ≤ J) :
    M / JLower ≤ A / J := by
  have hJ : 0 < J := lt_of_lt_of_le hLower hJLower
  have hratio : M / JLower ≤ 0 := div_nonpos_of_nonpos_of_nonneg hM (le_of_lt hLower)
  have hmul := mul_le_mul_of_nonpos_left hJLower hratio
  have heq : (M / JLower) * JLower = M := by
    field_simp [ne_of_gt hLower]
  apply (le_div_iff₀ hJ).mpr
  nlinarith

/-- Taking the stronger of two lower bounds preserves its meaning. -/
theorem combine_margin_bounds {a b margin : ℝ} (ha : a ≤ margin) (hb : b ≤ margin) :
    max a b ≤ margin := max_le ha hb

end

end QRH.Cycle090
