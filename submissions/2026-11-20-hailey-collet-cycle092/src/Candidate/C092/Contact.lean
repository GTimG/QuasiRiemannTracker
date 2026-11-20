/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.ContactReceipt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Global scalar inverse-count tangent, Appendix E (18)--(24).
This does not assert the separate analytic open-rectangle supplier. -/
set_option autoImplicit false
namespace QRH.ContactContinuation
open QRH.ContactCertificate QRH.RationalInterval
noncomputable section

def contactPolynomial (w : ℝ) : ℝ :=
  19^5*(3*w-2)^4*(9*w+2)^5-567*w^4*(45*w-14)^5
def radial (w : ℝ) : ℝ := value w radialExpr
def radical (r : ℝ) : ℝ := (5/16)*(7*r^4*(r-2/3)) ^ (1/5 : ℝ)
def inverseCount (r : ℝ) : ℝ := 11*r/16-7/24-radical r
def weight (r w : ℝ) : ℝ := (4*(r/w)+(r-2/3)/(w-2/3))/5

theorem contact_polynomial {x : ℝ} (hx : x < 11/12)
    (hz : rootPolynomial x = 0) : contactPolynomial (wValue x) = 0 := by
  have hd : 12*x-11 ≠ 0 := by linarith
  have hid : contactPolynomial (wValue x) =
      -49152 * rootPolynomial x / (12*x-11)^9 := by
    unfold contactPolynomial wValue rootPolynomial
    field_simp
    ring
  rw [hid, hz]
  simp

theorem radial_formula {w : ℝ} (hw : 45*w-14 ≠ 0) :
    radial w = 95*(3*w-2)*(9*w+2)/(48*(45*w-14)) := by
  change 11*w/16-7/24-(w+12-(45/2)*w*w)/(45*w-14) = _
  field_simp [hw]
  ring_nf
  field_simp [show -14+w*45 ≠ 0 by intro hz; apply hw; linarith]
  ring

theorem radial_pow {w : ℝ} (hw : 45*w-14 ≠ 0)
    (hz : contactPolynomial w = 0) :
    radial w ^ 5 = (5/16 : ℝ)^5 * 7*w^4*(w-2/3) := by
  rw [radial_formula hw]
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 5 (mul_ne_zero (by norm_num) hw))).2
  unfold contactPolynomial at hz
  linear_combination 3125*(3*w-2)*hz

theorem weighted_fifth {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a^4*b ≤ ((4*a+b)/5)^5 := by
  have hp : 0 ≤ (a-b)^2*(1024*a^3+203*a^2*b+22*a*b^2+b^3) := by positivity
  have hi : (4*a+b)^5-3125*a^4*b =
      (a-b)^2*(1024*a^3+203*a^2*b+22*a*b^2+b^3) := by ring
  have h : 3125*a^4*b ≤ (4*a+b)^5 := by linarith
  calc
    a^4*b = (3125*a^4*b)/3125 := by ring
    _ ≤ (4*a+b)^5/3125 := div_le_div_of_nonneg_right h (by norm_num)
    _ = ((4*a+b)/5)^5 := by ring

theorem radical_pow {r : ℝ} (hr : 2/3 ≤ r) :
    radical r ^ 5 = (5/16 : ℝ)^5*7*r^4*(r-2/3) := by
  have hn : 0 ≤ 7*r^4*(r-2/3) := by positivity
  have he : ((7*r^4*(r-2/3)) ^ (1/5 : ℝ))^5 = 7*r^4*(r-2/3) := by
    rw [← Real.rpow_mul_natCast hn]
    norm_num
  simp only [radical, mul_pow, he]
  ring

theorem radial_tangent {r w : ℝ} (hr : 2/3 ≤ r) (hw : 2/3 < w)
    (hc : 0 ≤ radial w) (hpow : radial w ^ 5 = (5/16 : ℝ)^5*7*w^4*(w-2/3)) :
    radical r ≤ radial w * weight r w := by
  have hw0 : 0 < w := by linarith
  have hwm : 0 < w-2/3 := by linarith
  have hr0 : 0 ≤ r := by linarith
  have ha : 0 ≤ r/w := div_nonneg hr0 hw0.le
  have hb : 0 ≤ (r-2/3)/(w-2/3) := div_nonneg (by linarith) hwm.le
  have hag := weighted_fifth ha hb
  have hwp : 0 ≤ weight r w := by unfold weight; positivity
  have he : (radial w)^5 * ((r/w)^4*((r-2/3)/(w-2/3))) =
      (5/16 : ℝ)^5*7*r^4*(r-2/3) := by
    rw [hpow]
    have hn : -2+w*3 ≠ 0 := by linarith
    field_simp [ne_of_gt hw0, ne_of_gt hwm, hn]
    ring_nf
    field_simp [hn]
    ring
  apply (pow_le_pow_iff_left₀ (by unfold radical; positivity)
    (mul_nonneg hc hwp) (by decide : (5 : ℕ) ≠ 0)).mp
  rw [radical_pow hr, ← he, mul_pow]
  exact mul_le_mul_of_nonneg_left hag (by positivity)

/-- The receipt coefficients are exactly the weighted supporting line. -/
theorem coefficient_line {r w : ℝ} (hw : 2/3 < w) :
    g0 w-g1 w*r = 11*r/16-7/24-radial w*weight r w := by
  have hw0 : w ≠ 0 := ne_of_gt (by linarith : 0 < w)
  have hwm : w-2/3 ≠ 0 := ne_of_gt (by linarith : 0 < w-2/3)
  have hden : 45*w-14 ≠ 0 := ne_of_gt (by linarith : 0 < 45*w-14)
  simp [g0, g1, g0Expr, g1Expr, radial, radialExpr, interceptExpr, value, weight]
  have hn : -2+w*3 ≠ 0 := by linarith
  have hn45 : -14+w*45 ≠ 0 := by linarith
  field_simp [hw0, hwm, hden, hn, hn45]
  ring_nf
  field_simp [hn, hn45]
  ring

theorem actual_contact_domain {x : ℝ} (hx : Contains alphaInterval x) :
    2/3 < wValue x := by
  have h := (w_enclosed hx).1
  have hl : (7523/10000 : ℝ) < (wInterval.lo : ℝ) := by
    have ht := (Rat.cast_lt (K := ℝ)).mpr w_narrow.1
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ht
    exact ht
  linarith

theorem actual_radial_positive {x : ℝ} (hx : Contains alphaInterval x) :
    0 < radial (wValue x) := by
  have hw := actual_contact_domain hx
  rw [radial_formula (ne_of_gt (by linarith : 0 < 45*wValue x-14))]
  apply div_pos
  · have h₁ : 0 < 3*wValue x-2 := by linarith
    have h₂ : 0 < 9*wValue x+2 := by linarith
    positivity
  · linarith

/-- The isolated polynomial root certifies the actual positive fifth-root branch. -/
theorem actual_radial_eq {x : ℝ} (hx : Contains alphaInterval x)
    (hz : rootPolynomial x = 0) : radial (wValue x) = radical (wValue x) := by
  have hw := actual_contact_domain hx
  have hxu : x < 11/12 := by
    have hu := real_root_bracket.2.2.1
    have hxhi := hx.2
    change x ≤ (alphaHi : ℝ) at hxhi
    linarith
  have hp := radial_pow (ne_of_gt (by linarith : 0 < 45*wValue x-14))
    (contact_polynomial hxu hz)
  have hp' := radical_pow hw.le
  have he : radial (wValue x)^5 = radical (wValue x)^5 := hp.trans hp'.symm
  have hr : 0 ≤ radical (wValue x) := by unfold radical; positivity
  have hc := (actual_radial_positive hx).le
  exact le_antisymm ((pow_le_pow_iff_left₀ hc hr (by decide : (5 : ℕ) ≠ 0)).mp he.le)
    ((pow_le_pow_iff_left₀ hr hc (by decide : (5 : ℕ) ≠ 0)).mp he.ge)

/-- The genuine inverse-count formula lies above the receipt's exact contact line
on its whole nonnegative-radical domain, hence on `[3/4,7/9]`. No tangent or
convexity hypothesis is assumed. -/
theorem actual_inverseCount_support {x r : ℝ} (hx : Contains alphaInterval x)
    (hz : rootPolynomial x = 0) (hr : 2/3 ≤ r) :
    g0 (wValue x)-g1 (wValue x)*r ≤ inverseCount r := by
  have hw := actual_contact_domain hx
  have hp := actual_radial_eq hx hz
  have hpow : radial (wValue x)^5 =
      (5/16 : ℝ)^5*7*(wValue x)^4*(wValue x-2/3) := by
    rw [hp]; exact radical_pow hw.le
  have ht := radial_tangent hr hw (actual_radial_positive hx).le hpow
  rw [coefficient_line hw]
  unfold inverseCount
  linarith

/-- The same line touches the genuine count at the certified contact. -/
theorem actual_inverseCount_contact {x : ℝ} (hx : Contains alphaInterval x)
    (hz : rootPolynomial x = 0) :
    g0 (wValue x)-g1 (wValue x)*wValue x = inverseCount (wValue x) := by
  have hw := actual_contact_domain hx
  rw [coefficient_line hw]
  have he : weight (wValue x) (wValue x) = 1 := by
    unfold weight
    rw [div_self (ne_of_gt (by linarith : 0 < wValue x)),
      div_self (ne_of_gt (by linarith : 0 < wValue x-2/3))]
    norm_num
  rw [he, mul_one, actual_radial_eq hx hz]
  rfl

/-- The directed receipt endpoints give a certified rational affine minorant. -/
theorem receipt_inverseCount_support {x r : ℝ} (hx : Contains alphaInterval x)
    (hz : rootPolynomial x = 0) (hr : 2/3 ≤ r) :
    (g0Receipt.lo : ℝ)-(g1Receipt.hi : ℝ)*r ≤ inverseCount r := by
  have hl := (g0_receipt_sound hx).1
  have hu := (g1_receipt_sound hx).2
  have hr0 : 0 ≤ r := by linarith
  have hm := mul_le_mul_of_nonneg_right hu hr0
  have hs := actual_inverseCount_support hx hz hr
  linarith

/-- An actual certified contact and its global supporting line exist. -/
theorem certified_inverseCount_tangent : ∃ x : ℝ,
    Contains alphaInterval x ∧ rootPolynomial x = 0 ∧
    (∀ r : ℝ, 2/3 ≤ r → g0 (wValue x)-g1 (wValue x)*r ≤ inverseCount r) ∧
    g0 (wValue x)-g1 (wValue x)*wValue x = inverseCount (wValue x) := by
  rcases root_exists with ⟨x,hx,hz⟩
  exact ⟨x,hx,hz,fun _ hr => actual_inverseCount_support hx hz hr,
    actual_inverseCount_contact hx hz⟩

/-- The rational receipt line minorizes the real formula unconditionally on its
domain. In particular this covers the whole manuscript interval `[3/4,7/9]`. -/
theorem receipt_inverseCount_global {r : ℝ} (hr : 2/3 ≤ r) :
    (g0Receipt.lo : ℝ)-(g1Receipt.hi : ℝ)*r ≤ inverseCount r := by
  rcases root_exists with ⟨x,hx,hz⟩
  exact receipt_inverseCount_support hx hz hr

end
end QRH.ContactContinuation
