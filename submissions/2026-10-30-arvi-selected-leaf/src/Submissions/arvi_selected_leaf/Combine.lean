/-
Scalar bookkeeping for the selected leaf: one branch bound fits the combined constants.
-/
import Mathlib

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf
noncomputable section

/-- A bound `c·dg·ctl₁²·base^d₁·Z^e₁` fits `C·dg·ctl²·base^deg·Z^e` when every factor is dominated. -/
theorem fit_bound {c C dg ctl₁ ctl base Z e₁ e : ℝ} {d₁ deg : ℕ}
    (hc : 0 ≤ c) (hcC : c ≤ C) (hdg : 0 ≤ dg) (hctl₁ : 0 ≤ ctl₁) (hctl : ctl₁ ≤ ctl)
    (hbase : 1 ≤ base) (hd : d₁ ≤ deg) (hZ : 1 ≤ Z) (he : e₁ ≤ e) :
    c*dg*ctl₁^2*base^d₁*Z^e₁ ≤ C*dg*ctl^2*base^deg*Z^e := by
  have h1 : ctl₁^2 ≤ ctl^2 := pow_le_pow_left₀ hctl₁ hctl 2
  have h2 : base^d₁ ≤ base^deg := pow_le_pow_right₀ hbase hd
  have h3 : Z^e₁ ≤ Z^e := Real.rpow_le_rpow_of_exponent_le hZ he
  have hb0 : 0 ≤ base^d₁ := pow_nonneg (zero_le_one.trans hbase) _
  have hz0 : 0 ≤ Z^e₁ := Real.rpow_nonneg (zero_le_one.trans hZ) _
  have hctl0 : 0 ≤ ctl^2 := sq_nonneg _
  have hbd : 0 ≤ base^deg := pow_nonneg (zero_le_one.trans hbase) _
  have hC0 : 0 ≤ C := hc.trans hcC
  calc c*dg*ctl₁^2*base^d₁*Z^e₁ ≤ C*dg*ctl₁^2*base^d₁*Z^e₁ := by gcongr
    _ ≤ C*dg*ctl^2*base^d₁*Z^e₁ := by gcongr
    _ ≤ C*dg*ctl^2*base^deg*Z^e₁ := by gcongr
    _ ≤ C*dg*ctl^2*base^deg*Z^e := by gcongr

/-- A cost factor `cD·base^dD·Z^x` times a bound `cP·dg·ctl₁²·base^dP·Z^y` fits the combined constants. -/
theorem fit_product {cD cP C dg ctl₁ ctl base Z x y e : ℝ} {dD dP deg : ℕ}
    (hcD : 0 ≤ cD) (hcP : 0 ≤ cP) (hcC : cD*cP ≤ C) (hdg : 0 ≤ dg) (hctl₁ : 0 ≤ ctl₁)
    (hctl : ctl₁ ≤ ctl) (hbase : 1 ≤ base) (hd : dD + dP ≤ deg) (hZ : 1 ≤ Z) (he : x + y ≤ e) :
    (cD*base^dD*Z^x)*(cP*dg*ctl₁^2*base^dP*Z^y) ≤ C*dg*ctl^2*base^deg*Z^e := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hrw : (cD*base^dD*Z^x)*(cP*dg*ctl₁^2*base^dP*Z^y) =
      (cD*cP)*dg*ctl₁^2*base^(dD+dP)*Z^(x+y) := by
    rw [pow_add, Real.rpow_add hZ0]; ring
  rw [hrw]
  exact fit_bound (mul_nonneg hcD hcP) hcC hdg hctl₁ hctl hbase hd hZ he

/-- A pure power of `Z` times a bound fits the combined constants. -/
theorem fit_scaled {c C dg ctl₁ ctl base Z x y e : ℝ} {d₁ deg : ℕ}
    (hc : 0 ≤ c) (hcC : c ≤ C) (hdg : 0 ≤ dg) (hctl₁ : 0 ≤ ctl₁) (hctl : ctl₁ ≤ ctl)
    (hbase : 1 ≤ base) (hd : d₁ ≤ deg) (hZ : 1 ≤ Z) (he : x + y ≤ e) :
    Z^x * (c*dg*ctl₁^2*base^d₁*Z^y) ≤ C*dg*ctl^2*base^deg*Z^e := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hrw : Z^x * (c*dg*ctl₁^2*base^d₁*Z^y) = c*dg*ctl₁^2*base^d₁*Z^(x+y) := by
    rw [Real.rpow_add hZ0]; ring
  rw [hrw]
  exact fit_bound hc hcC hdg hctl₁ hctl hbase hd hZ he

/-- Two branch bounds with constants `C₁, C₂` add up under `C ≥ C₁ + C₂`. -/
theorem fit_add {a b C₁ C₂ C Q : ℝ} (hQ : 0 ≤ Q) (ha : a ≤ C₁*Q) (hb : b ≤ C₂*Q)
    (hC : C₁ + C₂ ≤ C) : a + b ≤ C*Q := by
  nlinarith

/-- Two branch bounds in the combined shape add up. -/
theorem fit_add2 {a b C₁ C₂ C dg ctl base Z e : ℝ} {deg : ℕ} (hdg : 0 ≤ dg) (hbase : 1 ≤ base)
    (hZ : 1 ≤ Z) (ha : a ≤ C₁*dg*ctl^2*base^deg*Z^e) (hb : b ≤ C₂*dg*ctl^2*base^deg*Z^e)
    (hC : C₁ + C₂ ≤ C) : a + b ≤ C*dg*ctl^2*base^deg*Z^e := by
  have hQ : 0 ≤ dg*ctl^2*base^deg*Z^e := by
    have := pow_nonneg (zero_le_one.trans hbase) deg
    have := Real.rpow_nonneg (zero_le_one.trans hZ) e
    positivity
  have e1 : C₁*dg*ctl^2*base^deg*Z^e = C₁*(dg*ctl^2*base^deg*Z^e) := by ring
  have e2 : C₂*dg*ctl^2*base^deg*Z^e = C₂*(dg*ctl^2*base^deg*Z^e) := by ring
  have e3 : C*dg*ctl^2*base^deg*Z^e = C*(dg*ctl^2*base^deg*Z^e) := by ring
  rw [e1] at ha; rw [e2] at hb; rw [e3]
  exact fit_add hQ ha hb hC

end
end QRH.ArviSelectedLeaf
