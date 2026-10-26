/- The arithmetic of the joined bound of the selected low columns: the old part and the returned part of a row are
bounded by the same payment, and the exponent of the returned part is read from the coordinates of the row. Released
under Apache 2.0. -/
import Mathlib

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- The old part of a row: the weight of the row times the power of `Z` of its bound is at most the payment of the
row, when the exponent is at most the old exponent plus the allowance. -/
theorem old_row_bound {Z cc FF Zp Xold Xr Xf Cc mass amp pay : ℝ} (hZ : 1 ≤ Z)
    (hid : cc * (FF * Zp) * Z ^ Xold = Cc * (mass * Z ^ amp) * pay) (hX : Xr ≤ Xold + Xf)
    (hnonneg : 0 ≤ cc * (FF * Zp)) :
    cc * (FF * Z ^ Xr * Zp) ≤ Cc * (mass * Z ^ amp) * (pay * Z ^ Xf) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have h1 : Z ^ Xr ≤ Z ^ Xold * Z ^ Xf := by
    rw [← Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ hX
  calc cc * (FF * Z ^ Xr * Zp) = cc * (FF * Zp) * Z ^ Xr := by ring
    _ ≤ cc * (FF * Zp) * (Z ^ Xold * Z ^ Xf) := mul_le_mul_of_nonneg_left h1 hnonneg
    _ = cc * (FF * Zp) * Z ^ Xold * Z ^ Xf := by ring
    _ = Cc * (mass * Z ^ amp) * (pay * Z ^ Xf) := by rw [hid]; ring

/-- The weight of a row without its returned factor is bounded by the pointwise payment of the row, divided by the
power of `Z` of the old bound. -/
theorem returned_row_bound {Z cc FF Zp Xold Cc mass amp physical loss pay a E2 : ℝ} (hZ : 1 < Z)
    (hid : cc * (FF * Zp) * Z ^ Xold = Cc * (mass * Z ^ amp) * pay) (hpay0 : 0 ≤ pay)
    (hpay : pay ≤ Z ^ a / E2) (hmass : mass ≤ physical * Z ^ loss) (hphysical : 0 ≤ physical)
    (hCc : 0 ≤ Cc) (hE2 : 0 < E2) :
    cc * (FF * Zp) ≤ Cc * physical * (Z ^ (loss + amp + a - Xold) / E2) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hP : 0 < Z ^ Xold := Real.rpow_pos_of_pos hZ0 _
  have hza : 0 ≤ Z ^ amp := Real.rpow_nonneg hZ0.le _
  have hzl : 0 ≤ Z ^ loss := Real.rpow_nonneg hZ0.le _
  have hmass' : mass * Z ^ amp ≤ physical * Z ^ loss * Z ^ amp := mul_le_mul_of_nonneg_right hmass hza
  have hzE : 0 ≤ Z ^ a / E2 := div_nonneg (Real.rpow_nonneg hZ0.le _) hE2.le
  have h2 : (mass * Z ^ amp) * pay ≤ (physical * Z ^ loss * Z ^ amp) * (Z ^ a / E2) :=
    mul_le_mul hmass' hpay hpay0 (mul_nonneg (mul_nonneg hphysical hzl) hza)
  have h3 : cc * (FF * Zp) * Z ^ Xold ≤ Cc * physical * (Z ^ (loss + amp + a) / E2) := by
    rw [hid]
    calc Cc * (mass * Z ^ amp) * pay = Cc * ((mass * Z ^ amp) * pay) := by ring
      _ ≤ Cc * ((physical * Z ^ loss * Z ^ amp) * (Z ^ a / E2)) := mul_le_mul_of_nonneg_left h2 hCc
      _ = Cc * physical * (Z ^ (loss + amp + a) / E2) := by
          rw [Real.rpow_add hZ0, Real.rpow_add hZ0]
          ring
  have h4 : Z ^ (loss + amp + a - Xold) * Z ^ Xold = Z ^ (loss + amp + a) := by
    rw [← Real.rpow_add hZ0]
    congr 1
    ring
  rw [← mul_le_mul_iff_of_pos_right hP]
  calc cc * (FF * Zp) * Z ^ Xold ≤ Cc * physical * (Z ^ (loss + amp + a) / E2) := h3
    _ = Cc * physical * (Z ^ (loss + amp + a - Xold) / E2) * Z ^ Xold := by
        rw [← h4]
        ring

/-- The two forms of the term `max (c - d) 0 - c`. -/
theorem max_sub_swap (c d : ℝ) : max (c - d) 0 - c = max (d - c) 0 - d := by
  rcases le_total c d with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    ring

/-- The exponent of the weight of a returned row: the exponent read from the old payment of the row is the exponent
`E₀` of the target plus the first coordinate of the row. -/
theorem returned_exponent_identity (loss A c d R E M unit omega a g2 t2 b2 pad εv BN εshell dcard q target mesh : ℝ) :
    loss + (A - c + R + E) - (unit - (max (c - d) 0 + g2 - t2) - 6 * a - omega) + pad + (unit - M) + εv +
        BN * εshell - b2 + dcard + q * (target + mesh) =
      (loss + a + εv + BN * εshell + pad + dcard) +
        (-a + (2 * A - c - d + R + E - M + max (d - c) 0 + 6 * a + omega - (A - c)) + (g2 - t2 - b2)) +
        q * (target + mesh) := by
  have h := max_sub_swap c d
  linarith only [h]

end
end OAI.SevenEighths.Cycle63InitialMass
