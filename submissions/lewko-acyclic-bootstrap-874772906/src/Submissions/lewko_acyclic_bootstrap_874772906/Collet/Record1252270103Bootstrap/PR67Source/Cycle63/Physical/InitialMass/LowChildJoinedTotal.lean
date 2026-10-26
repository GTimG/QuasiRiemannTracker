import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildJoinedArith
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The arithmetic of the sum of the joined bound of the selected low columns: the bound of one row by its old part and
its returned part, and the comparison of the exponents of the total. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- The rate `rate` and the loss `εX` of the daughters are absorbed in the rate `lowRate` of the ledger: when
`εX ≤ (lowRate - rate) (εpad Mmin)`, the padding `omega + εpad unit` is at least `εpad Mmin`. -/
theorem absorb_rate {rate lowRate εX εpad Mmin unit omega : ℝ} (hrate : rate ≤ lowRate)
    (hεX : εX ≤ (lowRate - rate) * (εpad * Mmin)) (hεpad : 0 ≤ εpad) (hMmin : Mmin ≤ unit) (hω : 0 ≤ omega) :
    εX + rate * (omega + εpad * unit) ≤ lowRate * (omega + εpad * unit) := by
  have hP : εpad * Mmin ≤ omega + εpad * unit := by
    have := mul_le_mul_of_nonneg_left hMmin hεpad
    linarith only [this, hω]
  have h1 : (lowRate - rate) * (εpad * Mmin) ≤ (lowRate - rate) * (omega + εpad * unit) :=
    mul_le_mul_of_nonneg_left hP (by linarith only [hrate])
  nlinarith only [hεX, h1]

/-- One row: the weight of the row times its bound, `cc (K (Z^Xr + Ret) Zp)`, is at most the old part
`Cc (mass Z^amp) (pay0 Z^Xf)` plus the returned part `Cc physical (Wt value)`, when `Ret = factor value`, the exponent
`Xr` is at most the old exponent `Xold` plus the allowance `Xf`, and the weight `Wt` of the returned part is the power
of `Z` of the old payment divided by the norm `E2` times `factor`. -/
theorem joined_row_bound {Z cc K Zp Xr Xold Xf Cc mass amp physical loss pay0 a E2 Ret value factor Wt : ℝ}
    (hZ : 1 < Z) (hid : cc * (K * Zp) * Z ^ Xold = Cc * (mass * Z ^ amp) * pay0) (hX : Xr ≤ Xold + Xf)
    (hnonneg : 0 ≤ cc * (K * Zp)) (hpay0 : 0 ≤ pay0) (hpay : pay0 ≤ Z ^ a / E2)
    (hmass : mass ≤ physical * Z ^ loss) (hphys : 0 ≤ physical) (hCc : 0 ≤ Cc) (hE2 : 0 < E2)
    (hRet : Ret = factor * value) (hvalue : 0 ≤ value) (hfactor : 0 ≤ factor)
    (hW : Z ^ (loss + amp + a - Xold) / E2 * factor = Wt) :
    cc * (K * (Z ^ Xr + Ret) * Zp) ≤
      Cc * (mass * Z ^ amp) * (pay0 * Z ^ Xf) + Cc * physical * (Wt * value) := by
  have hold := old_row_bound hZ.le hid hX hnonneg
  have hret := returned_row_bound hZ hid hpay0 hpay hmass hphys hCc hE2
  have hRet0 : 0 ≤ Ret := by
    rw [hRet]
    exact mul_nonneg hfactor hvalue
  calc cc * (K * (Z ^ Xr + Ret) * Zp) = cc * (K * Z ^ Xr * Zp) + cc * (K * Zp) * Ret := by ring
    _ ≤ Cc * (mass * Z ^ amp) * (pay0 * Z ^ Xf) + Cc * physical * (Z ^ (loss + amp + a - Xold) / E2) * Ret :=
        add_le_add hold (mul_le_mul_of_nonneg_right hret hRet0)
    _ = _ := by
        rw [hRet, ← hW]
        ring

/-- The power of `Z` of the old payment divided by the norm `E2`, times the power `Z^y` of the factor of the returned
part, is the power of `Z` of the total exponent, when `b2` is the logarithm of `E2` to the base `Z`. -/
theorem returned_weight_eq {Z E2 b2 x y expo : ℝ} (hZ : 1 < Z) (hE2 : 0 < E2) (hb2 : b2 = Real.logb Z E2)
    (h : x - b2 + y = expo) : Z ^ x / E2 * Z ^ y = Z ^ expo := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hE : E2 = Z ^ b2 := by rw [hb2, Real.rpow_logb hZ0 hZ.ne' hE2]
  rw [hE, ← Real.rpow_sub hZ0, ← Real.rpow_add hZ0, h]

/-- The height factor `(1 + Tz)^J` of the returned payment is at most `2^J Z^ε` when `0 ≤ Tz ≤ Z^τT` and
`J τT ≤ ε`. -/
theorem height_power_bound {Z Tz τT ε : ℝ} {J : ℕ} (hZ : 1 < Z) (hTz : 0 ≤ Tz) (hTzZ : Tz ≤ Z ^ τT)
    (hε : 0 ≤ ε) (hJ : (J : ℝ) * τT ≤ ε) : (1 + Tz) ^ J ≤ 2 ^ J * Z ^ ε := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have h1 : 1 + Tz ≤ 2 * Z ^ (max τT 0) := by
    have hz1 : 1 ≤ Z ^ (max τT 0) := Real.one_le_rpow hZ.le (le_max_right _ _)
    have hz2 : Z ^ τT ≤ Z ^ (max τT 0) := Real.rpow_le_rpow_of_exponent_le hZ.le (le_max_left _ _)
    linarith only [hTzZ, hz1, hz2]
  have hJm : max τT 0 * (J : ℝ) ≤ ε := by
    rcases le_total τT 0 with h | h
    · rw [max_eq_right h, zero_mul]
      exact hε
    · rw [max_eq_left h, mul_comm]
      exact hJ
  calc (1 + Tz) ^ J ≤ (2 * Z ^ (max τT 0)) ^ J := pow_le_pow_left₀ (by linarith only [hTz]) h1 J
    _ = 2 ^ J * Z ^ (max τT 0 * (J : ℝ)) := by
        rw [mul_pow, Real.rpow_mul hZ0.le, Real.rpow_natCast]
    _ ≤ 2 ^ J * Z ^ ε :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hJm) (by positivity)

/-- A reciprocal norm: `Z^(E - e)` is at most `Z^E / seedN` when `seedN ≤ Z^e`. -/
theorem rpow_div_ge {Z seedN E e : ℝ} (hZ : 1 < Z) (hseed : 0 < seedN) (hle : seedN ≤ Z ^ e) :
    Z ^ (E - e) ≤ Z ^ E / seedN := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  rw [le_div_iff₀ hseed]
  calc Z ^ (E - e) * seedN ≤ Z ^ (E - e) * Z ^ e :=
        mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hZ0.le _)
    _ = Z ^ E := by
        rw [← Real.rpow_add hZ0]
        congr 1
        ring

/-- The exponent of the returned part of the total is below that of the old part: the height factor, the count of the
prefixes and the exponent of the returned payment are at most `2^J Z^Etot / seedN`, where the exponent `Etot` is that of
the total bound, by the margin of the two-level ledger and the size of the first projector. -/
theorem joined_returned_exponent {Z Tz τT εlabels εA E₀ Lmax hTM loss amp p exponent error εv BN εshell pad dcard
    seedN : ℝ} {J : ℕ} (hZ : 1 < Z) (hTz : 0 ≤ Tz) (hTzZ : Tz ≤ Z ^ τT) (hεl : 0 ≤ εlabels)
    (hJτ : (J : ℝ) * τT ≤ εlabels / 6) (hseed : 0 < seedN) (hsd : Real.logb Z seedN ≤ p + exponent)
    (hE₀ : E₀ = loss + amp + εv + BN * εshell + pad + dcard)
    (hF9 : Lmax - hTM + εA ≤ (error - pad - dcard) + εlabels / 2) :
    (1 + Tz) ^ J * Z ^ εA * Z ^ (E₀ - hTM + Lmax + εlabels / 6 + εlabels / 6) ≤
      2 ^ J * (Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels) / seedN) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have h1 := height_power_bound hZ hTz hTzZ (by linarith only [hεl]) hJτ
  have hseedle : seedN ≤ Z ^ (p + exponent) :=
    calc seedN = Z ^ (Real.logb Z seedN) := (Real.rpow_logb hZ0 hZ.ne' hseed).symm
      _ ≤ Z ^ (p + exponent) := Real.rpow_le_rpow_of_exponent_le hZ.le hsd
  have h3 := rpow_div_ge (E := loss + amp + p + exponent + error + εv + BN * εshell + εlabels) (e := p + exponent)
    hZ hseed hseedle
  have h4 : Z ^ εA * Z ^ (E₀ - hTM + Lmax + εlabels / 6 + εlabels / 6) * Z ^ (εlabels / 6) ≤
      Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels - (p + exponent)) := by
    rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    rw [hE₀]
    linarith only [hF9]
  have h2J : (0 : ℝ) ≤ 2 ^ J := by positivity
  calc (1 + Tz) ^ J * Z ^ εA * Z ^ (E₀ - hTM + Lmax + εlabels / 6 + εlabels / 6) ≤
        (2 ^ J * Z ^ (εlabels / 6)) * Z ^ εA * Z ^ (E₀ - hTM + Lmax + εlabels / 6 + εlabels / 6) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hZ0.le _))
          (Real.rpow_nonneg hZ0.le _)
    _ = 2 ^ J * (Z ^ εA * Z ^ (E₀ - hTM + Lmax + εlabels / 6 + εlabels / 6) * Z ^ (εlabels / 6)) := by ring
    _ ≤ 2 ^ J * Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels - (p + exponent)) :=
        mul_le_mul_of_nonneg_left h4 h2J
    _ ≤ 2 ^ J * (Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels) / seedN) :=
        mul_le_mul_of_nonneg_left h3 h2J

/-- The total: the old part and the returned part of the sum over the rows are at most the bound of the total, with the
constant `Cg (K₀ + Cret 2^J Capre Kmax)`. -/
theorem joined_total {Z Cg K₀ Cret Capre Kmax fixed boxc physical Tz τT seedN εlabels εA E₀ Lmax hTM
    loss amp p exponent error εv BN εshell pad dcard old ret : ℝ} {J : ℕ}
    (hZ : 1 < Z) (hCg : 0 ≤ Cg) (hCret : 0 ≤ Cret) (hCapre : 0 ≤ Capre) (hKmax : 0 ≤ Kmax)
    (hfixed : 0 ≤ fixed) (hboxc : 0 ≤ boxc) (hphys : 0 ≤ physical)
    (hTz : 0 ≤ Tz) (hTzZ : Tz ≤ Z ^ τT) (hεl : 0 ≤ εlabels) (hJτ : (J : ℝ) * τT ≤ εlabels / 6)
    (hseed : 0 < seedN) (hsd : Real.logb Z seedN ≤ p + exponent)
    (hE₀ : E₀ = loss + amp + εv + BN * εshell + pad + dcard)
    (hF9 : Lmax - hTM + εA ≤ (error - pad - dcard) + εlabels / 2)
    (hold : old ≤ Cg * fixed * (physical * Z ^ (loss + amp)) *
      (boxc * (K₀ * Z ^ (p + exponent + error + εv + BN * εshell + εlabels) / seedN)))
    (hret : ret ≤ Cg * fixed * physical * (Cret * (1 + Tz) ^ J * (Capre * boxc * Z ^ εA) * Kmax *
      Z ^ (E₀ - hTM + Lmax + εlabels / 6 + εlabels / 6))) :
    old + ret ≤ Cg * (K₀ + Cret * 2 ^ J * Capre * Kmax) * fixed * boxc * physical *
      Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels) / seedN := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hd := joined_returned_exponent hZ hTz hTzZ hεl hJτ hseed hsd hE₀ hF9
  have hcoef : 0 ≤ Cg * fixed * physical * (Cret * Capre * boxc * Kmax) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCg hfixed) hphys)
      (mul_nonneg (mul_nonneg (mul_nonneg hCret hCapre) hboxc) hKmax)
  have h2 : ret ≤ Cg * fixed * physical * (Cret * Capre * boxc * Kmax) *
      (2 ^ J * (Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels) / seedN)) :=
    calc ret ≤ Cg * fixed * physical * (Cret * (1 + Tz) ^ J * (Capre * boxc * Z ^ εA) * Kmax *
          Z ^ (E₀ - hTM + Lmax + εlabels / 6 + εlabels / 6)) := hret
      _ = Cg * fixed * physical * (Cret * Capre * boxc * Kmax) *
          ((1 + Tz) ^ J * Z ^ εA * Z ^ (E₀ - hTM + Lmax + εlabels / 6 + εlabels / 6)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd hcoef
  have hpow : Z ^ (loss + amp) * Z ^ (p + exponent + error + εv + BN * εshell + εlabels) =
      Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels) := by
    rw [← Real.rpow_add hZ0]
    congr 1
    ring
  have h1 : old ≤ Cg * K₀ * fixed * boxc * physical *
      (Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels) / seedN) :=
    calc old ≤ _ := hold
      _ = Cg * K₀ * fixed * boxc * physical *
          (Z ^ (loss + amp) * Z ^ (p + exponent + error + εv + BN * εshell + εlabels) / seedN) := by ring
      _ = _ := by rw [hpow]
  calc old + ret ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- The width of the returned payment times the factor `3 + 4 B` of the norms is a sixth of `x`. -/
theorem width_mul {x B : ℝ} (hB : 0 ≤ B) : x / (6 * (3 + 4 * B)) * (3 + 4 * B) = x / 6 := by
  have h : (3 + 4 * B) ≠ 0 := ne_of_gt (by linarith only [hB])
  field_simp

/-- The factor of the constants of the bound of the columns is not negative. -/
theorem joined_fixed_nonneg {b Cs dg ctrl Hh Tt : ℝ} {N : ℕ} (hdg : 0 ≤ dg) (hH : 0 ≤ Hh) (hT : 0 ≤ Tt) :
    0 ≤ 2 * b ^ 2 * Cs ^ (4 * N) * dg * ctrl ^ 2 * Hh * Tt := by
  have hCs : 0 ≤ Cs ^ (4 * N) := by
    rw [pow_mul]
    positivity
  positivity

/-- The factor in front of the bound of the columns of one row is not negative. -/
theorem joined_const_nonneg {Cg b Cs dg ctrl Hh Nn Tt Zp : ℝ} {N : ℕ} (hCg : 0 ≤ Cg) (hdg : 0 ≤ dg) (hH : 0 ≤ Hh)
    (hN : 0 ≤ Nn) (hT : 0 ≤ Tt) (hZp : 0 ≤ Zp) :
    0 ≤ Cg * (2 * b ^ 2 * Cs ^ (4 * N)) * dg * ctrl ^ 2 * Hh * Nn * Tt * Zp := by
  have hCs : 0 ≤ Cs ^ (4 * N) := by
    rw [pow_mul]
    positivity
  positivity

/-- The identity of a row: the weight `c` of the row times the bound of its columns without the returned part and
without the power of the old exponent is the old payment `pay0` of the row times the mass and the amplifier. -/
theorem joined_identity {c mass vol Kf normal Nn Cg c2 dg ctrl Hh Tt Zx Zp Zn Za Zma pay0 : ℝ}
    (hc : c = mass / vol * Kf * normal) (hpay : pay0 = Zma * (Kf / vol) * (normal * Nn) * Zn)
    (hZ : Zx * Zp = Zn) (hZa : Za * Zma = 1) :
    c * (Cg * c2 * dg * ctrl * Hh * Nn * Tt * Zp) * Zx = Cg * (c2 * dg * ctrl * Hh * Tt) * (mass * Za) * pay0 := by
  subst hc hpay
  calc _ = (Cg * c2 * dg * ctrl * Hh * Tt) * (mass / vol * Kf * normal * Nn) * (Zx * Zp) := by ring
    _ = (Cg * c2 * dg * ctrl * Hh * Tt) * (mass / vol * Kf * normal * Nn) * (Zn * (Za * Zma)) := by
        rw [hZ, hZa, mul_one]
    _ = _ := by ring

/-- The exponent of the weight of a returned row: the exponent of the old payment of the row, divided by the norm of its
own second ideal and multiplied by the factor of the returned part, is the exponent `E₀` of the target plus the first
coordinate of the row. -/
theorem joined_exponent {loss amp a Xold b2 dcard qdel E₀ X0 nomL lowGeom errorBase common pad Mrow unit εv BN εshell
    A c d R E ω g2 t2 : ℝ}
    (ha : a = lowGeom + errorBase + (unit - Mrow) + εv + BN * εshell)
    (hXold : Xold = nomL + amp + common) (herr : errorBase = common + pad)
    (hlow : lowGeom = A - c + R + E)
    (hnom : nomL = unit - max (c - d) 0 - 6 * amp - ω - g2 + t2)
    (hE₀ : E₀ = loss + amp + εv + BN * εshell + pad + dcard)
    (hX0 : X0 = -amp + (2 * A - c - d + R + E - Mrow + max (d - c) 0 + 6 * amp + ω - (A - c)) + (g2 - t2 - b2)) :
    loss + amp + a - Xold - b2 + (dcard + qdel) = E₀ + X0 + qdel := by
  have h := max_sub_swap c d
  rw [ha, hXold, herr, hlow, hnom, hE₀, hX0]
  linarith only [h]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
