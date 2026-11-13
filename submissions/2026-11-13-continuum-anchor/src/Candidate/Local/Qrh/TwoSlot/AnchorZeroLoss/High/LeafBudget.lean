/- Modified by Joseph Bebel (2026-11-12): positive source and detector
pads for the stronger anchor target. The actual physical coefficient,
mask and height contracts are preserved. Inherited attribution follows. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.BatchMax

/-!
# High.LeafBudget

Scalar bookkeeping of one regular core batch of the HIGH leaf:
* `bin_exponent_le` — the core-scale exponent `q·X` of `High.LeafClass.core_class_batch` is at most
  `dB + highPriceFW(P, S, dB)` plus the losses (`q = dB + margin ≤ Mcap + 1`);
* `bin_constant_le` — the constants and `Z`-powers of `core_class_batch` collapse to
  `K ctl² Y^Jo Z^(2 ε₁ d (N+1) + N wmin + E)`.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High
noncomputable section
variable [shift : WitnessShift]
open scoped BigOperators

/-- The exponent of one core batch, restored to the core width `dB`. -/
theorem bin_exponent_le {a0 a1 k wlo : ℝ} (hk0 : 1/6 ≤ k) (hk1 : k ≤ 3/4)
    {q dB margin Mc P S Sb ε' ε εm ηd bw mesh a N : ℝ}
    (hq : q = dB + margin) (hdB : 0 < dB) (hmargin : 0 ≤ margin) (hqM : q ≤ Mc)
    (hSb0 : 0 ≤ Sb) (hSb : Sb ≤ S) (hSbN : Sb ≤ N)
    (hε' : 0 ≤ ε') (hε : 0 ≤ ε) (hεm : 0 ≤ εm) (hηd : 0 ≤ ηd) (hbw : 0 ≤ bw) (hmesh : 0 ≤ mesh)
    (ha0 : 0 ≤ 2*a-1) (ha : 2*a-1 ≤ 1) :
    q * (1 + max 0 (detPriceW a0 a1 k wlo (P/q) (Sb/q) 1) + ε' +
        (154*ε + (2*a-1)*(mesh/q) + εm + 2*bw*(Sb/q)) + ηd) ≤
      dB + highPriceFW a0 a1 k wlo P S dB +
        (margin + Mc*(ε' + 154*ε + εm + ηd) + mesh + 2*bw*N) := by
  have hq0 : 0 < q := by rw [hq]; linarith
  have h1 := scaled_maxDetW_le (a0 := a0) (a1 := a1) (wlo := wlo) (P := P) (S := Sb)
    (show (0:ℝ) ≤ k by linarith) hk1 hq0
  have h2 := highPriceFW_antitoneM (a0 := a0) (a1 := a1) (wlo := wlo) hk0 hk1 P Sb
    (show dB ≤ q by rw [hq]; linarith)
  have h3 := highPriceFW_mono (a0 := a0) (a1 := a1) (wlo := wlo) (show (0:ℝ) ≤ k by linarith) hk1
    dB (le_refl P) hSb
  have e1 : q * ((2*a-1)*(mesh/q)) = (2*a-1)*mesh := by field_simp
  have e2 : q * (2*bw*(Sb/q)) = 2*bw*Sb := by field_simp
  have h4 : (2*a-1)*mesh ≤ mesh := by nlinarith
  have h5 : 2*bw*Sb ≤ 2*bw*N := by nlinarith
  have h6 : q * (ε' + 154*ε + εm + ηd) ≤ Mc * (ε' + 154*ε + εm + ηd) :=
    mul_le_mul_of_nonneg_right hqM (by positivity)
  have hexp : q * (1 + max 0 (detPriceW a0 a1 k wlo (P/q) (Sb/q) 1) + ε' +
        (154*ε + (2*a-1)*(mesh/q) + εm + 2*bw*(Sb/q)) + ηd) =
      q + q * max 0 (detPriceW a0 a1 k wlo (P/q) (Sb/q) 1) + q * (ε' + 154*ε + εm + ηd) +
        q * ((2*a-1)*(mesh/q)) + q * (2*bw*(Sb/q)) := by ring
  rw [hexp, e1, e2]
  linarith

/-- The constants of one core batch. -/
theorem bin_constant_le {Z Kr ctl2 Cs Cc Kc HD Ch Y ε₁ d wmin q X0 E : ℝ} {n₁ n₂ N J Jo : ℕ}
    (hZ : 1 < Z) (hKr : 0 ≤ Kr) (hctl : 0 ≤ ctl2) (hCs : 1 ≤ Cs) (hCc : 1 ≤ Cc) (hKc : 0 ≤ Kc)
    (hHD : 1 ≤ HD) (hHDY : HD ≤ Ch * Y) (hJ : J + 1 ≤ Jo) (hn : n₁ + n₂ ≤ N)
    (hε₁ : 0 ≤ ε₁) (hd : 0 ≤ d) (hwmin : 0 ≤ wmin) (hX : q * X0 ≤ E) :
    (Kr * ctl2 * Z^(2*ε₁*d)) * (Cs * Z^(2*ε₁*d) * Z^wmin)^n₁ * 4^n₂ *
        (((Cc * Z^(ε₁*d))^2)^n₂ * (Kc * HD^(J+1)) * (Z^q)^X0) ≤
      (Kr * (4*Cs*Cc^2)^N * Kc * Ch^Jo) * ctl2 * Y^Jo *
        Z^(2*ε₁*d*((N:ℝ)+1) + (N:ℝ)*wmin + E) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  rw [← Real.rpow_mul hZ0.le q X0]
  set X : ℝ := q * X0 with hXdef
  have hCs0 : 0 ≤ Cs := zero_le_one.trans hCs
  have hCc0 : 0 ≤ Cc := zero_le_one.trans hCc
  have hn₁ : n₁ ≤ N := by omega
  have hn₂ : n₂ ≤ N := by omega
  have hY : 0 ≤ Ch * Y := zero_le_one.trans (hHD.trans hHDY)
  -- the `Z` powers
  have z1 : (Cs * Z^(2*ε₁*d) * Z^wmin)^n₁ = Cs^n₁ * Z^((2*ε₁*d + wmin)*n₁) := by
    rw [mul_assoc, mul_pow, ← Real.rpow_add hZ0, ← Real.rpow_natCast (Z^(2*ε₁*d + wmin)) n₁,
      ← Real.rpow_mul hZ0.le]
  have z2 : ((Cc * Z^(ε₁*d))^2)^n₂ = (Cc^2)^n₂ * Z^(2*ε₁*d*n₂) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (Z^(ε₁*d)) 2, ← Real.rpow_mul hZ0.le,
      ← Real.rpow_natCast (Z^(ε₁*d*((2:ℕ):ℝ))) n₂, ← Real.rpow_mul hZ0.le]
    congr 1
    congr 1
    push_cast
    ring
  rw [z1, z2]
  -- the constants
  have c1 : 4^n₂ * Cs^n₁ * (Cc^2)^n₂ ≤ (4*Cs*Cc^2)^N := by
    rw [mul_pow, mul_pow]
    have h4 : (4:ℝ)^n₂ ≤ 4^N := pow_le_pow_right₀ (by norm_num) hn₂
    have hC : Cs^n₁ ≤ Cs^N := pow_le_pow_right₀ hCs hn₁
    have hC2 : (Cc^2)^n₂ ≤ (Cc^2)^N := pow_le_pow_right₀ (one_le_pow₀ hCc) hn₂
    calc (4:ℝ)^n₂ * Cs^n₁ * (Cc^2)^n₂ ≤ 4^N * Cs^N * (Cc^2)^N := by gcongr
      _ = _ := by ring
  have c2 : HD^(J+1) ≤ Ch^Jo * Y^Jo := by
    rw [← mul_pow]
    exact (pow_le_pow_right₀ hHD hJ).trans (pow_le_pow_left₀ (zero_le_one.trans hHD) hHDY _)
  have zexp : Z^(2*ε₁*d) * Z^((2*ε₁*d + wmin)*n₁) * Z^(2*ε₁*d*n₂) * Z^X ≤
      Z^(2*ε₁*d*((N:ℝ)+1) + (N:ℝ)*wmin + E) := by
    rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    have hN1 : (n₁ : ℝ) + n₂ ≤ N := by exact_mod_cast hn
    have hN1' : (n₁ : ℝ) ≤ N := by exact_mod_cast hn₁
    have hed : 0 ≤ 2*ε₁*d := by positivity
    nlinarith
  have hz0 : 0 ≤ Z^(2*ε₁*d) * Z^((2*ε₁*d + wmin)*n₁) * Z^(2*ε₁*d*n₂) * Z^X := by positivity
  calc (Kr * ctl2 * Z^(2*ε₁*d)) * (Cs^n₁ * Z^((2*ε₁*d + wmin)*n₁)) * 4^n₂ *
        ((Cc^2)^n₂ * Z^(2*ε₁*d*n₂) * (Kc * HD^(J+1)) * Z^X)
      = (Kr * Kc * ctl2) * (4^n₂ * Cs^n₁ * (Cc^2)^n₂) * HD^(J+1) *
          (Z^(2*ε₁*d) * Z^((2*ε₁*d + wmin)*n₁) * Z^(2*ε₁*d*n₂) * Z^X) := by ring
    _ ≤ (Kr * Kc * ctl2) * (4*Cs*Cc^2)^N * (Ch^Jo * Y^Jo) *
          Z^(2*ε₁*d*((N:ℝ)+1) + (N:ℝ)*wmin + E) := by
        have hK0 : 0 ≤ Kr * Kc * ctl2 := by positivity
        have hCY : 0 ≤ Ch^Jo * Y^Jo := by rw [← mul_pow]; exact pow_nonneg hY _
        have hc1 : 0 ≤ 4^n₂ * Cs^n₁ * (Cc^2)^n₂ := by positivity
        have hHD0 : 0 ≤ HD^(J+1) := pow_nonneg (zero_le_one.trans hHD) _
        have hC0 : 0 ≤ (4*Cs*Cc^2)^N := by positivity
        exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left c1 hK0) c2 hHD0
          (mul_nonneg hK0 hC0)) zexp hz0 (mul_nonneg (mul_nonneg hK0 hC0) hCY)
    _ = _ := by ring

end
end Qrh.TwoSlot.AnchorZeroLoss.High
