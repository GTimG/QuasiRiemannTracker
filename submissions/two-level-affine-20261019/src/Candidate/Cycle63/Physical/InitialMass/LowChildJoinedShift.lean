/- The total of the old and of the returned parts of the selected low columns when the first coordinate of the returned
rows is shifted by the side bound of the labels without their first projector: the returned part carries the factor
`Z^(p + exponent - log N(seed₀))`, which is the old exponent divided by the norm of the first projector. Released under
Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.LowChildJoinedTotal

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- The exponent of the returned part of the total is below that of the old part: the height factor, the count of the
prefixes and the exponent of the returned payment, whose target exponent `E₀' = E₀ + (p + exponent - log N(seed₀))`
is shifted by the side bound of the labels, are at most `2^J Z^Etot / seedN`, by the margin of the two-level ledger. -/
theorem joined_returned_exponent_shift {Z Tz τT εlabels εA E₀ E₀' Lmax hTM loss amp p exponent error εv BN εshell pad
    dcard seedN : ℝ} {J : ℕ} (hZ : 1 < Z) (hTz : 0 ≤ Tz) (hTzZ : Tz ≤ Z ^ τT) (hεl : 0 ≤ εlabels)
    (hJτ : (J : ℝ) * τT ≤ εlabels / 6) (hseed : 0 < seedN)
    (hE₀ : E₀ = loss + amp + εv + BN * εshell + pad + dcard)
    (hE₀' : E₀' = E₀ + (p + exponent - Real.logb Z seedN))
    (hF9 : Lmax - hTM + εA ≤ (error - pad - dcard) + εlabels / 2) :
    (1 + Tz) ^ J * Z ^ εA * Z ^ (E₀' - hTM + Lmax + εlabels / 6 + εlabels / 6) ≤
      2 ^ J * (Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels) / seedN) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have h1 := height_power_bound hZ hTz hTzZ (by linarith only [hεl]) hJτ
  have hlog : Z ^ (Real.logb Z seedN) = seedN := Real.rpow_logb hZ0 hZ.ne' hseed
  have h3 := rpow_div_ge (E := loss + amp + p + exponent + error + εv + BN * εshell + εlabels)
    (e := Real.logb Z seedN) hZ hseed hlog.ge
  have h4 : Z ^ εA * Z ^ (E₀' - hTM + Lmax + εlabels / 6 + εlabels / 6) * Z ^ (εlabels / 6) ≤
      Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels - Real.logb Z seedN) := by
    rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    rw [hE₀', hE₀]
    linarith only [hF9]
  have h2J : (0 : ℝ) ≤ 2 ^ J := by positivity
  calc (1 + Tz) ^ J * Z ^ εA * Z ^ (E₀' - hTM + Lmax + εlabels / 6 + εlabels / 6) ≤
        (2 ^ J * Z ^ (εlabels / 6)) * Z ^ εA * Z ^ (E₀' - hTM + Lmax + εlabels / 6 + εlabels / 6) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hZ0.le _))
          (Real.rpow_nonneg hZ0.le _)
    _ = 2 ^ J * (Z ^ εA * Z ^ (E₀' - hTM + Lmax + εlabels / 6 + εlabels / 6) * Z ^ (εlabels / 6)) := by ring
    _ ≤ 2 ^ J * Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels - Real.logb Z seedN) :=
        mul_le_mul_of_nonneg_left h4 h2J
    _ ≤ 2 ^ J * (Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels) / seedN) :=
        mul_le_mul_of_nonneg_left h3 h2J

/-- The total: the old part and the returned part of the sum over the rows are at most the bound of the total, with the
constant `Cg (K₀ + Cret 2^J Capre Kmax)`, when the target exponent of the returned part is shifted by the side bound
of the labels. -/
theorem joined_total_shift {Z Cg K₀ Cret Capre Kmax fixed boxc physical Tz τT seedN εlabels εA E₀ E₀' Lmax hTM
    loss amp p exponent error εv BN εshell pad dcard old ret : ℝ} {J : ℕ}
    (hZ : 1 < Z) (hCg : 0 ≤ Cg) (hCret : 0 ≤ Cret) (hCapre : 0 ≤ Capre) (hKmax : 0 ≤ Kmax)
    (hfixed : 0 ≤ fixed) (hboxc : 0 ≤ boxc) (hphys : 0 ≤ physical)
    (hTz : 0 ≤ Tz) (hTzZ : Tz ≤ Z ^ τT) (hεl : 0 ≤ εlabels) (hJτ : (J : ℝ) * τT ≤ εlabels / 6)
    (hseed : 0 < seedN)
    (hE₀ : E₀ = loss + amp + εv + BN * εshell + pad + dcard)
    (hE₀' : E₀' = E₀ + (p + exponent - Real.logb Z seedN))
    (hF9 : Lmax - hTM + εA ≤ (error - pad - dcard) + εlabels / 2)
    (hold : old ≤ Cg * fixed * (physical * Z ^ (loss + amp)) *
      (boxc * (K₀ * Z ^ (p + exponent + error + εv + BN * εshell + εlabels) / seedN)))
    (hret : ret ≤ Cg * fixed * physical * (Cret * (1 + Tz) ^ J * (Capre * boxc * Z ^ εA) * Kmax *
      Z ^ (E₀' - hTM + Lmax + εlabels / 6 + εlabels / 6))) :
    old + ret ≤ Cg * (K₀ + Cret * 2 ^ J * Capre * Kmax) * fixed * boxc * physical *
      Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels) / seedN := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hd := joined_returned_exponent_shift hZ hTz hTzZ hεl hJτ hseed hE₀ hE₀' hF9
  have hcoef : 0 ≤ Cg * fixed * physical * (Cret * Capre * boxc * Kmax) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCg hfixed) hphys)
      (mul_nonneg (mul_nonneg (mul_nonneg hCret hCapre) hboxc) hKmax)
  have h2 : ret ≤ Cg * fixed * physical * (Cret * Capre * boxc * Kmax) *
      (2 ^ J * (Z ^ (loss + amp + p + exponent + error + εv + BN * εshell + εlabels) / seedN)) :=
    calc ret ≤ Cg * fixed * physical * (Cret * (1 + Tz) ^ J * (Capre * boxc * Z ^ εA) * Kmax *
          Z ^ (E₀' - hTM + Lmax + εlabels / 6 + εlabels / 6)) := hret
      _ = Cg * fixed * physical * (Cret * Capre * boxc * Kmax) *
          ((1 + Tz) ^ J * Z ^ εA * Z ^ (E₀' - hTM + Lmax + εlabels / 6 + εlabels / 6)) := by ring
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

end
end OAI.SevenEighths.Cycle63InitialMass
