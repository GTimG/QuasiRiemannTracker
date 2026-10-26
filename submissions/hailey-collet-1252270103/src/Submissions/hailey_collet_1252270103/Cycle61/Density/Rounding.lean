import Submissions.hailey_collet_1252270103.LocalMoment.UnmarkedDensity

set_option autoImplicit false
namespace OAI.SevenEighths.LocalMoment

theorem unmarkedDensity_rounding {a b e : ℝ}
    (ha : a ≤ 7/8) (hb : b ≤ 7/8) (he : 0 ≤ e) (hab : a-e ≤ b) :
    unmarkedDensity (2*b-1) ≤ unmarkedDensity (2*a-1) + 3*e := by
  let A : ℝ := 5-2*(2*a-1)
  let B : ℝ := 5-2*(2*b-1)
  have hA : 7/2 ≤ A := by dsimp [A]; linarith
  have hB : 7/2 ≤ B := by dsimp [B]; linarith
  have hAp : 0 < A := by linarith
  have hBp : 0 < B := by linarith
  have hprod : 49/4 ≤ A*B := by nlinarith
  have hid : unmarkedDensity (2*b-1) - unmarkedDensity (2*a-1) =
      100*(a-b)/(3*A*B) := by
    change (1-10*(2*b-1)/(3*B))-(1-10*(2*a-1)/(3*A)) = _
    field_simp [hAp.ne', hBp.ne']
    dsimp [A, B]
    ring
  have hh : unmarkedDensity (2*b-1)-unmarkedDensity (2*a-1) ≤ 3*e := by
    rw [hid]
    apply (div_le_iff₀ (by positivity : 0 < 3*A*B)).mpr
    nlinarith
  linarith

theorem unmarkedDensity_le_one {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4) :
    unmarkedDensity δ ≤ 1 := by
  unfold unmarkedDensity
  have hden : 0 < 3*(5-2*δ) := by linarith
  have hq : 0 ≤ 10*δ/(3*(5-2*δ)) := div_nonneg (by linarith) hden.le
  linarith

theorem witness_height_power (U τ : ℝ) (I J : ℕ) (hU : 1 ≤ U) (hτ : 0 ≤ τ) :
    (1 + (2*Real.pi*U^(τ/2) + (3*I : ℕ)*U^τ))^J ≤
      (1+2*Real.pi+(3*I : ℕ))^J * U^((J : ℝ)*τ) := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hp := Real.one_le_rpow hU hτ
  have hm := Real.rpow_le_rpow_of_exponent_le hU (show τ/2 ≤ τ by linarith)
  have hbase : 1 + (2*Real.pi*U^(τ/2) + (3*I : ℕ)*U^τ) ≤
      (1+2*Real.pi+(3*I : ℕ))*U^τ := by
    nlinarith [Real.pi_pos]
  calc
    _ ≤ ((1+2*Real.pi+(3*I : ℕ))*U^τ)^J :=
      pow_le_pow_left₀ (by positivity) hbase J
    _ = _ := by
      rw [mul_pow, ← Real.rpow_natCast (U^τ) J, ← Real.rpow_mul hUp.le]
      congr 2
      ring

#print axioms unmarkedDensity_rounding
end OAI.SevenEighths.LocalMoment
