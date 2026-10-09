import QRH.Detector.LowReflectedLength
import OAI.NumberTheory.DirichletL.Detector.LowCentralTuple

namespace OAI.SevenEighths.ProbePhysical
noncomputable section

lemma low_penalty_le_length (d : ℝ) (hd : 0 ≤ d) : QRH.lowPenalty d ≤ d := by
  have hell : QRH.ell ≤ (1/5:ℝ) := by norm_num [QRH.ell, QRH.theta]
  have hm : max (5*QRH.ell+d-1) 0 ≤ d := max_le (by linarith) hd
  dsimp [QRH.lowPenalty]
  linarith

/-- Absorb the reflected square-root loss in the original Gram factor,
using the lower norm of the actual unselected product. -/
lemma low_penalty_gram_absorption (q c Z L d : ℝ)
    (hq : 0 ≤ q) (hc : 0 < c) (hZ : 1 ≤ Z) (hL : 0 < L)
    (hd : 0 ≤ d) (hlower : c * Z^d ≤ L) :
    Real.sqrt (3*q/L) * Z^(QRH.lowPenalty d/2) ≤ Real.sqrt (3*q/c) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hp : Z^(QRH.lowPenalty d) ≤ L/c :=
    (Real.rpow_le_rpow_of_exponent_le hZ (low_penalty_le_length d hd)).trans
      ((le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlower))
  have he : Z^(QRH.lowPenalty d/2) = Real.sqrt (Z^(QRH.lowPenalty d)) := by
    rw [Real.sqrt_eq_rpow, ←Real.rpow_mul hz.le]
    congr 1
    ring
  rw [he, ←Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ (3*q/L)*(L/c) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by field_simp

end
end OAI.SevenEighths.ProbePhysical
