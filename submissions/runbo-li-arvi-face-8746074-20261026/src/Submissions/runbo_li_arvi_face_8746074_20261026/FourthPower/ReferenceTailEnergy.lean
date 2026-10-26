/- Copyright (c) 2026 Sil. Apache-2.0.
Pay an arbitrarily small pointwise reflection error in the actual physical
row norm, including all remaining factor lengths and amplitudes.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.ReferenceCrudeFactors

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceTailEnergy
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
local notation "O" => HeckeFamily.O

theorem powered_error_energy (rows : Finset O) (e P : rows → ℂ)
    (Z R ε L C κ H A : ℝ) (n : ℕ)
    (hZ : 1 ≤ Z) (hR : 0 ≤ R) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hr : ∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R)
    (he : ∀ i, ‖e i‖ ≤ C*(1+H)^n*Z^(-(L+1)))
    (hp : ∀ i, ‖P i‖ ≤ κ*Z^L*A) :
    (∑ i : rows, ‖e i*P i‖^2) ≤ 128*(C*κ)^2*(1+H)^(2*n)*Z^(R+ε)*A^2 := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hh := ReferenceCrudeFactors.error_energy rows e P (Z^R)
    (C*(1+H)^n*Z^(-(L+1))) (κ*Z^L*A)
    (Real.one_le_rpow hZ hR) (by positivity) (by positivity) hr he hp
  have hpow : Z^R*(Z^(-(L+1))*Z^L)^2 ≤ Z^(R+ε) := by
    rw [← Real.rpow_add hz]
    rw [← Real.rpow_natCast (Z^(-(L+1)+L)) 2,← Real.rpow_mul hz.le,← Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  apply hh.trans
  calc
    _ = (128*(C*κ)^2*(1+H)^(2*n)*A^2)*(Z^R*(Z^(-(L+1))*Z^L)^2) := by
      rw [show 2*n = n*2 by omega,pow_mul]
      ring
    _ ≤ (128*(C*κ)^2*(1+H)^(2*n)*A^2)*Z^(R+ε) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

theorem split_energy {ι : Type*} [Fintype ι] (f g : ι → ℂ) :
    (∑ i, ‖f i+g i‖^2) ≤ 2*(∑ i, ‖f i‖^2)+2*(∑ i, ‖g i‖^2) := by
  calc
    _ ≤ ∑ i, (2*‖f i‖^2+2*‖g i‖^2) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := norm_add_le (f i) (g i)
      have h0 := norm_nonneg (f i+g i)
      have h1 := norm_nonneg (f i)
      have h2 := norm_nonneg (g i)
      nlinarith [sq_nonneg (‖f i‖-‖g i‖)]
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]

end
end Candidate.FourthPower.ReferenceTailEnergy
