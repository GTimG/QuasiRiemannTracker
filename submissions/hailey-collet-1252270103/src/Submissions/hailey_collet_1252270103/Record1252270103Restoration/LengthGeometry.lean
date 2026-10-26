/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.FullEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CenteredMomentEnergyBands
open QRH.Record12518109Source QRH.Record1252270103Source

theorem length_mono_raw {Z X Y : ℝ} (hZ : 1<Z) (hYX : Y≤X) : length Z Y≤length Z X := by
  apply Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  exact max_le_max le_rfl hYX

theorem raw_product_le_pow {Z X₁ X₂ B : ℝ} (hZ : 1<Z)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hlen : length Z X₁+length Z X₂≤B) : X₁*X₂≤Z^B := by
  have hz := zero_lt_one.trans hZ
  calc
    X₁*X₂ ≤ max 1 X₁*max 1 X₂ := mul_le_mul (le_max_right _ _) (le_max_right _ _) hX₂.le
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).le
    _ = Z^(length Z X₁+length Z X₂) := by
      rw [Real.rpow_add hz]
      unfold length
      rw [Real.rpow_logb hz hZ.ne' (lt_of_lt_of_le zero_lt_one (le_max_left _ _)),
        Real.rpow_logb hz hZ.ne' (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
    _ ≤ Z^B := Real.rpow_le_rpow_of_exponent_le hZ.le hlen

theorem global_raw_product_bound {Z X₁ X₂ B lam cap s : ℝ}
    (hZ : 1<Z) (hZ₆ : 6≤Z) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hlam : 0≤lam) (hs : 0≤s)
    (hface : (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) s 1) :
    (9/4:ℝ)^2*X₁*X₂≤Z^(B+1) := by
  have hlen := ((globalFace_admissible_iff (length_nonneg Z X₁ hZ)
    (length_nonneg Z X₂ hZ) hs hlam).mp hface).2
  have hprod := raw_product_le_pow hZ hX₁ hX₂ (show length Z X₁+length Z X₂≤B by
    nlinarith [mul_nonneg hlam hs])
  calc
    (9/4:ℝ)^2*X₁*X₂ = (9/4:ℝ)^2*(X₁*X₂) := by ring
    _ ≤ Z*(Z^B) := mul_le_mul (by linarith) hprod (mul_pos hX₁ hX₂).le (by linarith)
    _ = Z^(B+1) := by rw [Real.rpow_add (zero_lt_one.trans hZ),Real.rpow_one];ring

end
end QRH.Record1252270103Restoration
