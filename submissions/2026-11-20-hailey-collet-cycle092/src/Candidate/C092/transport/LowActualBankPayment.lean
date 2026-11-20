/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Payment for the actual finite lower-radius source bank. -/
import Candidate.C092.transport.LowActualRadialEnergy

set_option autoImplicit false
namespace QRH.Cycle092.LowActual
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source

/-- The actual finite-bank collar, width decrement and whole-slot rounding
fit the positive P.2 reserve with its full original radial allowance. -/
theorem lower_bank_paid {n y e r V decrement mesh : ℝ}
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY)
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper : ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho : ℚ))
    (hr : 0 < r) (hrV : r ≤ V) (hVH : V ≤ (H : ℝ))
    (hwidth : 0 ≤ radiusWidth n y r) (hd : 0 ≤ decrement) (hm : 0 ≤ mesh)
    (hfee : e*((3/4 : ℝ)*(V-r)+V*decrement+mesh) ≤ (rho : ℝ)/2) :
    e*max 0 (sourceWidth n y-(u : ℝ)-V*(radiusWidth n y r-decrement)+mesh) <
      (u : ℝ)-(rho : ℝ)/2+(5/6)*max 0 ((H : ℝ)-V) := by
  have hV : 0 < V := hr.trans_le hrV
  have hbase := checked_low_lower_radius hy0 hy1 he0 he1 hV hVH hp
  have hcap := bank_capacity_loss (decrement := decrement) hy0 hr hrV hVH hwidth
  have hδ : 0 ≤ (3/4 : ℝ)*(V-r)+V*decrement+mesh := by
    have hVr : 0 ≤ V-r := sub_nonneg.mpr hrV
    positivity
  have hid : sourceWidth n y-(u : ℝ)-V*radiusWidth n y V =
      (1-V)/2-(u : ℝ)+sourceGain y-V*continuedGain (y/V) := by
    rw [radiusWidth_identity hV]
    unfold sourceWidth
    ring
  have hmcap : max 0 (sourceWidth n y-(u : ℝ)-V*(radiusWidth n y r-decrement)+mesh) ≤
      max 0 (sourceWidth n y-(u : ℝ)-V*radiusWidth n y V)+
        ((3/4 : ℝ)*(V-r)+V*decrement+mesh) := by
    apply max_le
    · linarith [le_max_left 0 (sourceWidth n y-(u : ℝ)-V*radiusWidth n y V)]
    · linarith [le_max_right 0 (sourceWidth n y-(u : ℝ)-V*radiusWidth n y V)]
  have hpbound := mul_le_mul_of_nonneg_left hmcap he0
  rw [hid] at hpbound
  unfold lowRadialPrice radialAllowance at hbase
  push_cast at hbase
  nlinarith

/-- One explicit positive collar pays every choice of bank point, actual
radius and inward decrement satisfying these original geometric bounds. -/
theorem lower_bank_fee {e δ r V decrement mesh : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper : ℝ))
    (hδ : 0 ≤ δ) (_hrV : 0 ≤ V-r) (hnet : V-r ≤ δ)
    (hV : V ≤ 1) (hd0 : 0 ≤ decrement) (hd : decrement ≤ δ)
    (_hm0 : 0 ≤ mesh) (hm : mesh ≤ δ)
    (hbudget : 3*(responseUpper : ℝ)*δ ≤ (rho : ℝ)/2) :
    e*((3/4 : ℝ)*(V-r)+V*decrement+mesh) ≤ (rho : ℝ)/2 := by
  have hVd := mul_le_mul_of_nonneg_right hV hd0
  have hinner : (3/4 : ℝ)*(V-r)+V*decrement+mesh ≤ 3*δ := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hinner he0
  have h₂ := mul_le_mul_of_nonneg_right he1 (show 0 ≤ 3*δ by positivity)
  nlinarith

end
end QRH.Cycle092.LowActual
