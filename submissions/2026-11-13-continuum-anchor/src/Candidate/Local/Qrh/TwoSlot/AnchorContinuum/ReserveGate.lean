/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.StructuralGates

/-! The long-branch reserve is an exact multiple of the differential reserve.
The source-pad debit is retained and bounded at every positive tolerance. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum
noncomputable section
open Set Qrh.TwoSlot.AnchorZeroLoss.High

def stageDatum (R z v k H q : ℝ) : Stg where
  R := R
  z := z
  k := k
  a0 := z-R*v-q/5
  a1 := -v
  H := H

def baseReserve (R z k : ℝ) : ℝ := 5/6-5*R/4+k*(R-1/2-z)

theorem base_reserve_identity {R z v k gamma : ℝ} (hR : 2/3 < R)
    (hcut : k*(2+6*(z-R*v+R*gamma)) = 1) :
    baseReserve R z k = k*R*(15*R-10)/2*(v-gamma-Curve.flow R z) := by
  have hR0 : R ≠ 0 := ne_of_gt (by linarith)
  have h15 : 15*R-10 ≠ 0 := ne_of_gt (by linarith)
  have hn15 : -10+R*15 ≠ 0 := by linarith
  have heq : baseReserve R z k =
      k*R*(15*R-10)/2*(v-gamma-Curve.flow R z) +
      (5/6-5*R/4)*(1-k*(2+6*(z-R*v+R*gamma))) := by
    unfold baseReserve Curve.flow
    rw [Curve.A_eq hR]
    unfold Curve.b
    ring_nf
    field_simp [hR0,h15,hn15]
    <;> ring
  simpa only [hcut,sub_self,mul_zero,add_zero] using heq

theorem source_pad_debit {R z v k H q : ℝ} (hv : -4/45 ≤ v)
    (hk : 0 ≤ k) (hq : 0 ≤ q) :
    baseReserve R z k-q ≤ (stageDatum R z v k H q).F0 := by
  have hd : 0 < 1/2+v := by linarith
  have hn2 : 1+v*2 ≠ 0 := by linarith
  have hwb : (stageDatum R z v k H q).wb = R+q/(5*(1/2+v)) := by
    unfold Stg.wb Stg.D stageDatum
    dsimp
    ring_nf
    field_simp [hn2]
    <;> ring
  have heq : (stageDatum R z v k H q).F0 = baseReserve R z k-
      (5/4-3*k/2)*q/(5*(1/2+v)) := by
    unfold Stg.F0
    rw [hwb]
    dsimp [stageDatum,baseReserve]
    ring
  have hdebit : (5/4-3*k/2)*q/(5*(1/2+v)) ≤ q := by
    rw [div_le_iff₀ (by positivity : 0 < 5*(1/2+v))]
    have hm := mul_le_mul_of_nonneg_right (by linarith : 5/4-3*k/2 ≤ 5*(1/2+v)) hq
    nlinarith only [hm]
  rw [heq]
  linarith

/-- One explicit tolerance bound pays the actual HIGH reserve uniformly. -/
theorem reserve_gate {R z v k H q gamma : ℝ}
    (hR : R ∈ Icc (3/4:ℝ) (7/9)) (hk : 45457/125000 ≤ k)
    (hv : -4/45 ≤ v) (hH : 9/10 ≤ H) (hg : 0 < gamma)
    (hq : 0 < q) (hqg : q ≤ gamma/1000)
    (hcut : k*(2+6*(z-R*v+R*gamma)) = 1)
    (hreserve : 3*gamma ≤ v-Curve.flow R z) :
    30*q < (stageDatum R z v k H q).H*(stageDatum R z v k H q).F0 := by
  have hk0 : 0 < k := by linarith
  have hrterm : (15/16:ℝ) ≤ R*(15*R-10) := by
    have h := mul_le_mul hR.1 (show (5/4:ℝ) ≤ 15*R-10 by linarith [hR.1])
      (by norm_num : (0:ℝ) ≤ 5/4) (by linarith [hR.1])
    norm_num at h
    exact h
  have hkterm : (1/3:ℝ) ≤ k*R*(15*R-10) := by
    have h := mul_le_mul hk hrterm (by norm_num : (0:ℝ) ≤ 15/16) hk0.le
    norm_num at h
    nlinarith only [h]
  have hbase : gamma/3 ≤ baseReserve R z k := by
    rw [base_reserve_identity (by linarith [hR.1]) hcut]
    have hc : 0 ≤ k*R*(15*R-10)/2 := by nlinarith only [hkterm]
    have h1 := mul_le_mul_of_nonneg_left
      (show 2*gamma ≤ v-gamma-Curve.flow R z by linarith) hc
    have h2 := mul_le_mul_of_nonneg_right hkterm hg.le
    nlinarith only [h1,h2]
  have hdebit := source_pad_debit (R:=R) (z:=z) (H:=H) hv hk0.le hq.le
  have hf : gamma/4 ≤ (stageDatum R z v k H q).F0 := by linarith
  have hp := mul_le_mul hH hf (by positivity : 0 ≤ gamma/4) (by linarith : 0 ≤ H)
  change 30*q < H*(stageDatum R z v k H q).F0
  nlinarith only [hp,hqg,hg]

end
end Qrh.TwoSlot.AnchorContinuum
