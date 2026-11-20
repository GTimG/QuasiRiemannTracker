/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact alignment of P.2's real curved quota with the genuine analytic curve,
and positive open-rectangle collars above the actual inverse length. -/
import Candidate.C092.transport.MediumInversePriceRect
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorContinuum.GainBounds

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open Set OAI OAI.SevenEighths
open Qrh.MarkedAnchor.Interface.Contract
open QRH.ContactContinuation QRH.SourceCertificate
open QRH.Cycle092.Source

theorem curve_gain_eq {r : ℝ} (hr : 3/4 ≤ r) :
    Qrh.TwoSlot.AnchorContinuum.Curve.Z (7/9) r =
      11*r/16-7/24-radical r := by
  let C := Qrh.TwoSlot.AnchorContinuum.Curve.Z (7/9) r
  have hq := Qrh.TwoSlot.AnchorContinuum.Curve.q0_pow_five (r := r) (by linarith)
  have hqt := Qrh.TwoSlot.AnchorContinuum.Curve.q0_pow_five (r := 7/9) (by norm_num)
  have hqp := Qrh.TwoSlot.AnchorContinuum.Curve.q0_pos (r := r) (by linarith)
  have hqtp := Qrh.TwoSlot.AnchorContinuum.Curve.q0_pos (r := 7/9) (by norm_num)
  have hCeq : (11*r/16-7/24)-C =
      (Qrh.TwoSlot.AnchorContinuum.Curve.P (7/9)/Qrh.TwoSlot.AnchorContinuum.Curve.q0 (7/9))*
        Qrh.TwoSlot.AnchorContinuum.Curve.q0 r := by
    dsimp [C,Qrh.TwoSlot.AnchorContinuum.Curve.Z,Qrh.TwoSlot.AnchorContinuum.Curve.P]
    ring
  have hPtop : 0 < Qrh.TwoSlot.AnchorContinuum.Curve.P (7/9) := by
    norm_num [Qrh.TwoSlot.AnchorContinuum.Curve.P]
  have hgap0 : 0 ≤ (11*r/16-7/24)-C := by
    rw [hCeq]
    exact mul_nonneg (div_nonneg hPtop.le hqtp.le) hqp.le
  have hdiff : 0 ≤ r-2/3 := by linarith
  have hr0 : 0 ≤ radical r := by unfold radical;positivity
  have he : ((11*r/16-7/24)-C)^5=(radical r)^5 := by
    rw [hCeq,mul_pow,div_pow,hq,hqt,radical_pow (by linarith)]
    norm_num [Qrh.TwoSlot.AnchorContinuum.Curve.P]
    ring
  have hgap : (11*r/16-7/24)-C=radical r := by
    apply le_antisymm
    · exact (pow_le_pow_iff_left₀ hgap0 hr0 (by decide : (5 : ℕ)≠0)).mp he.le
    · exact (pow_le_pow_iff_left₀ hr0 hgap0 (by decide : (5 : ℕ)≠0)).mp he.ge
  dsimp [C] at hgap
  linarith

theorem curve_quota_eq {r : ℝ} (hr : 3/4 ≤ r) :
    (1-r)/2+Qrh.TwoSlot.AnchorContinuum.Curve.Z (7/9) r=curvedQuota r := by
  rw [curve_gain_eq hr]
  unfold curvedQuota radical
  ring

/-- The rectangle is anchored strictly ABOVE the actual length r. Its
positive decrement remains genuine; ζ pays at most three such decrements. -/
theorem curved_anchor_admissible {r R δ ζ : ℝ}
    (hr : 3/4 ≤ r) (hδ : 0 < δ) (hRlo : r+δ ≤ R) (hRhi : R ≤ r+2*δ)
    (hRtop : R ≤ 7/9) (hζ : 3*δ ≤ ζ)
    (hz : 0 ≤ inverseQuota r-ζ) :
    (anchorRect R (Qrh.TwoSlot.AnchorContinuum.Curve.Z (7/9) R) δ).Admissible
      r (inverseQuota r-ζ) 1 := by
  have hrR : r ≤ R := by linarith
  have hrTop : r < 7/9 := by linarith
  have hq : inverseQuota r=curvedQuota r := by
    simp [inverseQuota,not_lt.mpr hr,not_le.mpr hrTop]
  have hd := radical_increment_le hr hrR hRtop
  have hloss : curvedQuota r-curvedQuota R ≤ (13/16 : ℝ)*(R-r) := by
    unfold curvedQuota at *
    change radical R-radical r ≤ R-r at hd
    unfold radical at hd
    linarith
  refine ⟨by linarith,?_,hz,?_⟩
  · simp only [anchorRect,mul_one]
    linarith
  · simp only [anchorRect,mul_one]
    change inverseQuota r-ζ ≤ (1-R)/2+Qrh.TwoSlot.AnchorContinuum.Curve.Z (7/9) R-δ
    rw [curve_quota_eq (hr.trans hrR),hq]
    linarith

/-- The checker uses its certified rational lower tangent. Any genuine
source gain above that tangent pays the same three-decrement collar. -/
theorem tangent_anchor_admissible {r R δ ζ gain : ℝ}
    (hr : 0 ≤ r) (hrtop : r < 3/4) (hδ : 0 < δ)
    (hRlo : r+δ ≤ R) (hRhi : R ≤ r+2*δ) (hζ : 3*δ ≤ ζ)
    (hgain : 5805911/100000000-(379981/5000000)*R ≤ gain)
    (hz : 0 ≤ inverseQuota r-ζ) :
    (anchorRect R gain δ).Admissible r (inverseQuota r-ζ) 1 := by
  have hq : inverseQuota r=(1-r)/2+5805911/100000000-(379981/5000000)*r := by
    simp [inverseQuota,hrtop]
  refine ⟨hr,?_,hz,?_⟩
  · simp only [anchorRect,mul_one]
    linarith
  · simp only [anchorRect,mul_one]
    change inverseQuota r-ζ ≤ (1-R)/2+gain-δ
    rw [hq]
    linarith

#print axioms curve_gain_eq
#print axioms curved_anchor_admissible
#print axioms tangent_anchor_admissible
end
end QRH.Cycle092.MediumInversePrice
