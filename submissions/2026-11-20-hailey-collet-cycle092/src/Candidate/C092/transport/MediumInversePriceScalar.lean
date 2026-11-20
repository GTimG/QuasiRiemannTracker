/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact P.2 alignment of the actual repeated native/inverse source prices.
Above-one continuation uses the separately corrected native-credit module. -/
import Candidate.C092.transport.MediumInversePriceRepeatActual
import Candidate.C092.transport.MediumInversePriceShort
import Candidate.C092.transport.NativeFourthEffective

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source

def repeatedPrice (y e ν V r live nativeWidth inverseWidth : ℝ) : ℝ :=
  ν*y+e*(live-nativeWidth/2)-V*(ν*r+e*inverseWidth)/2

/-- One actual long-native quota and one actual inverse quota, with their
inward rounding and open-anchor losses, give precisely P.2's scalar price.
The native quota is halved once by Cauchy. -/
theorem repeated_price_le_checked {n y e ν V r live nativeWidth inverseWidth nativeLoss inverseLoss : ℝ}
    (he : 0 ≤ e) (hV : 0 ≤ V) (hV1 : V ≤ 1)
    (hLive : live ≤ sourceWidth n y-(u : ℝ))
    (hNative : V/2-n-nativeLoss ≤ nativeWidth)
    (hInverse : inverseQuota r-inverseLoss ≤ inverseWidth) :
    repeatedPrice y e ν V r live nativeWidth inverseWidth ≤
      actualInversePrice n y e ν V r+e*nativeLoss/2+V*e*inverseLoss/2 := by
  have hl := mul_le_mul_of_nonneg_left hLive he
  have hn := mul_le_mul_of_nonneg_left hNative he
  have hi := mul_le_mul_of_nonneg_left hInverse (mul_nonneg hV he)
  unfold repeatedPrice actualInversePrice nativeFourthCap
  rw [if_pos hV1]
  nlinarith

/-- Every strict checked P.2 payment leaves a positive simultaneous budget
for the genuine native quota, inverse anchor/floor quota and analytic losses.
This statement is restricted to the correctly normalized radius interval. -/
theorem checked_inverse_pays_repeated {n y e ν r V : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    (hg : RootGuard c.inverse c.rootUpper) (hr0 : 367/500 ≤ r)
    (hr : (c.inverse : ℝ) ≤ r) (hr1 : r ≤ 1)
    (hV0 : (98/100 : ℝ) ≤ V) (hV1 : V ≤ 1) (hp : PaidWithBand y e ν c) :
    ∃ fee : ℝ, 0 < fee ∧
      ∀ (live nativeWidth inverseWidth nativeLoss inverseLoss error : ℝ),
        live ≤ sourceWidth n y-(u : ℝ) → V/2-n-nativeLoss ≤ nativeWidth →
        inverseQuota r-inverseLoss ≤ inverseWidth →
        nativeLoss ≤ fee → inverseLoss ≤ fee → error ≤ fee →
      repeatedPrice y e ν V r live nativeWidth inverseWidth+error < radialAllowance V := by
  have hpaid := checked_inverse_pays_all_radii c hy hn he hν hν1 hg hr0 hr hr1 hV0 hp
  have hV : 0 ≤ V := by linarith
  let gap := radialAllowance V-actualInversePrice n y e ν V r
  let factor := 1+e+V*e
  let fee := gap/(4*factor)
  have hgap : 0 < gap := by dsimp [gap];linarith
  have hfactor : 0 < factor := by dsimp [factor];positivity
  have hfee : 0 < fee := div_pos hgap (mul_pos (by norm_num) hfactor)
  have hfeeEq : fee*(4*factor)=gap := by dsimp [fee];field_simp
  refine ⟨fee,hfee,?_⟩
  intro live nativeWidth inverseWidth nativeLoss inverseLoss error hl hn hi hnfee hifee hefee
  have hb := repeated_price_le_checked (ν := ν) he hV hV1 hl hn hi
  have hnl := mul_le_mul_of_nonneg_left hnfee he
  have hil := mul_le_mul_of_nonneg_left hifee (mul_nonneg hV he)
  have hfe : 0 ≤ fee*e := mul_nonneg hfee.le he
  have hfVe : 0 ≤ fee*(V*e) := mul_nonneg hfee.le (mul_nonneg hV he)
  dsimp [factor,gap] at hfeeEq
  nlinarith

/-- The true native quota is twice its contribution after Cauchy, at every
radius. Inward quota losses enter linearly in the actual same-row price. -/
theorem repeated_price_le_corrected
    {n y e ν V r live nativeWidth inverseWidth nativeLoss inverseLoss : ℝ}
    (he : 0 ≤ e) (hV : 0 ≤ V)
    (hLive : live ≤ sourceWidth n y-(u : ℝ))
    (hNative : 2*NativeFourthEffective.credit n V-nativeLoss ≤ nativeWidth)
    (hInverse : inverseQuota r-inverseLoss ≤ inverseWidth) :
    repeatedPrice y e ν V r live nativeWidth inverseWidth ≤
      NativeFourthEffective.price n y e ν V (ν*r+e*inverseQuota r)+
        e*nativeLoss/2+V*e*inverseLoss/2 := by
  have hl := mul_le_mul_of_nonneg_left hLive he
  have hn := mul_le_mul_of_nonneg_left hNative he
  have hi := mul_le_mul_of_nonneg_left hInverse (mul_nonneg hV he)
  unfold repeatedPrice NativeFourthEffective.price
  nlinarith

/-- The corrected checked payment gives one positive budget for the actual
native quota, the inverse open-anchor/floor quota, and analytic errors, also
above unit radius. All events refer to the same repeated-price expression. -/
theorem corrected_checked_inverse_pays_repeated {n y e ν r V : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    (hg : RootGuard c.inverse c.rootUpper) (hr0 : 367/500 ≤ r)
    (hr : (c.inverse : ℝ) ≤ r) (hr1 : r ≤ 1)
    (hV0 : (98/100 : ℝ) ≤ V) (hp : PaidWithBand y e ν c) :
    ∃ fee : ℝ, 0 < fee ∧
      ∀ (live nativeWidth inverseWidth nativeLoss inverseLoss error : ℝ),
        live ≤ sourceWidth n y-(u : ℝ) →
        2*NativeFourthEffective.credit n V-nativeLoss ≤ nativeWidth →
        inverseQuota r-inverseLoss ≤ inverseWidth →
        nativeLoss ≤ fee → inverseLoss ≤ fee → error ≤ fee →
      repeatedPrice y e ν V r live nativeWidth inverseWidth+error < radialAllowance V := by
  have hpaid := NativeFourthEffective.corrected_short_price c hy hn he hν hν1 hg hr0 hr hr1 hV0 hp
  have hV : 0 ≤ V := by linarith
  let gap := radialAllowance V-NativeFourthEffective.price n y e ν V (ν*r+e*inverseQuota r)
  let factor := 1+e+V*e
  let fee := gap/(4*factor)
  have hgap : 0 < gap := by dsimp [gap];linarith
  have hfactor : 0 < factor := by dsimp [factor];positivity
  have hfee : 0 < fee := div_pos hgap (mul_pos (by norm_num) hfactor)
  have hfeeEq : fee*(4*factor)=gap := by dsimp [fee];field_simp
  refine ⟨fee,hfee,?_⟩
  intro live nativeWidth inverseWidth nativeLoss inverseLoss error hl hn hi hnfee hifee hefee
  have hb := repeated_price_le_corrected (ν := ν) he hV hl hn hi
  have hnl := mul_le_mul_of_nonneg_left hnfee he
  have hil := mul_le_mul_of_nonneg_left hifee (mul_nonneg hV he)
  have hfe : 0 ≤ fee*e := mul_nonneg hfee.le he
  have hfVe : 0 ≤ fee*(V*e) := mul_nonneg hfee.le (mul_nonneg hV he)
  dsimp [factor,gap] at hfeeEq
  nlinarith

#print axioms corrected_checked_inverse_pays_repeated
#print axioms checked_inverse_pays_repeated
end
end QRH.Cycle092.MediumInversePrice
