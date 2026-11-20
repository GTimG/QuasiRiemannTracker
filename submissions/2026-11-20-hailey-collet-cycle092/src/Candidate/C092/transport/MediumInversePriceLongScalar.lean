/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual long inverse count and retained native fourth use P.2's corrected
price, with one common positive budget for all inward analytic losses. -/
import Candidate.C092.transport.MediumInversePriceScalar

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source

def countedPrice (y e ν V live nativeWidth deficit : ℝ) : ℝ :=
  ν*y+e*(live-nativeWidth/2)-V*deficit/2

theorem counted_price_le_corrected
    {n y e ν V live nativeWidth deficit targetDeficit nativeLoss deficitLoss : ℝ}
    (he : 0 ≤ e) (hV : 0 ≤ V)
    (hLive : live ≤ sourceWidth n y-(u : ℝ))
    (hNative : 2*NativeFourthEffective.credit n V-nativeLoss ≤ nativeWidth)
    (hDeficit : targetDeficit-deficitLoss ≤ deficit) :
    countedPrice y e ν V live nativeWidth deficit ≤
      NativeFourthEffective.price n y e ν V targetDeficit+
        e*nativeLoss/2+V*deficitLoss/2 := by
  have hl := mul_le_mul_of_nonneg_left hLive he
  have hn := mul_le_mul_of_nonneg_left hNative he
  have hd := mul_le_mul_of_nonneg_left hDeficit hV
  unfold countedPrice NativeFourthEffective.price
  nlinarith

/-- The long branch's actual count deficit may be rounded inward, and the
true native retained quota may also be rounded inward. Strict checked P.2
payment pays both losses and the remaining analytic error simultaneously. -/
theorem corrected_checked_long_pays_repeated {n y e ν r V : ℝ} (c : Cutoff)
    (hy0 : (369/1000 : ℝ) ≤ y) (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c) (hr0 : 1 ≤ r)
    (hr : r ≤ (c.inverse : ℝ)+(c.ordinary : ℝ))
    (hV0 : (98/100 : ℝ) ≤ V) (hp : PaidWithBand y e ν c) :
    ∃ fee : ℝ, 0 < fee ∧
      ∀ (live nativeWidth deficit nativeLoss deficitLoss error : ℝ),
        live ≤ sourceWidth n y-(u : ℝ) →
        2*NativeFourthEffective.credit n V-nativeLoss ≤ nativeWidth →
        QRH.Cycle092.Source.longDeficit ν r-deficitLoss ≤ deficit →
        nativeLoss ≤ fee → deficitLoss ≤ fee → error ≤ fee →
      countedPrice y e ν V live nativeWidth deficit+error < radialAllowance V := by
  have hpaid := NativeFourthEffective.corrected_long_price c hy0 hy hn he hν hν1 hg hr0 hr hV0 hp
  have hV : 0 ≤ V := by linarith
  let gap := radialAllowance V-NativeFourthEffective.price n y e ν V (QRH.Cycle092.Source.longDeficit ν r)
  let factor := 1+e+V
  let fee := gap/(4*factor)
  have hgap : 0 < gap := by dsimp [gap];linarith
  have hfactor : 0 < factor := by dsimp [factor];positivity
  have hfee : 0 < fee := div_pos hgap (mul_pos (by norm_num) hfactor)
  have hfeeEq : fee*(4*factor)=gap := by dsimp [fee];field_simp
  refine ⟨fee,hfee,?_⟩
  intro live nativeWidth deficit nativeLoss deficitLoss error hl hn hd hnfee hdfee hefee
  have hb := counted_price_le_corrected (ν := ν) he hV hl hn hd
  have hnl := mul_le_mul_of_nonneg_left hnfee he
  have hdl := mul_le_mul_of_nonneg_left hdfee hV
  have hfe : 0 ≤ fee*e := mul_nonneg hfee.le he
  have hfV : 0 ≤ fee*V := mul_nonneg hfee.le hV
  dsimp [factor,gap] at hfeeEq
  nlinarith

#print axioms corrected_checked_long_pays_repeated
end
end QRH.Cycle092.MediumInversePrice
