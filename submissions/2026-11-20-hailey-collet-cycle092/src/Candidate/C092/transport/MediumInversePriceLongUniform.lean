/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One early uniform strict payment budget for all actual amplified inverse
witnesses in a checked cutoff cell and every radius. -/
import Candidate.C092.transport.MediumInversePriceLongScalar

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source

theorem corrected_long_price_uniform_gap {n y e ν r V : ℝ} (c : Cutoff)
    (hy0 : (369/1000 : ℝ) ≤ y) (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c) (hr0 : 1 ≤ r)
    (hr : r ≤ (c.inverse : ℝ)+(c.ordinary : ℝ)) (hp : PaidWithBand y e ν c) :
    NativeFourthEffective.price n y e ν V (QRH.Cycle092.Source.longDeficit ν r)-radialAllowance V ≤
      longCostWithBand y e ν c-(u-rho : ℚ) := by
  have hn1 : n ≤ 1/2 := by
    have h := hn.trans (mul_le_mul_of_nonneg_left hy (by norm_num [sourceRatio]))
    norm_num [sourceRatio,sourceY] at h
    linarith
  have hH : (H : ℝ) ≤ 1 := by norm_num [H,u]
  have hD := paid_longDeficit_positive c hy0 hy he hν hν1 hg hr hp
  have hbase := actualLongPrice_le_checked (n:=n) (y:=y) (e:=e) c hν1 hr
  have hbelow {v : ℝ} (hv : v ≤ 1) :
      NativeFourthEffective.price n y e ν v (QRH.Cycle092.Source.longDeficit ν r)=actualLongPrice n y e ν v r := by
    unfold NativeFourthEffective.price NativeFourthEffective.credit actualLongPrice nativeFourthCap
    simp only [if_pos hv]
  by_cases hV : V ≤ (H : ℝ)
  · have hDmax : QRH.Cycle092.Source.longDeficit ν r ≤ 5/6 := by
      unfold QRH.Cycle092.Source.longDeficit
      nlinarith [mul_nonneg (show 0 ≤ 5/6-ν by linarith) (show 0 ≤ r by linarith)]
    have hslope : e/4+QRH.Cycle092.Source.longDeficit ν r/2 ≤ 5/6 := by linarith
    have hscale := mul_le_mul_of_nonneg_left hslope (sub_nonneg.mpr hV)
    have hid : actualLongPrice n y e ν V r-actualLongPrice n y e ν (H : ℝ) r =
        ((H : ℝ)-V)*(e/4+QRH.Cycle092.Source.longDeficit ν r/2) := by
      unfold actualLongPrice nativeFourthCap
      rw [if_pos (hV.trans hH),if_pos hH]
      ring
    rw [hbelow (hV.trans hH)]
    unfold radialAllowance
    rw [max_eq_right (by linarith : 0 ≤ (H : ℝ)-V)]
    linarith
  · have hcredit : NativeFourthEffective.credit n (H : ℝ) ≤ NativeFourthEffective.credit n V := by
      unfold NativeFourthEffective.credit
      rw [if_pos hH]
      by_cases hV1 : V ≤ 1
      · rw [if_pos hV1];linarith
      · rw [if_neg hV1]
        nlinarith [mul_nonneg (show 0 ≤ V-1 by linarith) (show 0 ≤ 1/2-n by linarith)]
    have hcost : NativeFourthEffective.price n y e ν V (QRH.Cycle092.Source.longDeficit ν r) ≤
        NativeFourthEffective.price n y e ν (H : ℝ) (QRH.Cycle092.Source.longDeficit ν r) := by
      have hc := mul_le_mul_of_nonneg_left hcredit he
      have hd := mul_le_mul_of_nonneg_right (le_of_not_ge hV) hD.le
      unfold NativeFourthEffective.price
      linarith
    rw [hbelow hH] at hcost
    unfold radialAllowance
    rw [max_eq_left (by linarith : (H : ℝ)-V ≤ 0)]
    linarith

theorem uniform_corrected_long_cell_fee {y e ν : ℝ} (c : Cutoff)
    (hy0 : (369/1000 : ℝ) ≤ y) (hy : y ≤ sourceY)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c) (hp : PaidWithBand y e ν c) :
    ∃ fee : ℝ, 0 < fee ∧
    ∀ n : ℝ, n ≤ sourceRatio*y → ∀ r V : ℝ, 1 ≤ r → r ≤ (c.inverse : ℝ)+(c.ordinary : ℝ) → 0 ≤ V →
      ∀ (live nativeWidth deficit nativeLoss deficitLoss error : ℝ),
        live ≤ sourceWidth n y-(u : ℝ) →
        2*NativeFourthEffective.credit n V-nativeLoss ≤ nativeWidth →
        QRH.Cycle092.Source.longDeficit ν r-deficitLoss ≤ deficit →
        nativeLoss ≤ fee → deficitLoss ≤ fee → error ≤ fee →
      countedPrice y e ν V live nativeWidth deficit+error < radialAllowance V := by
  let gap : ℝ := (u-rho : ℚ)-longCostWithBand y e ν c
  have hgap : 0 < gap := sub_pos.mpr hp.2.1
  let Dmin : ℝ := QRH.Cycle092.Source.longDeficit ν ((c.inverse : ℝ)+(c.ordinary : ℝ))
  have hDmin : 0 < Dmin := paid_longDeficit_positive c hy0 hy he hν hν1 hg le_rfl hp
  let fee : ℝ := min (Dmin/2) (gap/(4*(2+e)))
  have hfee : 0 < fee := lt_min (by positivity) (div_pos hgap (by positivity))
  have hdef : fee ≤ Dmin/2 := min_le_left _ _
  have hsmall : fee*(4*(2+e)) ≤ gap :=
    (le_div_iff₀ (by positivity : (0 : ℝ)<4*(2+e))).mp (min_le_right _ _)
  have hbudget : e*fee/2+fee/2+fee < gap := by
    have hf : 0 < fee*(2+e) := mul_pos hfee (by positivity)
    nlinarith
  refine ⟨fee,hfee,?_⟩
  intro n hn r V hr0 hr hV live nativeWidth deficit nativeLoss deficitLoss error hl hn' hd hnf hdf hef
  have hn1 : n ≤ 1/2 := by
    have h := hn.trans (mul_le_mul_of_nonneg_left hy (by norm_num [sourceRatio]))
    norm_num [sourceRatio,sourceY] at h
    linarith
  have hgV := corrected_long_price_uniform_gap c hy0 hy hn he hν hν1 hg hr0 hr hp (V:=V)
  have hnl := mul_le_mul_of_nonneg_left hnf he
  by_cases hV1 : V ≤ 1
  · have hb := counted_price_le_corrected (ν:=ν) he hV hl hn' hd
    have hdfV := mul_le_mul_of_nonneg_left hdf hV
    have hVf := mul_nonneg (sub_nonneg.mpr hV1) hfee.le
    dsimp [gap] at hbudget
    nlinarith
  · let D : ℝ := QRH.Cycle092.Source.longDeficit ν r-fee
    have hD : 0 ≤ D := by
      have h := QRH.Cycle092.Source.longDeficit_cutoff hν1 hr
      dsimp [D,Dmin] at *
      linarith
    have hc : NativeFourthEffective.credit n 1 ≤ NativeFourthEffective.credit n V := by
      rw [NativeFourthEffective.credit_at_one,NativeFourthEffective.credit,if_neg hV1]
      nlinarith [mul_nonneg (show 0 ≤ V-1 by linarith) (show 0 ≤ 1/2-n by linarith)]
    have hpV : NativeFourthEffective.price n y e ν V D ≤ NativeFourthEffective.price n y e ν 1 D := by
      have hc' := mul_le_mul_of_nonneg_left hc he
      have hd' := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ V by linarith) hD
      unfold NativeFourthEffective.price
      linarith
    have hinv : D ≤ deficit := by dsimp [D];linarith
    have hraw : countedPrice y e ν V live nativeWidth deficit ≤
        NativeFourthEffective.price n y e ν V D+e*fee/2 := by
      have hl' := mul_le_mul_of_nonneg_left hl he
      have hn'' := mul_le_mul_of_nonneg_left hn' he
      have hi' := mul_le_mul_of_nonneg_left hinv hV
      unfold countedPrice NativeFourthEffective.price
      nlinarith
    have hp1 : NativeFourthEffective.price n y e ν 1 D =
        NativeFourthEffective.price n y e ν 1 (QRH.Cycle092.Source.longDeficit ν r)+fee/2 := by
      unfold NativeFourthEffective.price D
      ring
    have hg1 := corrected_long_price_uniform_gap c hy0 hy hn he hν hν1 hg hr0 hr hp (V:=1)
    have ha : radialAllowance V=radialAllowance 1 := by
      unfold radialAllowance
      rw [max_eq_left (by have h := H_real_bounds.2;linarith : (H : ℝ)-V ≤ 0),
        max_eq_left (by have h := H_real_bounds.2;linarith : (H : ℝ)-1 ≤ 0)]
    rw [ha]
    rw [hp1] at hpV
    dsimp [gap] at hbudget
    linarith


theorem uniform_corrected_long_fee {n y e ν : ℝ} (c : Cutoff)
    (hy0 : (369/1000 : ℝ) ≤ y) (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c) (hp : PaidWithBand y e ν c) :
    ∃ fee : ℝ, 0 < fee ∧
    ∀ r V : ℝ, 1 ≤ r → r ≤ (c.inverse : ℝ)+(c.ordinary : ℝ) → 0 ≤ V →
      ∀ (live nativeWidth deficit nativeLoss deficitLoss error : ℝ),
        live ≤ sourceWidth n y-(u : ℝ) →
        2*NativeFourthEffective.credit n V-nativeLoss ≤ nativeWidth →
        QRH.Cycle092.Source.longDeficit ν r-deficitLoss ≤ deficit →
        nativeLoss ≤ fee → deficitLoss ≤ fee → error ≤ fee →
      countedPrice y e ν V live nativeWidth deficit+error < radialAllowance V := by
  obtain ⟨fee,hfee,h⟩ := uniform_corrected_long_cell_fee c hy0 hy he hν hν1 hg hp
  exact ⟨fee,hfee,h n hn⟩

#print axioms uniform_corrected_long_cell_fee
#print axioms uniform_corrected_long_fee
end
end QRH.Cycle092.MediumInversePrice
