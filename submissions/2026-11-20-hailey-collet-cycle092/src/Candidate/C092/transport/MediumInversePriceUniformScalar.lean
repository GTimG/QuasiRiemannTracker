/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform strict reserve for the actual repeated inverse branch. The reserve
is chosen before the actual inverse length and radius, as source banks need. -/
import Candidate.C092.transport.MediumInversePriceScalar

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source

theorem corrected_inverse_price_uniform_gap {n y e ν r V : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    (hg : RootGuard c.inverse c.rootUpper) (hr0 : 367/500 ≤ r)
    (hr : (c.inverse : ℝ) ≤ r) (hr1 : r ≤ 1) :
    NativeFourthEffective.price n y e ν V (ν*r+e*inverseQuota r)-radialAllowance V ≤
      shortCostWithBand y e ν c-(u-rho : ℚ) := by
  have hn1 : n ≤ 1/2 := by
    have h := hn.trans (mul_le_mul_of_nonneg_left hy (by norm_num [sourceRatio]))
    norm_num [sourceRatio,sourceY] at h
    linarith
  have hH : (H : ℝ) ≤ 1 := by norm_num [H,u]
  have hD : 0 ≤ ν*r+e*inverseQuota r := add_nonneg
    (mul_nonneg (he.trans hν) (by linarith)) (mul_nonneg he (inverseQuota_nonneg hr0 hr1))
  have hbase := inversePrice_le_checked (y:=y) c he hν hg hr
  have hbelow {v : ℝ} (hv : v ≤ 1) :
      NativeFourthEffective.price n y e ν v (ν*r+e*inverseQuota r)=inversePrice y e ν v r := by
    unfold NativeFourthEffective.price NativeFourthEffective.credit inversePrice sourceWidth
    rw [if_pos hv]
    ring
  by_cases hV : V ≤ (H : ℝ)
  · have hq := mul_le_mul_of_nonneg_left (inverseQuota_le_half hr0 hr1) he
    have hnr := mul_le_mul_of_nonneg_left hr1 (he.trans hν)
    have hslope : e/4+(ν*r+e*inverseQuota r)/2 ≤ 5/6 := by nlinarith
    have hscale := mul_le_mul_of_nonneg_left hslope (sub_nonneg.mpr hV)
    have hid : inversePrice y e ν V r-inversePrice y e ν (H : ℝ) r =
        ((H : ℝ)-V)*(e/4+(ν*r+e*inverseQuota r)/2) := by unfold inversePrice;ring
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
    have hcost : NativeFourthEffective.price n y e ν V (ν*r+e*inverseQuota r) ≤
        NativeFourthEffective.price n y e ν (H : ℝ) (ν*r+e*inverseQuota r) := by
      have hc := mul_le_mul_of_nonneg_left hcredit he
      have hd := mul_le_mul_of_nonneg_right (le_of_not_ge hV) hD
      unfold NativeFourthEffective.price
      linarith
    rw [hbelow hH] at hcost
    unfold radialAllowance
    rw [max_eq_left (by linarith : (H : ℝ)-V ≤ 0)]
    linarith

/-- A fixed checked cell gives one strictly positive loss budget valid for
all actual short-inverse lengths and all radii. The same budget may therefore
be used to construct the genuine finite source bank before the scale. -/
theorem uniform_corrected_inverse_cell_fee {y e ν : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    (hg : RootGuard c.inverse c.rootUpper) (hp : PaidWithBand y e ν c) :
    ∃ fee : ℝ, 0 < fee ∧ fee ≤ 1/2 ∧
    ∀ n : ℝ, n ≤ sourceRatio*y → ∀ r V : ℝ, 367/500 ≤ r → (c.inverse : ℝ) ≤ r → r ≤ 1 → 0 ≤ V →
      ∀ (live nativeWidth inverseWidth nativeLoss inverseLoss error : ℝ),
        live ≤ sourceWidth n y-(u : ℝ) →
        2*NativeFourthEffective.credit n V-nativeLoss ≤ nativeWidth →
        inverseQuota r-inverseLoss ≤ inverseWidth →
        nativeLoss ≤ fee → inverseLoss ≤ fee → error ≤ fee →
      repeatedPrice y e ν V r live nativeWidth inverseWidth+error < radialAllowance V := by
  let gap : ℝ := (u-rho : ℚ)-shortCostWithBand y e ν c
  have hgap : 0 < gap := sub_pos.mpr hp.1
  let fee : ℝ := min (1/2) (gap/(4*(1+e)))
  have hfee : 0 < fee := lt_min (by norm_num) (div_pos hgap (by positivity))
  have hhalf : fee ≤ 1/2 := min_le_left _ _
  have hsmall : fee*(4*(1+e)) ≤ gap :=
    (le_div_iff₀ (by positivity : (0 : ℝ)<4*(1+e))).mp (min_le_right _ _)
  have hbudget : e*fee+fee < gap := by
    have hf : 0 < fee*(1+e) := mul_pos hfee (by positivity)
    nlinarith
  refine ⟨fee,hfee,hhalf,?_⟩
  intro n hn r V hr0 hr hr1 hV live nativeWidth inverseWidth nativeLoss inverseLoss error hl hn' hi hnf hif hef
  have hn1 : n ≤ 1/2 := by
    have h := hn.trans (mul_le_mul_of_nonneg_left hy (by norm_num [sourceRatio]))
    norm_num [sourceRatio,sourceY] at h
    linarith
  have hgV := corrected_inverse_price_uniform_gap c hy hn he hν hν1 hg hr0 hr hr1 (V:=V)
  have hnl := mul_le_mul_of_nonneg_left hnf he
  have hil := mul_le_mul_of_nonneg_left hif he
  by_cases hV1 : V ≤ 1
  · have hb := repeated_price_le_corrected (ν:=ν) he hV hl hn' hi
    have hifV := mul_le_mul_of_nonneg_left hil hV
    have hVe := mul_nonneg (sub_nonneg.mpr hV1) (mul_nonneg he hfee.le)
    dsimp [gap] at hbudget
    nlinarith
  · let D : ℝ := ν*r+e*inverseQuota r-e*fee
    have hq := mul_nonneg he (inverseQuota_nonneg hr0 hr1)
    have hνr := mul_le_mul_of_nonneg_right hν (show 0 ≤ r by linarith)
    have her := mul_nonneg he (show 0 ≤ r-fee by linarith)
    have hD : 0 ≤ D := by dsimp [D];nlinarith
    have hc : NativeFourthEffective.credit n 1 ≤ NativeFourthEffective.credit n V := by
      rw [NativeFourthEffective.credit_at_one,NativeFourthEffective.credit,if_neg hV1]
      nlinarith [mul_nonneg (show 0 ≤ V-1 by linarith) (show 0 ≤ 1/2-n by linarith)]
    have hpV : NativeFourthEffective.price n y e ν V D ≤ NativeFourthEffective.price n y e ν 1 D := by
      have hc' := mul_le_mul_of_nonneg_left hc he
      have hd' := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ V by linarith) hD
      unfold NativeFourthEffective.price
      linarith
    have hinv : D ≤ ν*r+e*inverseWidth := by
      dsimp [D]
      nlinarith [mul_le_mul_of_nonneg_left hi he]
    have hraw : repeatedPrice y e ν V r live nativeWidth inverseWidth ≤
        NativeFourthEffective.price n y e ν V D+e*fee/2 := by
      have hl' := mul_le_mul_of_nonneg_left hl he
      have hn'' := mul_le_mul_of_nonneg_left hn' he
      have hi' := mul_le_mul_of_nonneg_left hinv hV
      unfold repeatedPrice NativeFourthEffective.price
      nlinarith
    have hp1 : NativeFourthEffective.price n y e ν 1 D =
        NativeFourthEffective.price n y e ν 1 (ν*r+e*inverseQuota r)+e*fee/2 := by
      unfold NativeFourthEffective.price D
      ring
    have hg1 := corrected_inverse_price_uniform_gap c hy hn he hν hν1 hg hr0 hr hr1 (V:=1)
    have ha : radialAllowance V=radialAllowance 1 := by
      unfold radialAllowance
      rw [max_eq_left (by have h := H_real_bounds.2;linarith : (H : ℝ)-V ≤ 0),
        max_eq_left (by have h := H_real_bounds.2;linarith : (H : ℝ)-1 ≤ 0)]
    rw [ha]
    rw [hp1] at hpV
    dsimp [gap] at hbudget
    linarith


theorem uniform_corrected_inverse_fee {n y e ν : ℝ} (c : Cutoff)
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y)
    (he : 0 ≤ e) (hν : e ≤ ν) (hν1 : ν ≤ 3/4)
    (hg : RootGuard c.inverse c.rootUpper) (hp : PaidWithBand y e ν c) :
    ∃ fee : ℝ, 0 < fee ∧ fee ≤ 1/2 ∧
    ∀ r V : ℝ, 367/500 ≤ r → (c.inverse : ℝ) ≤ r → r ≤ 1 → 0 ≤ V →
      ∀ (live nativeWidth inverseWidth nativeLoss inverseLoss error : ℝ),
        live ≤ sourceWidth n y-(u : ℝ) →
        2*NativeFourthEffective.credit n V-nativeLoss ≤ nativeWidth →
        inverseQuota r-inverseLoss ≤ inverseWidth →
        nativeLoss ≤ fee → inverseLoss ≤ fee → error ≤ fee →
      repeatedPrice y e ν V r live nativeWidth inverseWidth+error < radialAllowance V := by
  obtain ⟨fee,hfee,hhalf,h⟩ := uniform_corrected_inverse_cell_fee c hy he hν hν1 hg hp
  exact ⟨fee,hfee,hhalf,h n hn⟩

#print axioms uniform_corrected_inverse_cell_fee
#print axioms uniform_corrected_inverse_fee
end
end QRH.Cycle092.MediumInversePrice
