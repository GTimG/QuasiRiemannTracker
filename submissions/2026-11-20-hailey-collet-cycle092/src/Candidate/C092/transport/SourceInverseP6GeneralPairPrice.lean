/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual inverse prices with the charged response/zero window discrepancy. -/
import Candidate.C092.transport.SourceInverseP6ClosePrice
namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source
open QRH.Cycle092.MediumInversePrice QRH.Cycle092.SourceFurtherWitness

theorem general_pair_approx_price_window {y el eu ν ν₀ d r L nw iw step price : ℝ}
    (hν0 : ν₀ ≤ ν+price) (hν : ν ≤ ν₀+step) (he : eu ≤ el+step)
    (hs : 0 ≤ step) (hy0 : 0 ≤ y) (hy : y ≤ 1) (hL0 : 0 ≤ L) (hL : L ≤ 1)
    (hd : 0 ≤ d) (hr : 0 ≤ r) (hp : 0 ≤ price) :
    roundedSourcePrice y el eu ν d r L nw iw ≤
      roundedSourcePrice y el el ν₀ d r L nw iw+2*step+price*d*r/2 := by
  have h1 := mul_le_mul_of_nonneg_right (show ν-ν₀ ≤ step by linarith) hy0
  have h2 := mul_le_mul_of_nonneg_left hy hs
  have h3 := mul_le_mul_of_nonneg_right (show eu-el ≤ step by linarith) hL0
  have h4 := mul_le_mul_of_nonneg_left hL hs
  have hneg : -(price*d*r) ≤ d*((ν-ν₀)*r) := by
    have h := mul_le_mul_of_nonneg_left (show -price ≤ ν-ν₀ by linarith) (mul_nonneg hd hr)
    nlinarith
  unfold roundedSourcePrice unmarkedDeficit
  nlinarith

/-- One early positive mesh/loss budget pays both inverse alternatives at
all actual V>=.98. Actual responses may vary throughout their finite window.
The source radius d is enlarged exactly once. -/
theorem general_pair_approx_inverse_alternatives_paid
    {y el ν₀ loss : ℝ} (c : Cutoff)
    (hy0 : (369/1000:ℝ) ≤ y) (hy : y ≤ sourceY)
    (he : 0 ≤ el) (hν : el ≤ ν₀) (hν1 : ν₀ ≤ 3/4)
    {b : ℚ} (hg : CutoffGuard b c) (hp : PaidWithBand y el ν₀ c) (hloss : 0 < loss) :
    ∃ step δ fee : ℝ,0 < step ∧ 0 < δ ∧ 0 < fee ∧ step=loss/10 ∧ δ=loss/10 ∧ 3*δ+2*step ≤ loss ∧
    ∀ (n V d ν eu r L nw iw nativeLoss inverseLoss ε error price dmax : ℝ),
      n ≤ sourceRatio*y → (98/100:ℝ) ≤ V → V ≤ d → d ≤ V+3*δ →
      0 ≤ price → ν₀ ≤ ν+price → ν ≤ ν₀+step → eu ≤ el+step →
      d ≤ dmax → r ≤ 2 → price*dmax ≤ loss/4 →
      (c.inverse:ℝ) ≤ r → r ≤ (c.inverse:ℝ)+(c.ordinary:ℝ)+ε →
      0 ≤ L → L ≤ 1 → L ≤ sourceWidth n y-(u:ℝ) →
      2*NativeFourthEffective.credit n d-nativeLoss ≤ nw →
      (r ≤ 1 → inverseQuota r-inverseLoss ≤ iw) →
      nativeLoss ≤ fee → inverseLoss ≤ fee → 0 ≤ ε → ε ≤ fee → error ≤ fee →
      d+roundedSourcePrice y el eu ν d r L nw (if r ≤ 1 then iw else 0)+error < 
        V+radialAllowance V+loss := by
  have hroot : RootGuard c.inverse c.rootUpper := hg.2.2.2.2.2.2.2.2
  obtain ⟨fi,hfi,_,hpayI⟩ := uniform_corrected_inverse_cell_fee c hy he hν hν1 hroot hp
  obtain ⟨fl,hfl,hpayL⟩ := uniform_corrected_long_cell_fee c hy0 hy he hν hν1 hg hp
  let step := loss/10
  let δ := loss/10
  let fee := min fi fl
  have hfee : 0 < fee := lt_min hfi hfl
  have hstep : 0 < step := by dsimp [step]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨step,δ,fee,hstep,hδ,hfee,rfl,rfl,by dsimp [step,δ];linarith,?_⟩
  intro n V d ν eu r L nw iw nativeLoss inverseLoss ε error price dmax hn hV hVd hdV hp0 hν0 hν' heu hdmax hr2 hpbudget hr0 hrT
    hL0 hL hLive hNative hInverse hnl hil hε hεfee hef
  have hd : 0 ≤ d := by linarith
  have hrbase : (367/500:ℝ) ≤ r := by
    have h := (Rat.cast_lt (K:=ℝ)).mpr hg.2.2.2.2.2.1
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
    linarith
  have hr : 0 ≤ r := by linarith
  have hypos : 0 ≤ y := by linarith
  have hy1 : y ≤ 1 := hy.trans (by norm_num [sourceY])
  have hwin0 := general_pair_approx_price_window hν0 hν' heu hstep.le hypos hy1 hL0 hL hd hr hp0
    (el:=el) (nw:=nw) (iw:=if r ≤ 1 then iw else 0)
  have hpriceRadius : price*d*r/2 ≤ price*dmax := by
    have h1 := mul_le_mul_of_nonneg_left hdmax hp0
    have h2 := mul_le_mul_of_nonneg_left hr2 (mul_nonneg hp0 hd)
    nlinarith
  have hwin := hwin0.trans (show _ ≤ roundedSourcePrice y el el ν₀ d r L nw (if r ≤ 1 then iw else 0)+2*step+price*dmax by linarith)
  have hni : nativeLoss ≤ fi := hnl.trans (min_le_left _ _)
  have hnl' : nativeLoss ≤ fl := hnl.trans (min_le_right _ _)
  have hei : error ≤ fi := hef.trans (min_le_left _ _)
  have hel : error ≤ fl := hef.trans (min_le_right _ _)
  have hpayed : roundedSourcePrice y el el ν₀ d r L nw (if r ≤ 1 then iw else 0)+error < radialAllowance d := by
    by_cases hrs : r ≤ 1
    · have h := hpayI n hn r d hrbase hr0 hrs hd L nw iw nativeLoss inverseLoss error
        hLive hNative (hInverse hrs) hni (hil.trans (min_le_left _ _)) hei
      unfold roundedSourcePrice
      rw [if_pos hrs,unmarked_deficit_short hrs]
      dsimp only [repeatedPrice] at h
      linarith
    · have hrl : 1 ≤ r := (lt_of_not_ge hrs).le
      let T : ℝ := (c.inverse:ℝ)+(c.ordinary:ℝ)
      have hT : 1 ≤ T := (cutoff_detector_domain c hg).1
      let rclip := min r T
      have hc0 : 1 ≤ rclip := le_min hrl hT
      have hcT : rclip ≤ T := min_le_right _ _
      have hc : QRH.Cycle092.Source.longDeficit ν₀ rclip-(5/6-ν₀)*ε ≤ QRH.Cycle092.Source.longDeficit ν₀ r := by
        have hgap : r-rclip ≤ ε := by
          by_cases hrc : r ≤ T
          · dsimp only [rclip];rw [min_eq_left hrc];linarith
          · dsimp only [rclip];rw [min_eq_right (le_of_not_ge hrc)];dsimp only [T];linarith
        have hprod := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 5/6-ν₀ by linarith)
        unfold QRH.Cycle092.Source.longDeficit
        nlinarith
      have hdf : (5/6-ν₀)*ε ≤ fl := by
        have h0 : 0 ≤ ν₀ := he.trans hν
        have hsmall : (5/6-ν₀)*ε ≤ ε := by nlinarith
        exact hsmall.trans (hεfee.trans (min_le_right _ _))
      have h := hpayL n hn rclip d hc0 hcT hd L nw (QRH.Cycle092.Source.longDeficit ν₀ r)
        nativeLoss ((5/6-ν₀)*ε) error hLive hNative hc hnl' hdf hel
      unfold roundedSourcePrice
      rw [if_neg hrs,unmarked_deficit_long hrl,mul_zero,add_zero]
      dsimp only [countedPrice] at h
      linarith
  have hrad := QRH.Cycle092.MediumReplace.Source.enlarged_price hVd hdV
  dsimp [step,δ] at *
  linarith

#print axioms general_pair_approx_inverse_alternatives_paid
end
end QRH.Cycle092.SourceInverseP6
