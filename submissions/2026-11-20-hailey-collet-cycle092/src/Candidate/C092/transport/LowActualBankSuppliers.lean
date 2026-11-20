/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual source suppliers for every lower-radius bank entry. -/
import Candidate.C092.transport.LowActualRadiusBank

set_option autoImplicit false
namespace QRH.Cycle092.LowActual
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.NativeStrip
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths

/-- The genuine positive reserve family approaches the native mean quota.
The strictly smaller marked width chooses a true positive reserve parameter. -/
theorem native_mean_box (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {N Y l : ℝ} (hN : N ≤ 1/2) (hY : Y ≤ 1/2) (hl0 : 0 ≤ l)
    (hlcap : l < 3/20) (hlmean : l < (1-N-Y)/2) : UniformBox N Y l := by
  let gap := 1-N-Y-2*l
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let allowance := min (gap/(2*(1+10*l))) (((3/20 : ℝ)-l)*1143/1000)
  have hall : 0 < allowance := lt_min (div_pos hgap (by positivity)) (by positivity)
  obtain ⟨s,hs,hsall,hsmax,hsource⟩ :=
    Qrh.TwoSlot.AnchorContinuum.PositiveSource.arbitrarily_small hβ hall
  have hsfee : s*(2*(1+10*l)) < gap :=
    (lt_div_iff₀ (show 0 < 2*(1+10*l) by positivity)).1
      (hsall.trans_le (min_le_left _ _))
  have hscap : s < ((3/20 : ℝ)-l)*1143/1000 := hsall.trans_le (min_le_right _ _)
  apply uniformBox_of_source hsource
  intro x z t hbox
  obtain ⟨hx,hz,hpair,ht0,htl⟩ := hbox
  have hsum : x+z ≤ N+Y := by rcases hpair with h | h <;> linarith [h.1,h.2]
  have hxhi : x ≤ 1/2 := by rcases hpair with h | h; exact h.1.trans hN; exact h.1.trans hY
  have hzhi : z ≤ 1/2 := by rcases hpair with h | h; exact h.2.trans hY; exact h.2.trans hN
  dsimp [SourceFace.Admissible,Qrh.TwoSlot.AnchorContinuum.PositiveSource.face]
  simp only [mul_one]
  refine ⟨hx,hxhi,hz,hzhi,ht0,?_,?_⟩
  · nlinarith
  · have hlt := mul_le_mul_of_nonneg_left htl (show 0 ≤ 2+10*s by positivity)
    dsimp [gap] at hsfee
    nlinarith

/-- Actual P.2 caps have a positive capacity throughout the near-H sector,
including its genuine native arm. -/
theorem radius_width_pos {n y r : ℝ}
    (hy : y ≤ sourceY) (hn : n ≤ sourceRatio*y) (hr : (98/100 : ℝ) ≤ r) :
    0 < radiusWidth n y r := by
  have hr0 : 0 < r := (by norm_num : (0 : ℝ) < 98/100).trans_le hr
  have hyc : y/r ≤ 397/1000 := by
    apply (div_le_iff₀ hr0).2
    norm_num [sourceY] at hy
    nlinarith
  have hnc : n/r ≤ 457/1000 := by
    apply (div_le_iff₀ hr0).2
    norm_num [sourceY,sourceRatio] at hy hn
    nlinarith
  unfold radiusWidth continuedGain
  split_ifs with hs
  · have hg := native_collar_gain_lower (hs.trans (by norm_num [sourceY]))
    linarith
  · linarith

/-- Every actual bank radius is served by a genuine preceding source, or
by the original positive native reserve beyond its true seam. -/
theorem radius_bank_source (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {n y r : ℝ} (cover : EarlierCover OpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY)
    (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (hr0 : (98/100 : ℝ) ≤ r) (hr1 : r ≤ (H : ℝ)) :
    ∀ l : ℝ, 0 ≤ l → l < radiusWidth n y r → UniformBox (n/r) (y/r) l := by
  have hr : 0 < r := (by norm_num : (0 : ℝ) < 98/100).trans_le hr0
  by_cases hseam : y/r ≤ sourceY
  · have hsource := earlier_low_pair cover (source_domain.1.le.trans hy0) hn0 hn1 hr hr1 hseam
    simpa [radiusWidth,continuedGain,hseam,sourceWidth] using (show ∀ l, 0 ≤ l → l < sourceWidth (n/r) (y/r) → UniformBox (n/r) (y/r) l from hsource)
  · intro l hl0 hl
    have hN : n/r ≤ 1/2 := by
      apply (div_le_iff₀ hr).2
      norm_num [sourceY,sourceRatio] at hy1 hn1
      nlinarith
    have hY : y/r ≤ 1/2 := by
      apply (div_le_iff₀ hr).2
      norm_num [sourceY] at hy1
      nlinarith
    have hypos : 0 ≤ y := source_domain.1.le.trans hy0
    have hrle : r ≤ 1 := hr1.trans H_real_bounds.2.le
    have hyr : y ≤ y/r := (le_div_iff₀ hr).2 (mul_le_of_le_one_right hypos hrle)
    have hnr : y ≤ n/r := hyr.trans (div_le_div_of_nonneg_right hn0 hr.le)
    have hmean : l < (1-n/r-y/r)/2 := by simpa [radiusWidth,continuedGain,hseam] using hl
    have hcap : l < 3/20 := by norm_num [sourceY0] at hy0; linarith
    exact native_mean_box hβ hN hY hl0 hcap hmean

end
end QRH.Cycle092.LowActual
