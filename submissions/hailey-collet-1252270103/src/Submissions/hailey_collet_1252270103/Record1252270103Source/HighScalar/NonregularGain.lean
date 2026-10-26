/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact fixed/tiny gains are paid by the three original family gaps. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.HighScalar.SingletonLoss
import Submissions.hailey_collet_1252270103.Record12518109Natural.SharpHighSector
import Submissions.hailey_collet_1252270103.Record12518109Gain.ExceptionalAdmission
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.HighScalar
noncomputable section
open OAI OAI.SevenEighths Record12518109Natural LocalMoment
open Record1252270103Finite PhysicalScalar

/-- The external tiny cutoff is D/50. The fixed branch uses both family
credits; no ordinary-density gain is substituted for either branch. -/
theorem nonregular_gap_payment (n low : Source) (high : Option Source)
    (sector : HighSector) (hsector : sector≠.regular)
    (b ν reserve D live frequency c d forced : ℝ)
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hD : 0≤D)
    (hc : 0≤c) (hd : 0≤d) (hforced : 0≤forced)
    (hfreq : 0≤frequency) (hlive : live≤D*b)
    (htiny : sector=.tiny →frequency≤D/50)
    (hg : ActualGaps n low high b ν reserve)
    (hrows : D*(sourceFReal n low b-(n.allowance:ℝ))≤frequency+2*c+2*d) :
    D*(sourceBase n low b ν-1)-ν*(c+d+forced)-
      sectorSharpGain sector ν live (D/50) frequency≤-D*((n.highFee:ℝ)+reserve) := by
  have hr0:=NaturalLowDensity.rho_lower hν1
  have hr : 1/6≤unmarkedDensity ν := by change 1/6≤Record12518109Gain.rho ν;linarith
  have he : High.rho ν=unmarkedDensity ν:=High.rho_eq_original ν
  have h0:=mul_le_mul_of_nonneg_left (hg.2 0) hD
  have h1:=mul_le_mul_of_nonneg_left (hg.2 1) hD
  have h2:=mul_le_mul_of_nonneg_left (hg.2 2) hD
  norm_num [familyGap] at h0 h1 h2
  simp only [he] at h0 h1 h2
  have hwidth : D*(sourceFReal n low b-(n.allowance:ℝ))≤frequency+2*(c+d+forced) := by linarith
  cases sector with
  | regular => exact (hsector rfl).elim
  | fixed =>
    have hp:=Record12518109Gain.fixed_cost_payment ν (unmarkedDensity ν) ν frequency live
      (D*(sourceFReal n low b-(n.allowance:ℝ))) (c+d+forced)
      (D*(1-sourceBase n low b ν)) (D*b) (D*((n.highFee:ℝ)+reserve))
      (by linarith) hr (by linarith) hfreq (by linarith) (by linarith only [hwidth]) hlive
      (by nlinarith only [h0]) (by nlinarith only [h1])
    simp only [sectorSharpGain,exceptionalHighGain,ite_true]
    nlinarith only [hp]
  | tiny =>
    have hq:=htiny rfl
    have hw:=mul_le_mul_of_nonneg_left (show D*(sourceFReal n low b-(n.allowance:ℝ))-D/50≤
      2*(c+d+forced) by linarith) (show 0≤ν by linarith)
    have hl:=mul_le_mul_of_nonneg_left hlive (show 0≤1-ν by linarith)
    simp only [sectorSharpGain]
    nlinarith only [h2,hw,hl]

/-- Nonregular singleton deletion has its exact paid volume loss. In both
sectors ν*S−gain is affine with coefficient one in S. -/
theorem nonregular_singleton_loss (sector : HighSector) (hs : sector≠.regular)
    (ν small full tiny forced : ℝ) (x : Fin 4→ℝ) :
    JointHigh.retainedHighExponent ν (sectorSharpGain sector ν small tiny)
      (lostWidthCoordinates x (forced+full-small))=
      JointHigh.retainedHighExponent ν (sectorSharpGain sector ν full tiny) x-
        ν*forced-(full-small) := by
  rw [retained_exponent_lost_width]
  cases sector with
  | regular => exact (hs rfl).elim
  | fixed => simp only [JointHigh.retainedHighExponent,sectorSharpGain,exceptionalHighGain,ite_true];ring
  | tiny => simp only [JointHigh.retainedHighExponent,sectorSharpGain];ring

lemma nonregular_singleton_subset_payment (sector : HighSector) (hs : sector≠.regular)
    (ν small full tiny forced : ℝ) (x : Fin 4→ℝ) (hwidth : small≤full) :
    JointHigh.retainedHighExponent ν (sectorSharpGain sector ν small tiny)
      (lostWidthCoordinates x (forced+full-small))≤
      JointHigh.retainedHighExponent ν (sectorSharpGain sector ν full tiny) x-ν*forced := by
  rw [nonregular_singleton_loss sector hs]
  linarith

end
end QRH.Record1252270103Source.HighScalar
#print axioms QRH.Record1252270103Source.HighScalar.nonregular_gap_payment
#print axioms QRH.Record1252270103Source.HighScalar.nonregular_singleton_loss
#print axioms QRH.Record1252270103Source.HighScalar.nonregular_singleton_subset_payment
