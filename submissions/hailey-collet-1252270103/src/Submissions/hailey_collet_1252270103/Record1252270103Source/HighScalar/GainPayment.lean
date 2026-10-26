/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Both literal gain alternatives pay first, second and forced common losses. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalReserve
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.Rescale
import Submissions.hailey_collet_1252270103.Record1252270103Source.NaturalLowDensity.Homogeneous
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.HighScalar
noncomputable section
open Record1252270103Finite PhysicalScalar

def gainAt (high : Option Source) (ν S F : ℝ) : ℝ :=
  match high with
  | none => Record12518109Gain.gain ν S F
  | some h => High.gain ν (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ) S F

def GainParameters (high : Option Source) : Prop :=
  ∀h∈high,(22/23:ℝ)≤h.B ∧(h.B:ℝ)≤1 ∧1<(h.L:ℝ) ∧0≤(h.cap:ℝ) ∧(h.cap:ℝ)≤1

lemma natural_common_gain_reserve {ν S L Q F c d : ℝ}
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hc : 0≤c) (hd : 0≤d)
    (hslots : S≤L+c+d) (hrows : F≤Q+2*c+2*d) :
    Record12518109Gain.gain ν S F-Record12518109Gain.gain ν L Q-ν*(c+d)≤-(c+d)/12 := by
  have hm := NaturalLowDensity.gain_mono hν0 hν1 hslots hrows
  have hs := NaturalLowDensity.gain_slot_loss (F:=Q+2*c+2*d) hν0 hν1
    (show L≤L+c+d by linarith)
  have hr := NaturalLowDensity.gain_width_loss (S:=L) hν0 hν1
    (show Q≤Q+2*c+2*d by linarith)
  have hcoef := (NaturalLowDensity.coefficient_bounds hν0 hν1).2.2.2.2.2.2
  have hphi : Record12518109Gain.phi ν≤ν-1/4 := by
    unfold Record12518109Gain.phi
    apply (div_le_iff₀ (show 0<5-2*ν by linarith)).mpr
    nlinarith [sq_nonneg (ν-1/2)]
  have hp := mul_le_mul_of_nonneg_right hphi (show 0≤c+d by linarith)
  have hh := mul_le_mul_of_nonneg_right hcoef.le (show 0≤2*c+2*d by linarith)
  nlinarith

lemma gainAt_common_reserve (high : Option Source) (hp : GainParameters high)
    {ν S L Q F c d : ℝ} (hν0 : 1/2≤ν) (hν1 : ν≤3/4)
    (hc : 0≤c) (hd : 0≤d) (hslots : S≤L+c+d) (hrows : F≤Q+2*c+2*d) :
    gainAt high ν S F-gainAt high ν L Q-ν*(c+d)≤-(c+d)/12 := by
  cases high with
  | none => exact natural_common_gain_reserve hν0 hν1 hc hd hslots hrows
  | some h =>
    obtain ⟨hB,hB',hL,hh,hh'⟩:=hp h (by simp)
    exact High.common_gain_reserve hν0 hν1 hB hB' hL hh hh' hc hd hslots hrows

lemma gainAt_homogeneous (high : Option Source) (ν S F D : ℝ)
    (hν : 0≤ν) (hD : 0≤D) : gainAt high ν (D*S) (D*F)=D*gainAt high ν S F := by
  cases high with
  | none => exact NaturalLowDensity.gain_homogeneous ν S F D hD
  | some h => exact High.gain_homogeneous hν hD

lemma actual_gap_gain_payment (n low : Source) (high : Option Source)
    (hp : GainParameters high) (b ν reserve D live frequency c d forced : ℝ)
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hD : 0≤D)
    (hc : 0≤c) (hd : 0≤d) (hforced : 0≤forced)
    (hg : ActualGaps n low high b ν reserve)
    (hslots : D*(b-2*(n.allowance:ℝ))≤live+c+d+forced)
    (hrows : D*(sourceFReal n low b-(n.allowance:ℝ))≤frequency+2*c+2*d) :
    D*(sourceBase n low b ν-1)-ν*(c+d+forced)-gainAt high ν live frequency≤
      -D*((n.highFee:ℝ)+reserve)-(c+d+forced)/12 := by
  have hr : D*(sourceFReal n low b-(n.allowance:ℝ))≤frequency+2*c+2*(d+forced) := by linarith
  have hs : D*(b-2*(n.allowance:ℝ))≤live+c+(d+forced) := by linarith
  have hpmt:=gainAt_common_reserve high hp hν0 hν1 hc (show 0≤d+forced by linarith) hs hr
  rw [gainAt_homogeneous high ν _ _ D (by linarith) hD] at hpmt
  have he : gainAt high ν (b-2*(n.allowance:ℝ)) (sourceFReal n low b-(n.allowance:ℝ))=
      selectedGain n low high b ν := by cases high <;> rfl
  rw [he] at hpmt
  have hg':=mul_le_mul_of_nonneg_left hg.1 hD
  nlinarith

end
end QRH.Record1252270103Source.HighScalar
#print axioms QRH.Record1252270103Source.HighScalar.natural_common_gain_reserve
#print axioms QRH.Record1252270103Source.HighScalar.gainAt_common_reserve
#print axioms QRH.Record1252270103Source.HighScalar.actual_gap_gain_payment
