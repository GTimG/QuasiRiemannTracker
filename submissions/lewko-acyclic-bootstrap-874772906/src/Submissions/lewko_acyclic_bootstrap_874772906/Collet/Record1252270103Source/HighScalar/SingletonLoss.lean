/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Deleting equality-block slots keeps the exact corresponding volume loss. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.HighScalar.LabelPayment
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.HighScalar
noncomputable section
open OAI OAI.SevenEighths Record12518109Natural.JointHigh Cycle61InitialMass
open Record1252270103Finite

lemma gainAt_weighted_width_mono (high : Option Source) (hp : GainParameters high)
    {ν small full Q : ℝ} (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hwidth : small≤full) :
    ν*small-gainAt high ν small Q≤ν*full-gainAt high ν full Q := by
  cases high with
  | none => exact NaturalLowDensity.weighted_exponent_mono hν0 hν1 hwidth
  | some h =>
    obtain ⟨_,_,hL,_,_⟩:=hp h (by simp)
    have hphi : High.phi ν≤ν := by
      unfold High.phi
      apply (div_le_iff₀ (show 0<High.densityDenom ν by dsimp [High.densityDenom];linarith)).mpr
      dsimp [High.w,High.densityDenom]
      nlinarith
    have hg:=High.gain_slot_loss (B:=(h.B:ℝ)) (h:=(h.cap:ℝ)) (Q:=Q) hν0 hν1 hL hwidth
    have hm:=mul_le_mul_of_nonneg_right hphi (sub_nonneg.mpr hwidth)
    dsimp only [gainAt]
    nlinarith

/-- The coordinate is the original one with only the paid marked-width
normalization removed. The frequency and counted missing radical are fixed. -/
def lostWidthCoordinates (x : Fin 4→ℝ) (loss : ℝ) : Fin 4→ℝ :=
  ![x 0,x 1,x 2,x 3-loss]

lemma retained_exponent_lost_width (ν : ℝ) (gain : ℝ→ℝ) (x : Fin 4→ℝ) (loss : ℝ) :
    retainedHighExponent ν gain (lostWidthCoordinates x loss)=retainedHighExponent ν gain x-ν*loss := by
  change x 0+x 1+LocalMoment.unmarkedDensity ν*x 2+ν*(x 3-loss)-gain (x 2)=
    (x 0+x 1+LocalMoment.unmarkedDensity ν*x 2+ν*x 3-gain (x 2))-ν*loss
  ring

theorem full_singleton_subset_payment (high : Option Source) (hp : GainParameters high)
    {ν small full forced : ℝ} (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hwidth : small≤full)
    (x : Fin 4→ℝ) :
    retainedHighExponent ν (gainAt high ν small)
      (lostWidthCoordinates x (forced+full-small))≤
      retainedHighExponent ν (gainAt high ν full) x-ν*forced := by
  rw [retained_exponent_lost_width]
  have hm:=gainAt_weighted_width_mono high hp hν0 hν1 hwidth (Q:=x 2)
  dsimp only [retainedHighExponent]
  nlinarith

end
end QRH.Record1252270103Source.HighScalar
#print axioms QRH.Record1252270103Source.HighScalar.gainAt_weighted_width_mono
#print axioms QRH.Record1252270103Source.HighScalar.retained_exponent_lost_width
#print axioms QRH.Record1252270103Source.HighScalar.full_singleton_subset_payment
