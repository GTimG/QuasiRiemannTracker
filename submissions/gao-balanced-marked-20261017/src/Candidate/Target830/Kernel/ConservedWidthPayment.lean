import Candidate.Target830.Kernel.ExactMarkedGain
import Mathlib.Tactic

/-! Conserved-width scalar payment for the exact asymmetric marked gain.
Only scalar transport is asserted. No analytic source provider or endpoint
is supplied by this module. All analytic payment hypotheses remain explicit. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace OAI.SevenEighths.ConservedWidthPayment

open ExactMarkedGain

/-- One nonnegative affine live/frequency branch, with removed width charged. -/
theorem affine_payment {gamma R a b S F : ℝ}
    (hgamma : 0 ≤ gamma) (hR : 0 ≤ R) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hS : 0 ≤ S) (hF : 2*S ≤ F) :
    min (gamma*S) (a*S+b*F) ≤
      gamma*R+a*max (S-R) 0+b*max (F-2*R) 0 := by
  by_cases hRS : S ≤ R
  · have hg := mul_le_mul_of_nonneg_left hRS hgamma
    have hposA : 0 ≤ a*max (S-R) 0 := mul_nonneg ha (le_max_right _ _)
    have hposB : 0 ≤ b*max (F-2*R) 0 := mul_nonneg hb (le_max_right _ _)
    exact (min_le_left _ _).trans (by linarith)
  · have hRS' : R ≤ S := le_of_lt (lt_of_not_ge hRS)
    rw [max_eq_left (by linarith : 0 ≤ S-R),
      max_eq_left (by linarith : 0 ≤ F-2*R)]
    by_cases hslope : a+2*b ≤ gamma
    · have hs := mul_nonneg (by linarith : 0 ≤ gamma-a-2*b) hR
      exact (min_le_right _ _).trans (by nlinarith)
    · have hs := mul_nonneg (by linarith : 0 ≤ a+2*b-gamma)
        (by linarith : 0 ≤ S-R)
      have htail := mul_nonneg hb (by linarith : 0 ≤ F-2*S)
      exact (min_le_left _ _).trans (by nlinarith)

/-- The large-root branch is retained whenever its slope is at most half
of the removed-width payment. -/
theorem root_payment {gamma R t F : ℝ}
    (hR : 0 ≤ R) (ht : 0 ≤ t) (hslope : 2*t ≤ gamma) :
    t*F ≤ gamma*R+t*max (F-2*R) 0 := by
  have hm := le_max_left (F-2*R) 0
  have hmul := mul_le_mul_of_nonneg_left hm ht
  have hs := mul_nonneg (by linarith : 0 ≤ gamma-2*t) hR
  nlinarith

/-- Exact asymmetric gain is the minimum of its four affine forms.
No coarser rate-times-min replacement occurs. -/
theorem scaledGain_eq_min_four (phi u v S F : ℝ) (hphi : 0 ≤ phi) :
    scaledGain phi u v S F =
      min (phi*S)
        (min (phi*(2*S+v*F)/3)
          (min (phi*(2*u*F+S)/3) (phi*(2*u+v)*F/3))) := by
  dsimp [scaledGain, gain]
  simp only [min_def]
  split_ifs <;> nlinarith

/-- Five finite scalar channels pay the exact marked branch. -/
theorem exact_gain_payment {gamma R phi u v S F base fee : ℝ}
    (hgamma : 0 ≤ gamma) (hR : 0 ≤ R) (hphi : 0 ≤ phi)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hS : 0 ≤ S) (hF : 2*S ≤ F)
    (hremoved : fee ≤ base+gamma*S)
    (hlinear : fee ≤ base+phi*S)
    (hplain : fee ≤ base+phi*(2*S+v*F)/3)
    (hinverse : fee ≤ base+phi*(2*u*F+S)/3)
    (hcapped : fee ≤ base+phi*(2*u+v)*F/3) :
    fee ≤ base+gamma*R+
      scaledGain phi u v (max (S-R) 0) (max (F-2*R) 0) := by
  have pay (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hbranch : fee ≤ base+a*S+b*F) :
      fee ≤ base+gamma*R+a*max (S-R) 0+b*max (F-2*R) 0 := by
    have hm : fee-base ≤ min (gamma*S) (a*S+b*F) :=
      le_min (by linarith) (by linarith)
    have hp := affine_payment hgamma hR ha hb hS hF
    linarith
  have h0 := pay phi 0 hphi (by norm_num) (by nlinarith [hlinear])
  have h1 := pay (2*phi/3) (phi*v/3) (by positivity) (by positivity)
    (by nlinarith [hplain])
  have h2 := pay (phi/3) (2*phi*u/3) (by positivity) (by positivity)
    (by nlinarith [hinverse])
  have h3 := pay 0 (phi*(2*u+v)/3) (by norm_num) (by positivity)
    (by nlinarith [hcapped])
  rw [scaledGain_eq_min_four _ _ _ _ _ hphi]
  have hmin : fee-(base+gamma*R) ≤
      min (phi*max (S-R) 0)
        (min (phi*(2*max (S-R) 0+v*max (F-2*R) 0)/3)
          (min (phi*(2*u*max (F-2*R) 0+max (S-R) 0)/3)
            (phi*(2*u+v)*max (F-2*R) 0/3))) := by
    refine le_min ?_ (le_min ?_ (le_min ?_ ?_)) <;> nlinarith
  linarith

/-- All six channels give a conserved-width payment, including the root
alternative, on the actual remaining live width and frequency. -/
theorem six_channel_payment {gamma R phi u v S F live freq t base fee : ℝ}
    (hgamma : 0 ≤ gamma) (hR : 0 ≤ R) (hphi : 0 ≤ phi)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hS : 0 ≤ S) (hF : 2*S ≤ F)
    (hlive : 0 ≤ live) (hfreq : 0 ≤ freq)
    (hsupply : S ≤ R+live) (hfrequency : F ≤ 2*R+freq)
    (ht : 0 ≤ t) (hrootSlope : 2*t ≤ gamma)
    (hremoved : fee ≤ base+gamma*S)
    (hlinear : fee ≤ base+phi*S)
    (hplain : fee ≤ base+phi*(2*S+v*F)/3)
    (hinverse : fee ≤ base+phi*(2*u*F+S)/3)
    (hcapped : fee ≤ base+phi*(2*u+v)*F/3)
    (hroot : fee ≤ base+t*F) :
    fee ≤ base+gamma*R+min (scaledGain phi u v live freq) (t*freq) := by
  have hL : max (S-R) 0 ≤ live := max_le (by linarith) hlive
  have hV : max (F-2*R) 0 ≤ freq := max_le (by linarith) hfreq
  have hg := exact_gain_payment hgamma hR hphi hu hv hS hF
    hremoved hlinear hplain hinverse hcapped
  have hmL := scaledGain_mono_width phi u v (max (F-2*R) 0) hphi hL
  have hmV := scaledGain_mono_scale phi u v live hphi hu hv hV
  have hgain : fee-(base+gamma*R) ≤ scaledGain phi u v live freq := by
    linarith
  have hr := root_payment (gamma := gamma) (R := R) (t := t) (F := F)
    hR ht hrootSlope
  have hm := mul_le_mul_of_nonneg_left hV ht
  have hroot' : fee-(base+gamma*R) ≤ t*freq := by linarith
  have hmin := le_min hgain hroot'
  linarith

end OAI.SevenEighths.ConservedWidthPayment
end

#print axioms OAI.SevenEighths.ConservedWidthPayment.affine_payment
#print axioms OAI.SevenEighths.ConservedWidthPayment.root_payment
#print axioms OAI.SevenEighths.ConservedWidthPayment.scaledGain_eq_min_four
#print axioms OAI.SevenEighths.ConservedWidthPayment.exact_gain_payment
#print axioms OAI.SevenEighths.ConservedWidthPayment.six_channel_payment
