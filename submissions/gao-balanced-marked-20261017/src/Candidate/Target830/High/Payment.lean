import Candidate.Target830.High.Bins
import Candidate.Target830.Kernel.ConservedWidthPayment

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open Cycle63InitialMass

/-- Retained-HIGH payment on the actual four-coordinate exponent, with
all six channel hypotheses explicit. The source valuation/budget proof is
an argument; it is not an axiom or a claimed scalar-only analytic supplier. -/
theorem retained_high_payment (delta : ℝ) (x : Fin 4→ℝ)
    (side target base fee gamma removed supply live frequency core tail : ℝ)
    (hdelta : 31/50 ≤ delta) (hdelta' : delta ≤ 7/10)
    (hgamma : 0≤gamma) (hremoved : 0≤removed)
    (hsupply : 0≤supply) (hfrequency : 2*supply≤frequency)
    (hlive : 0≤live) (hcore : 0≤core) (hcore' : core≤1) (hx2 : 0≤x 2)
    (hliveSupply : supply≤removed+live)
    (hfreqSupply : frequency≤2*removed+core*x 2)
    (htail : 0≤tail) (hrootSlope : 2*tail≤gamma)
    (hsource : highExponentValue delta x≤side+target-base-gamma*removed)
    (hr : fee≤base+gamma*supply)
    (h0 : fee≤base+Marked830.VariableSupply.phi delta*supply)
    (h1 : fee≤base+Marked830.VariableSupply.phi delta*
      (2*supply+Marked830.VariableSupply.plainCap delta*frequency)/3)
    (h2 : fee≤base+Marked830.VariableSupply.phi delta*
      (2*Marked830.VariableSupply.cap delta*frequency+supply)/3)
    (h3 : fee≤base+Marked830.VariableSupply.phi delta*
      (2*Marked830.VariableSupply.cap delta+Marked830.VariableSupply.plainCap delta)*frequency/3)
    (ht : fee≤base+tail*frequency) :
    retainedHighExponent delta
      (fun q=>min (Marked830.VariableSupply.physicalGain delta live (core*q)) (tail*q)) x≤
      side+target-fee := by
  have hp := ConservedWidthPayment.six_channel_payment hgamma hremoved
    (Marked830.VariableSupply.phi_nonneg hdelta hdelta')
    (Marked830.VariableSupply.cap_bounds hdelta hdelta').1.le
    (Marked830.VariableSupply.plainCap_nonneg hdelta hdelta')
    hsupply hfrequency hlive (mul_nonneg hcore hx2) hliveSupply hfreqSupply
    htail hrootSlope hr h0 h1 h2 h3 ht
  have htailMono : tail*(core*x 2)≤tail*x 2 := by
    exact mul_le_mul_of_nonneg_left
      (by nlinarith : core*x 2≤x 2) htail
  have hm := min_le_min_left
    (Marked830.VariableSupply.physicalGain delta live (core*x 2)) htailMono
  change fee≤base+gamma*removed+
    min (Marked830.VariableSupply.physicalGain delta live (core*x 2)) (tail*(core*x 2)) at hp
  unfold retainedHighExponent
  linarith

end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.retained_high_payment
