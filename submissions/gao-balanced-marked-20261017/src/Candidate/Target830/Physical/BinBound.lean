/- Target830 actual physical specialization, adapted from accepted .874836.
Predecessor attribution retained. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Target830.Physical.Geometry
import Candidate.Cycle25.Numerator.AmplitudeHolder

/- Adapted from Cycle25/Numerator/AmplitudeHolder.lean and its
akashlevy/QuasiRiemannTracker Apache-2.0 predecessor. The selected capacity
is the explicit Cycle63 schedule; the fourth moment is an input. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace OAI.SevenEighths.Target830.Physical.Packet
open OAI.SevenEighths.Target830 OAI.SevenEighths.Target830.Physical
open Cycle25.Numerator

theorem weighted_dilation_bin (plane : SourcePlane) {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (d U R q L v xi ann delta loss epsilon Ccount Cmoment : ℝ)
    (hd : dMinus ≤ d ∧ d ≤ dPlus)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta / 2) (hv : 0 ≤ v) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcard : (s.card : ℝ) ≤ Ccount * U^R)
    (hselected : ∀ i ∈ s, U^(q*scheduledCapacity plane d (2*(v+xi+ann))-loss) ≤ ‖Q i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : (∑ i ∈ s, ‖S i‖^4 * ‖Q i‖^2) ≤ Cmoment * U^(1+epsilon)) :
    U^(-delta*v/2) * (∑ i ∈ s, ‖S i * P i‖) ≤
      Ccount * Cmoment * U^(q*L-q*zeroCapacity plane d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2-
        2*dampingRate*delta*(v+xi+ann)) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hh := weighted_amplitude_bin s S Q P U R (q*L)
    (q*scheduledCapacity plane d (2*(v+xi+ann))-loss) epsilon Ccount Cmoment hU0 hc hm
    hcard hselected hfull henergy
  have hdelta : 0 ≤ delta := by linarith
  have hdamp := scheduled_capacity_damping plane hd (by positivity : 0 ≤ 2*(v+xi+ann)) hq hqdelta hdelta
  calc
    _ ≤ U^(-delta*v/2) *
        (Ccount*Cmoment*U^(q*L-(q*scheduledCapacity plane d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hU0.le _)
    _ = (Ccount*Cmoment) * (U^(-delta*v/2) *
        U^(q*L-(q*scheduledCapacity plane d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4)) := by ring
    _ = Ccount*Cmoment*U^(-delta*v/2+q*L-
        (q*scheduledCapacity plane d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4) := by
      rw [←Real.rpow_add hU0]
      congr 1
      congr 1
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by have hc0 := le_trans zero_le_one hc; have hm0 := le_trans zero_le_one hm; positivity)
      apply Real.rpow_le_rpow_of_exponent_le hU
      linarith


end OAI.SevenEighths.Target830.Physical.Packet

#print axioms OAI.SevenEighths.Target830.Physical.Packet.weighted_dilation_bin
