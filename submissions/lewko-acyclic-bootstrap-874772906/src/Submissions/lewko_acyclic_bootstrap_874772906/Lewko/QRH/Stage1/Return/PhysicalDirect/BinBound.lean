/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Adapted from Gao Target830 physical closure, inherited OpenAI/Hailey Collet/Akash Levy; Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.Schedule
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.PhysicalDirect.Geometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle25.Numerator.AmplitudeHolder
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open scoped BigOperators
namespace QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect.Packet
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.LewkoStage1Return.GenericArithmetic
open QRH.LewkoStage1Return.GenericArithmetic QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect
open Cycle25.Numerator

theorem weighted_dilation_bin {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (d U R q L v xi ann delta loss epsilon Ccount Cmoment : ℝ)
    (hd : dm ≤ d ∧ d ≤ dp)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta / 2) (hv : 0 ≤ v) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcard : (s.card : ℝ) ≤ Ccount * U^R)
    (hselected : ∀ i ∈ s, U^(q*scheduledCapacity d (2*(v+xi+ann))-loss) ≤ ‖Q i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : (∑ i ∈ s, ‖S i‖^4 * ‖Q i‖^2) ≤ Cmoment * U^(1+epsilon)) :
    U^(-delta*v/2) * (∑ i ∈ s, ‖S i * P i‖) ≤
      Ccount * Cmoment * U^(q*L-q*zeroCapacity d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2-
        2*dampingRate*delta*(v+xi+ann)) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hh := weighted_amplitude_bin s S Q P U R (q*L)
    (q*scheduledCapacity d (2*(v+xi+ann))-loss) epsilon Ccount Cmoment hU0 hc hm
    hcard hselected hfull henergy
  have hdelta : 0 ≤ delta := by linarith
  have hdamp := scheduled_capacity_damping hd (by positivity : 0 ≤ 2*(v+xi+ann)) hq hqdelta hdelta
  calc
    _ ≤ U^(-delta*v/2) *
        (Ccount*Cmoment*U^(q*L-(q*scheduledCapacity d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hU0.le _)
    _ = (Ccount*Cmoment) * (U^(-delta*v/2) *
        U^(q*L-(q*scheduledCapacity d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4)) := by ring
    _ = Ccount*Cmoment*U^(-delta*v/2+q*L-
        (q*scheduledCapacity d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4) := by
      rw [←Real.rpow_add hU0]
      congr 1
      congr 1
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by have hc0 := le_trans zero_le_one hc; have hm0 := le_trans zero_le_one hm; positivity)
      apply Real.rpow_le_rpow_of_exponent_le hU
      linarith


end QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect.Packet

#print axioms QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect.Packet.weighted_dilation_bin
