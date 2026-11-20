/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The sharp original coefficient-dilation payment: actual affine/clipped schedule,
full two-times source shift, quarter of the original density times dilation. -/
import Candidate.C092.transport.DirectActualDilation
import Candidate.C092.transport.SelectedNonfloorBins
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
namespace QRH.Cycle092.MixedTicketTails

/-- The genuine full source schedule loses at most one normalized width per
unit coefficient dilation. The physical source cap is preserved by clipping. -/
theorem quarter_capacity_damping {y s d v q delta : ℝ}
    (hs : 0 ≤ s) (hv : 0 ≤ v) (hq : 0 ≤ q) (hqd : q ≤ delta/2) :
    q*Physical.Selection.zeroCapacity y s d/2  ≤  delta*v/4+
      q*Physical.Selection.scheduledCapacity y s d (2*v)/2 := by
  have hloss := Physical.Selection.clipped_shift_loss hs hv (y:=y) (d:=d)
  have hden : 0 < 2+10*s := by positivity
  have hdiv : 2*v/(2+10*s) ≤ v := (div_le_iff₀ hden).mpr (by nlinarith [mul_nonneg hs hv])
  have hsched : Physical.Selection.clippedCapacity y s d v ≤ 
      Physical.Selection.scheduledCapacity y s d (2*v) := by
    simpa only [Physical.Selection.scheduledCapacity,show 2*v/2=v by ring] using
      (le_max_right 0 (Physical.Selection.clippedCapacity y s d v))
  have hdrop : Physical.Selection.zeroCapacity y s d-
      Physical.Selection.scheduledCapacity y s d (2*v) ≤ v := by linarith
  have hpay := mul_le_mul_of_nonneg_left hdrop hq
  have hamp := mul_le_mul_of_nonneg_right hqd hv
  nlinarith

/-- The true original weighted first-norm bin earns delta*v/4, with only the
explicit source-bin and annulus collars on the other side. -/
theorem weighted_bin_quarter {ι : Type*} (rows : Finset ι) (S Q P : ι→ℂ)
    (y cost d U R q L v xi ann delta loss epsilon Ccount Cmoment : ℝ)
    (hcost : 0 ≤ cost) (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hq : 0 ≤ q) (hqd : q ≤ delta/2) (hv : 0 ≤ v) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcard : (rows.card:ℝ) ≤ Ccount*U^R)
    (hselected : ∀i∈rows,U^(q*Physical.Selection.scheduledCapacity y cost d
      (2*(v+xi+ann))-loss) ≤ ‖Q i‖)
    (hfull : ∀i∈rows,‖P i‖ ≤ U^(q*L))
    (henergy : (∑i∈rows,‖S i‖^4*‖Q i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    U^(-delta*v/2)*(∑i∈rows,‖S i*P i‖)  ≤ 
      Ccount*Cmoment*U^(q*L-q*Physical.Selection.zeroCapacity y cost d/2+
        (3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/4-delta*v/4) := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hh := DirectEnergy.Packet.weighted_amplitude_bin rows S Q P U R (q*L)
    (q*Physical.Selection.scheduledCapacity y cost d (2*(v+xi+ann))-loss)
    epsilon Ccount Cmoment hU0 hc hm hcard hselected hfull henergy
  have hdamp := quarter_capacity_damping (y:=y) (d:=d) hcost
    (by positivity : 0 ≤ v+xi+ann) hq hqd
  calc
    _  ≤  U^(-delta*v/2)*(Ccount*Cmoment*
        U^(q*L-(q*Physical.Selection.scheduledCapacity y cost d (2*(v+xi+ann))-loss)/2+
          (3*R+1+epsilon)/4)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = Ccount*Cmoment*U^(-delta*v/2+q*L-
        (q*Physical.Selection.scheduledCapacity y cost d (2*(v+xi+ann))-loss)/2+
        (3*R+1+epsilon)/4) := by
      rw [←mul_assoc,mul_comm (U^(-delta*v/2)),mul_assoc,←Real.rpow_add hU0]
      congr 2
      ring
    _  ≤  _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU (by linarith)) (by positivity)

#print axioms quarter_capacity_damping
#print axioms weighted_bin_quarter
end QRH.Cycle092.MixedTicketTails
