/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original shortened ordinary scales supply the actual P4 length. -/
import Candidate.C092.transport.RegularColoredTerminalLeafOriginalScale
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open OAI.SevenEighths.Cycle61Moment
open CenteredMomentNaturalFixedRaySource CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open QRH.Record12518109Source QRH.Record12518109Existence
open CenteredMomentEnergyBands
open QRH.Cycle092.MediumReplace.Source

/-- A componentwise cap bounds the native clamped length, including every
positive subunit shortening. -/
theorem terminal_original_length_cap {U X cap : ℝ} (hU : 1 < U) (hc : 0 ≤ cap)
    (hX : X ≤ U^cap) : length U X ≤ cap := by
  have h := QRH.SilDensitySplit.CubeFree.Packet.Grouped.length_mono U X (U^cap) hU hX
  have hp : 1 ≤ U^cap := Real.one_le_rpow hU.le hc
  simpa only [length,max_eq_right hp,Real.logb_rpow (zero_lt_one.trans hU) (ne_of_gt hU)] using h

/-- P4's short length is the actual original log length. It is not the
witness inverse dyad or an artificially enlarged upper cap. -/
theorem terminal_original_short_length {U d dmin Y y R : ℝ}
    (hU : 1 < U) (hdmin : 0 < dmin) (hd : dmin ≤ d) (hy : 0 ≤ y)
    (hY : 1 ≤ Y) (hYcap : Y ≤ U^y) (hR : y/dmin ≤ R) :
    let r := Real.logb (U^d) Y;
      0 ≤ r ∧ r ≤ R ∧ d*r ≤ y ∧ (U^d)^r=Y := by
  intro r
  have hd0 : 0 < d := hdmin.trans_le hd
  have hUd : 1 < U^d := Real.one_lt_rpow hU hd0
  have hr0 : 0 ≤ r := Real.logb_nonneg hUd hY
  have hlen := terminal_original_length_cap hU hy hYcap
  have hrel := length_rpow_base U Y d (zero_lt_one.trans hU)
  have hr : r=length U Y/d := by
    simpa only [length,max_eq_right hY] using hrel
  have hry : r ≤ y/d := by
    rw [hr]
    exact div_le_div_of_nonneg_right hlen hd0.le
  refine ⟨hr0,hry.trans ((div_le_div_of_nonneg_left hy hdmin hd).trans hR),?_,?_⟩
  · simpa only [mul_comm] using (le_div_iff₀ hd0).mp hry
  · exact terminal_actual_short_scale hUd (zero_lt_one.trans_le hY)

#print axioms terminal_original_length_cap
#print axioms terminal_original_short_length
end
end QRH.Cycle092.RegularColoredForward
