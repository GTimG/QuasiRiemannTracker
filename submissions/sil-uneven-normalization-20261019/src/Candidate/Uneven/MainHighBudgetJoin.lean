/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainCellGeometry
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Uneven.MainAffineAmplification
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment

set_option autoImplicit false
namespace OAI.SevenEighths.MainHigh
noncomputable section
open Sil.Uneven.MainSource
open Target830.Source.Uneven
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open CenteredMomentEnergyFirstAnnularAdmission

/-- One numerical coefficient works for every original-width cell. -/
theorem geometry_affine_main_amplifier_bound (plane : Plane) (beta : ℝ)
    (hb : widthLo≤beta ∧ beta≤widthHi) :
    let a:=Sil.Uneven.MainSource.amp plane beta
    0≤(amplifierCap 2 0 1+6*a)/(a/2) ∧
      (amplifierCap 2 0 1+6*a)/(a/2)≤2000000 := by
  intro a
  have hg:=Sil.Uneven.MainSource.scheduling_guards plane hb
  have hlo : Sil.Uneven.MainSource.amplifierMinimum≤a:=hg.2.2.1
  have ha : 0<a:=lt_of_lt_of_le hg.2.1 hlo
  constructor
  · unfold amplifierCap; positivity
  · apply (div_le_iff₀ (show 0<a/2 by positivity)).mpr
    norm_num only [amplifierCap,max_eq_left (by norm_num : (0:ℝ)≤2)]
    norm_num [Sil.Uneven.MainSource.amplifierMinimum] at hlo
    linarith



end
end OAI.SevenEighths.MainHigh
