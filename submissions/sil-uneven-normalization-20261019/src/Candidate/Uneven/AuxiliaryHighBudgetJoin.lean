import Candidate.Uneven.AuxiliaryHighParameters
import Candidate.Target830.High.BalancedMass
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryCellGeometry
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Uneven.AuxiliaryAffineAmplification
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryHigh
open TargetHigh830 SaturatedPlain
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open OAI.SevenEighths.AuxiliaryPhysical
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open CenteredMomentEnergyFirstAnnularAdmission

/-- One numerical coefficient works for every original-width cell. -/
theorem geometry_affine_main_amplifier_bound  (beta : ℝ)
    (hb : Sil.Uneven.AuxiliarySource.widthLo≤beta ∧ beta≤Sil.Uneven.AuxiliarySource.widthHi) :
    let a:=Sil.Uneven.AuxiliarySource.amp beta
    0≤(amplifierCap 2 0 1+6*a)/(a/2) ∧
      (amplifierCap 2 0 1+6*a)/(a/2)≤2000000 := by
  intro a
  have hg:=Sil.Uneven.AuxiliarySource.scheduling_guards  hb
  have hlo : Sil.Uneven.AuxiliarySource.amplifierMinimum≤a:=hg.2.2.1
  have ha : 0<a:=lt_of_lt_of_le hg.2.1 hlo
  constructor
  · unfold amplifierCap; positivity
  · apply (div_le_iff₀ (show 0<a/2 by positivity)).mpr
    norm_num only [amplifierCap,max_eq_left (by norm_num : (0:ℝ)≤2)]
    norm_num [Sil.Uneven.AuxiliarySource.amplifierMinimum] at hlo
    linarith



end
end OAI.SevenEighths.AuxiliaryHigh
