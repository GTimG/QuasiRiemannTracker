/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Join O.2 to the actual final PR141 stage, preserving its source objects. -/
import Candidate.C092.transport.TangentExtensionGeometry
import Candidate.C092.transport.TangentExtensionSeedData
import Candidate.C092.UpstreamPrivate.Local.Qrh.TwoSlot.AnchorZeroLoss.FiniteSource
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace QRH.Cycle092.TangentExtension.Certificate
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.TwoSlot.AnchorExtension.ChainData Qrh.TwoSlot.AnchorZeroLoss

theorem entry_anchor (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    AnchorAt (stage 0).R (stage 0).gain := by
  have hb := (Qrh.TwoSlot.AnchorZeroLoss.Certificate.Stage.ok_sound
    (Qrh.TwoSlot.AnchorZeroLoss.Certificate.local_checked 8191 (by norm_num))).1
  have hs := Qrh.TwoSlot.AnchorZeroLoss.Certificate.all_stage_outputs
    Qrh.MarkedAnchor.Price.pr103Face hβ (Reserve.reserveParametricSource hβ)
    (Driver.pr103_parent hβ) (Reserve.base_anchor_native hβ) 8191 (by norm_num)
    (oldStage 8191).left le_rfl (Rat.cast_le.mpr hb.2.2.2.1.le)
  rw [←Qrh.TwoSlot.AnchorZeroLoss.Certificate.cast_Y] at hs
  rw [entry_exact.1,entry_exact.2.1]
  exact hs

/-- The earlier affine HIGH line is paid by complete genuine old stages,
including the last one, at every real point above the new entry. -/
theorem entry_prior (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (x : ℝ) (hx : (stage 0).R ≤ x) (hx' : x ≤ 311/400) :
    ∃ gain : ℝ,0 ≤ gain ∧ (stage 0).a0-(stage 0).a1*x ≤ gain ∧ AnchorAt x gain := by
  have hxlo : (1467/2000:ℝ) ≤ x := by
    have he := congrArg (fun q : ℚ=>(q:ℝ)) first_R
    norm_num at he
    linarith
  obtain ⟨j,hj,hlo,hhi⟩ := Qrh.TwoSlot.AnchorZeroLoss.Certificate.full_cover hxlo hx'
  have hS := Qrh.TwoSlot.AnchorZeroLoss.Certificate.ordinary_hyp (oldStage j)
    (Qrh.TwoSlot.AnchorZeroLoss.Certificate.local_checked j hj) x hlo hhi
  have hA := Qrh.TwoSlot.AnchorZeroLoss.Certificate.all_stage_outputs
    Qrh.MarkedAnchor.Price.pr103Face hβ (Reserve.reserveParametricSource hβ)
    (Driver.pr103_parent hβ) (Reserve.base_anchor_native hβ) j hj x hlo hhi
  refine ⟨fY ((oldStage j).R:ℝ) (oldStage j).gain (oldStage j).cut x,hS.Y_nonneg,?_,hA⟩
  by_cases he : j=8191
  · subst j
    have hL : (((stage 0).line (oldStage 8191).left+pad:ℚ):ℝ) < (((oldStage 8191).Y (oldStage 8191).left:ℚ):ℝ) := Rat.cast_lt.mpr join_minorant_checked.1
    have hR : (((stage 0).line (oldStage 8191).R+pad:ℚ):ℝ) < (((oldStage 8191).Y (oldStage 8191).R:ℚ):ℝ) := Rat.cast_lt.mpr join_minorant_checked.2
    simp only [Stage.line,fline,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,
      Qrh.TwoSlot.AnchorZeroLoss.Certificate.cast_Y] at hL hR
    have hb := (Qrh.TwoSlot.AnchorZeroLoss.Certificate.Stage.ok_sound
      (Qrh.TwoSlot.AnchorZeroLoss.Certificate.local_checked 8191 (by norm_num))).1
    have hlt : ((oldStage 8191).left:ℝ)<(oldStage 8191).R := Rat.cast_lt.mpr hb.2.2.2.1
    have hh := QRH.Cycle092.TangentExtension.source_minorant_between hlt hlo hhi hL hR
    have hp : (0:ℝ)<(pad:ℝ) := by norm_num [pad]
    linarith
  · have hh := Qrh.TwoSlot.AnchorZeroLoss.Certificate.previous_minorant 8191 (by norm_num) j
      (by omega) x hlo hhi
    have ha0 := congrArg (fun q : ℚ=>(q:ℝ)) entry_exact.2.2.1
    have ha1 := congrArg (fun q : ℚ=>(q:ℝ)) entry_exact.2.2.2
    unfold Qrh.TwoSlot.AnchorZeroLoss.sourceLine at hh
    rw [←ha0,←ha1] at hh
    have hp : (0:ℝ)<(Qrh.TwoSlot.AnchorZeroLoss.Certificate.pad:ℝ) := by norm_num [Qrh.TwoSlot.AnchorZeroLoss.Certificate.pad]
    linarith

end QRH.Cycle092.TangentExtension.Certificate
#print axioms QRH.Cycle092.TangentExtension.Certificate.entry_anchor
#print axioms QRH.Cycle092.TangentExtension.Certificate.entry_prior
