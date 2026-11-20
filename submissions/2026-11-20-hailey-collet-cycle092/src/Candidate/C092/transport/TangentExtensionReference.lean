/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Apply the genuine new reference source to the actual .72 stage datum. -/
import Candidate.C092.transport.TangentExtensionOrdinaryStage
import Candidate.C092.transport.ReferenceLaneFine
set_option autoImplicit false
noncomputable section
namespace QRH.Cycle092.TangentExtension
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.TwoSlot.AnchorExtension.ChainData

def parentFace : ParentFace where
  B₀ := 99/100
  L₀ := 23/10
  c₀ := 149/1000
  hB := by norm_num
  hL := by norm_num
  hc := by norm_num
  hcross := by norm_num

theorem parent_source (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    QRH.Record1252270103Source.GlobalSource parentFace.B₀ parentFace.L₀ parentFace.c₀ :=
  ReferenceFine.parent_source hβ

/-- The operational .001 cap collar is chosen before the live arithmetic
objects. Its source energy is supplied by the new reference theorem. -/
theorem reference_lane_zero (F : ParentFace) {R z k r : ℝ}
    (hS : StageHyp R z k r) (high : QRH.SilDensitySplit.CubeFree.Price)
    (hk0 : 0 ≤ k) {β : ℝ} (hβ : 0 < β) (_hβhi : β ≤ 1/1000) :
    Ordinary.Reference.ReferenceLaneFine (stageData F R z k r β high hk0 hβ) := by
  apply ReferenceFine.reference_lane_fine (ρ:=1/1000)
  have hc := stage_c_eq F high hk0 (r:=r) (z:=z) (R:=R) hβ
  have hlo := hS.S_lower
  have hcap := hS.g2
  refine ⟨by norm_num,by norm_num [stageData],?_,?_,?_,?_⟩
  · rw [hc];linarith [hS.hr.2,hS.hR.2]
  · change 7/50+1/2+ReferenceFine.Lref* _+1/1000 ≤ ReferenceFine.Bref
    rw [hc]
    norm_num [ReferenceFine.Lref,ReferenceFine.Bref]
    linarith
  · rw [hc];norm_num [ReferenceFine.cref];linarith
  · change 7/50+ _ ≤ 1
    rw [hc];linarith

end QRH.Cycle092.TangentExtension
#print axioms QRH.Cycle092.TangentExtension.reference_lane_zero
