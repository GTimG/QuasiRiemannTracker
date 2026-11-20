/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Expose the authentic E49 tangent rectangle counts at an arbitrary cutoff. -/
import Candidate.C092.transport.PacketJoinE49Count
import Candidate.C092.transport.MixedCenteredFaces
import Candidate.C092.transport.MixedOffsetBankTransition
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount
noncomputable section
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorBatch
open QRH.Record12518109Count Cycle25ProbeFinalAssembly
open QRH.Cycle092.PacketJoinE49
open Qrh.MarkedAnchor.Return (fiber_inverse_width_count fiber_ordinary_width_count)
local notation "O" => HeckeFamily.O

/-- Both bounds are derived from real improved rectangle moments, with their
literal source error and selected-width decrement. This helper is consumed
by the actual source supplier below, not left as an analytic endpoint premise. -/
theorem rectangle_counts {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
    {U a ε tstar T allowance ν C height εm : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (hU : 1<U) (ha : 1/2<a) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i:ℕ)*T≤height)
    (hν : 0<ν) (hνhi : ν≤1/10000000)
    (himp : ImprovedMoments Return.line F ν C height εm)
    (hrlo : anchorLeft≤F.r) (hrhi : F.r≤anchorTop)
    (hmlo : anchorLeft≤2*F.m) (hmhi : 2*F.m≤anchorTop) :
    (F.rows.card:ℝ)≤(12*(1+height)*C)*
      U^(1-(2*a-1)*(Return.aI (F.q/(2*a-1))+Return.kI (F.q/(2*a-1))*F.r)+
        2*F.q*ν+2*ε+(2*a-1)*F.mesh+εm) ∧
    (F.rows.card:ℝ)≤(192*(1+height)*C)*
      U^(1-(2*a-1)*(Return.aI (F.q/(2*a-1))+2*Return.kI (F.q/(2*a-1))*F.m)+
        2*F.q*ν+4*ε+(2*a-1)*F.mesh+εm) := by
  have hq : (2*a-1)*(F.q/(2*a-1))=F.q :=
    mul_div_cancel₀ _ (by linarith : 2*a-1≠0)
  constructor
  · obtain ⟨hz,hz'⟩:=Return.markCap_bounds (line:=Return.line) hrlo hrhi hν hνhi
    have hb:=fiber_inverse_width_count F hU ha.le hC hh hf (markCap Return.line F.r-ν) hz.le hz'
      (fun sel hsel hw=>himp.inverse hrlo hrhi sel hsel hw)
    convert hb using 1
    congr 2
    dsimp [Return.aI,Return.kI,markCap]
    field_simp [show 2*a-1≠0 by linarith]
    <;> ring
  · obtain ⟨hz,hz'⟩:=Return.markCap_bounds (line:=Return.line) hmlo hmhi hν hνhi
    have hmhalf : F.m<1/2 := by norm_num [anchorTop] at hmhi;linarith
    have hb:=fiber_ordinary_width_count F hU ha.le hC hh hf hmhalf hz hz'
      (fun sel hsel hw=>himp.ordinary hmlo hmhi sel hsel hw)
    convert hb using 1
    congr 2
    dsimp [Return.aI,Return.kI,markCap]
    field_simp [show 2*a-1≠0 by linarith]
    <;> ring

end
end QRH.Cycle092.MixedOffsetCount
