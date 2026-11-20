/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal early fee and finite response multiplicity use explicit reserves. -/
import Candidate.C092.transport.MixedUpperFinalEnvelopeFee
import Candidate.C092.transport.MixedUpperFinalUnion
import Candidate.C092.transport.MixedUpperFinalBankCost
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical
open Filter OAI OAI.SevenEighths HeckeDetectorWitnessRows
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.PacketJoin QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount QRH.Cycle090
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Exactly the displayed final fee, with a freely smaller logarithmic
count loss. No native row estimate is an input. -/
theorem actual_exit_fee_paid (D : BaselineData) (P : TransportParameters D)
    (a d affineError loss logLoss : ℝ) (hd : 0<d) (hd' : d ≤ 1)
    (ha : 1/2 ≤ a) (ha' : a ≤ 7/8) (haff : 0 ≤ affineError)
    (hloss : 0 ≤ loss) (hlog : logLoss ≤ loss) (hlog0 : 0 ≤ logLoss)
    (hreserve : 159*D.ε+12*D.t+P.mesh+16*D.e+2*P.eps+affineError/4+loss+2*rowPad ≤ 1/100000000000000) :
    d*(3*(countLoss D.ε P.mesh D.t+logLoss)/4+nativeMoment D affineError/4+nativeMass D a d)+
      (16*D.e+2*P.eps*d+17*D.t/25)+rowPad ≤ 1/2000000000000 := by
  have hnative:=native_early_fee_le_reserve D P a d P.eps affineError loss hd hd' ha ha'
    P.eps_pos.le haff hloss P.mesh_pos.le
  have hlog' : 3*logLoss/4 ≤ loss:=by linarith only [hlog,hlog0]
  have hl:=mul_le_mul_of_nonneg_left hlog' hd.le
  have hpad : 0 ≤ rowPad:=by unfold rowPad;positivity
  dsimp only [countLoss]
  nlinarith only [hnative,hreserve,hl,hpad]

/-- The complete response descriptor count is absorbed once in the original
source scale. The label count is fixed before the physical exponent. -/
theorem descriptor_power_absorbed (Label : Type*) [Fintype Label]
    (loss : ℝ) (hloss : 0<loss) :
    ∃C : ℝ,0 ≤ C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀d a source fee strong target : ℝ,(1/2:ℝ) ≤ d →
      d*loss ≤ target-strong →
      (Fintype.card (Descriptor Label (dyadicLength (Z^d))):ℝ)*
        (Z^d)^(SelectedNonfloor.finalPower a d source fee strong) ≤
      C*(Z^d)^(SelectedNonfloor.finalPower a d source fee target) := by
  obtain ⟨C,hC,h⟩:=descriptor_cost_absorbed Label loss hloss
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with Z h hZ
  refine ⟨hZ,?_⟩
  intro d a source fee strong target hd hgap
  have hU : 1<Z^d:=Real.one_lt_rpow hZ (by linarith)
  calc
    _ ≤ C*(Z^d)^loss*(Z^d)^(SelectedNonfloor.finalPower a d source fee strong) :=
      mul_le_mul_of_nonneg_right (h.2 d hd) (Real.rpow_nonneg (zero_lt_one.trans hU).le _)
    _ = C*(Z^d)^(SelectedNonfloor.finalPower a d source fee strong+loss) := by
      rw [mul_assoc,←Real.rpow_add (zero_lt_one.trans hU),add_comm loss]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU.le
        (final_power_add_loss_le a d source fee strong target loss (by linarith) hgap)) hC

#print axioms actual_exit_fee_paid
#print axioms descriptor_power_absorbed
end
end QRH.Cycle092.MixedUpperFinal
