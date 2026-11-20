/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native original phase multiplicity and literal physical reference capacity. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceWindow
import Candidate.C092.transport.MixedMiddleReturnPaidSlicePrefactor
import Candidate.C092.transport.MixedUpperFinalMiddle
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorRawFiber HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.MixedOffsetCount QRH.Cycle090
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]
set_option allowUnsafeReducibility true
attribute [local reducible] BaselineData.toMomentData

/-- Native bin multiplicity is a deterministic original-alphabet bound,
proved from original metadata; this is not an analytic row-cardinality premise. -/
theorem paid_native_phase_card (D : BaselineData) (F : BaselineSourceData D)
    {η : Character} {Z : ℝ} (B : MiddleBank D.toMomentData F η Z)
    (hslots : B.base.batch.slots=Finset.univ) (hbin : B.base.batch.binWidth=D.t) :
    (Fintype.card B.base.batch.Bin:ℝ) ≤ PacketJoin.phaseCardBound D := by
  change (Fintype.card (BinLabel B.base.batch.slots ((2*B.a-1)/2) B.base.batch.binWidth):ℝ) ≤ _
  rw [hslots,hbin]
  simpa only [Nat.card_eq_fintype_card] using PacketJoin.phase_card_le D B.a (by linarith [B.delta_max])

/-- The actual Q capacity satisfies the reference cap at every permitted
physical conductor; no new numerical cap premise remains. -/
theorem paid_capacity {h d : ℝ} (hh : hLower ≤ h) (hd : 0<d) (hdh : d ≤ h+rowPad) :
    Physical.Selection.zeroCapacity (h-2*ell) sourceCost d ≤ (h-2*ell)/d-1/2 := by
  have hn : (1/2:ℝ) ≤ (h-2*ell)/d := by
    apply (le_div_iff₀ hd).mpr
    have hpad : rowPad ≤ 1/100 := by
      unfold rowPad
      apply one_div_le_one_div_of_le (by norm_num : (0:ℝ)<100)
      calc
        (100:ℝ)=(10:ℝ)^2 := by norm_num
        _ ≤ (10:ℝ)^258 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hc : 4*ell+(1/100:ℝ) ≤ hLower := by norm_num [ell,hLower,theta]
    linarith
  have hs : 0 ≤ sourceCost := by norm_num [sourceCost]
  have hc := actual_capacity_reference hn hs
  convert hc using 1 <;> dsimp [Physical.Selection.zeroCapacity,Physical.Selection.clippedCapacity,
    Physical.Selection.affineCapacity,Physical.Selection.plainScale] <;> congr 1 <;> ring

/-- A fixed exponent cost is converted in the true conductor d, not treated
as a Z-exponent twice. The old 5e-13 reserve retains 4e-13 afterwards. -/
theorem paid_power_absorb {a d outerFee : ℝ} (hd : 0<d) (hdhi : d ≤ 7/8) :
    SelectedNonfloor.finalPower a d sourceCost outerFee (theta-1/2000000000000)+
      (1/50000000000000:ℝ) ≤
    SelectedNonfloor.finalPower a d sourceCost outerFee (theta-1/2500000000000) := by
  unfold SelectedNonfloor.finalPower
  apply (add_le_add_iff_left (1/4:ℝ)).mp
  field_simp
  <;> nlinarith only [hd,hdhi]

#print axioms paid_native_phase_card
#print axioms paid_capacity
#print axioms paid_power_absorb
end
end QRH.Cycle092.MixedMiddleReturn
