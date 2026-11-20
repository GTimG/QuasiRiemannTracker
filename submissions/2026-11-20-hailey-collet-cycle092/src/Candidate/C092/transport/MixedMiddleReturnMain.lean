/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual complementary main products and the masked-class mean. -/
import Candidate.C092.transport.MixedMiddleReturnPresentation
import Candidate.C092.transport.MixedMiddleReturnAnalytic
import Candidate.C092.transport.MixedMiddleReturnExponent

set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorPhysicalSelection
open Cycle25.Numerator Cycle25DetectorRowCount
local notation "O" => HeckeFamily.O

/-- The original complete complementary product is bounded from its own bins,
with the full length denominator retained in qMain. -/
theorem main_product_upper {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label : Type}
    {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε cutoff T allowance i) (hU : 1<U)
    (hslots : F.slots=Finset.univ) (main : Finset Slot) (u : FreeRow)
    (hupper : ∀s∈main,‖physical M H (fun v : FreeRow=>v.val)
      F.profile F.upper F.widths F.external U u s‖≤U^(F.widths s*(F.bin s+F.binWidth))) :
    ‖F.physicalProduct main u‖≤U^(
      weightedMean F.slots F.widths (maskedGain main F.bin)*(∑s∈F.slots,F.widths s)+
      F.binWidth*(∑s∈F.slots,F.widths s)) := by
  have hw (s : Slot) : 0≤F.widths s :=
    (F.widths_pos s (hslots ▸ Finset.mem_univ s)).le
  have hL : 0<∑s : Slot,F.widths s := by
    have hs := F.supply
    rw [hslots] at hs
    linarith
  have h := masked_main_product_upper main F.widths F.bin U F.binWidth
    (fun s=>physical M H (fun v : FreeRow=>v.val) F.profile F.upper F.widths F.external U u s)
    hU.le F.binWidth_pos.le hw hL hupper
  simpa only [hslots,Fiber.physicalProduct] using h

#print axioms main_product_upper
end
end QRH.Cycle092.MixedMiddleReturn
