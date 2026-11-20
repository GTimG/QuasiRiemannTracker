/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.MixedMiddleReturnBank
import Candidate.C092.transport.MediumWitnessBatch
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorRawFiber HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters]
set_option allowUnsafeReducibility true
attribute [local reducible] BaselineData.toMomentData

/-- The source bank's original physical mark is precisely the original
canonical prime amplitude, at the same contour coordinate and prime scale. -/
theorem native_original_slot (D : BaselineData) (F : BaselineSourceData D)
    {η : Character} {Z : ℝ} (B : MixedOffsetCount.MiddleBank D.toMomentData F η Z)
    (hZ : 0<Z) (z : Fin D.N→ℂ) (hz : B.current.batch.external=z)
    (u : FreeRow) (s : Fin D.N) :
    physical F.modulus ⊤ (fun v : FreeRow=>v.val) B.currentSlice.fiber.profile
      B.currentSlice.fiber.upper B.currentSlice.fiber.widths B.currentSlice.fiber.external
      B.baseScale u s =
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) (z s) := by
  change physical F.modulus ⊤ (fun v : FreeRow=>v.val) B.current.batch.profile
    B.current.batch.upper B.current.batch.widths B.current.batch.external (Z^B.d) u s=_
  rw [B.current.profile,B.current.upper,B.current.widths,hz]
  exact MediumWitness.originalPhysical_eq D F Z B.d hZ (by linarith [B.d_min]) z u s

/-- The complementary main product is the literal product in the original
numerator mask; no rowwise prime subproduct is substituted. -/
theorem native_original_main (D : BaselineData) (F : BaselineSourceData D)
    {η : Character} {Z : ℝ} (B : MixedOffsetCount.MiddleBank D.toMomentData F η Z)
    (hZ : 0<Z) (J : Finset (Fin D.N)) (z : ℂ)
    (hz : B.current.batch.external=(fun _=>z)) (u : FreeRow) :
    B.currentSlice.fiber.physicalProduct (Finset.univ\J) u=mainProduct D F J u Z z := by
  unfold Fiber.physicalProduct mainProduct
  apply Finset.prod_congr rfl
  intro s hs
  exact native_original_slot D F B hZ (fun _=>z) hz u s

/-- Native physical slot lengths retain the full original denominator. -/
theorem native_original_total (D : BaselineData) (F : BaselineSourceData D)
    {η : Character} {Z : ℝ} (B : MixedOffsetCount.MiddleBank D.toMomentData F η Z)
    (hslots : B.currentSlice.fiber.slots=Finset.univ) :
    (∑s∈B.currentSlice.fiber.slots,B.currentSlice.fiber.widths s)=Geometry.ell/B.d := by
  rw [hslots]
  change (∑s : Fin D.N,B.current.batch.widths s)=_
  rw [B.current.widths,←Finset.sum_div,D.slots_sum]

#print axioms native_original_main
#print axioms native_original_total
end
end QRH.Cycle092.MixedMiddleReturn
