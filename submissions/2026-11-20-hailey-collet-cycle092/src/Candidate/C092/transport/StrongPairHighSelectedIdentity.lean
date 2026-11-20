/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite two-anchor source invariant and its proved native base.
All mark-presentation hypotheses are exact equalities on the same physical
rows; no fourth-moment or replacement-energy bound is an input. -/
import Candidate.C092.transport.StrongPairHighIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Cycle090 QRH.SourceCertificate
local notation "O" => ActualEisensteinCubic.O

open QRH.Record12518109Source QRH.Record12518109Existence

open CenteredMomentEnergyState Qrh.JointDetector

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

/-- Literal selected whole-mark mass on the unchanged free row. -/
theorem high_selected_slotMass_eq {U bΦ : ℝ} (st : NaturalState U 0 bΦ)
    (old base : Character) (hchar : st.character=old)
    (hmask : st.mask=fixedBadMask*idealGenerator 1)
    (W : ℝ→ℂ) (J : Finset Slot) (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
    (t : ℝ) (u : FreeRow) :
    RefinedSupplier.slotMass rayM Hr hHr st base W
      (fun i:J=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>v i.val)
      t (rowMap (u,highRootOne))=
      ∏ i∈J,‖originalMark rayM Hr hHr old base θ W U w σ v t i u‖^2 := by
  rw [high_rowMap_one]
  simp only [RefinedSupplier.slotMass,hchar,hmask]
  change (∏ i:J,‖originalMark rayM Hr hHr old base θ W U w σ v t i.val u‖^2)=_
  exact Finset.prod_coe_sort J (fun i=>‖originalMark rayM Hr hHr old base θ W U w σ v t i u‖^2)

/-- The measured supplier uses exactly the original response of the selected
subproduct, with the original zero-width convention and denominator. -/
theorem high_selected_measuredResponse_eq {U bΦ : ℝ} (st : NaturalState U 0 bΦ)
    (old base : Character) (hchar : st.character=old)
    (hmask : st.mask=fixedBadMask*idealGenerator 1)
    (W : ℝ→ℂ) (J : Finset Slot) (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
    (t pay : ℝ) (u : FreeRow) :
    MeasuredPair.response rayM Hr hHr st base W J
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>v i.val)
      t pay (rowMap (u,highRootOne))=
      LowActual.originalResponse old (fixedBadMask*idealGenerator 1) 1 t U pay (fun i:J=>w i.val)
        (originalPools rayM Hr 2 U (fun i:J=>w i.val))
        (originalCoefficients rayM Hr hHr base (fun i:J=>θ i.val) W U
          (fun i:J=>w i.val) (fun i:J=>σ i.val) (fun i:J=>v i.val))
        (fun i:J=>U^(w i.val)) u.val := by
  rw [high_rowMap_one]
  unfold MeasuredPair.response LowActual.originalResponse
  rw [hchar,hmask]
  rfl

#print axioms high_selected_slotMass_eq
#print axioms high_selected_measuredResponse_eq
end
end QRH.Cycle092.StrongPair
