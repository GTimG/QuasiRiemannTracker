/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine finite two-anchor source invariant and its proved native base.
All mark-presentation hypotheses are exact equalities on the same physical
rows; no fourth-moment or replacement-energy bound is an input. -/
import Candidate.C092.transport.StrongPairPhysical
import Candidate.C092.transport.MeasuredBall
import Candidate.C092.transport.LowActualSource

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

/-- The actual unit cofactor, with no preferred-generator convention assumed. -/
def highRootOne : NonzeroIdeal:=⟨1,one_ne_zero⟩

theorem high_rowMap_one (u : FreeRow) : rowMap (u,highRootOne)=u.val := by
  have hu : IsUnit (idealGenerator (1:Ideal O)):=
    Ideal.span_singleton_eq_top.mp (by simpa using span_idealGenerator (1:Ideal O))
  obtain ⟨v,hv⟩:=hu
  have hp : (idealGenerator (1:Ideal O))^6=1:=by
    rw [←hv]
    exact CanonicalUnitEuler.unit_pow_six v
  change u.val*(idealGenerator (1:Ideal O))^6=u.val
  rw [hp,mul_one]

/-- Reindexing all slots preserves the exact measured response, including
its zero-width and empty-family conventions. -/
theorem high_response_univ {Slot : Type} [Fintype Slot]
    (U pay : ℝ) (w amplitude : Slot→ℝ) :
    LowActual.response U pay (fun i:(Finset.univ:Finset Slot)=>w i.val)
      (fun i=>amplitude i.val)=LowActual.response U pay w amplitude := by
  apply le_antisymm
  · apply (LowActual.response_le_iff ..).2
    have h:=(LowActual.response_le_iff ..).1 (le_refl (LowActual.response U pay w amplitude))
    exact ⟨h.1,fun i=>h.2 i.val⟩
  · apply (LowActual.response_le_iff ..).2
    have h:=(LowActual.response_le_iff ..).1
      (le_refl (LowActual.response U pay (fun i:(Finset.univ:Finset Slot)=>w i.val) (fun i=>amplitude i.val)))
    exact ⟨h.1,fun i=>h.2 ⟨i,Finset.mem_univ _⟩⟩

theorem high_diagonal_ge_one : 1 ≤ QuadraticInitialBound.diagonalControl radialMajorant := by
  have hz : radialMajorant 0=1:=radialMajorant_one 0 (by constructor <;> norm_num)
  have hnorm:=SchwartzMap.norm_le_seminorm ℝ radialMajorant 0
  rw [hz,norm_one] at hnorm
  have hs : SchwartzMap.seminorm ℝ 0 0 radialMajorant ≤
      ((Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ)) radialMajorant :=
    Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) (by decide : (0,0)∈Finset.Iic (2,0))) radialMajorant
  unfold QuadraticInitialBound.diagonalControl
  apply one_le_mul_of_one_le_of_one_le
  · nlinarith [Real.pi_pos]
  · exact hnorm.trans hs

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

theorem high_slotMass_eq {U bΦ : ℝ} (st : NaturalState U 0 bΦ)
    (old base : Character) (hchar : st.character=old)
    (hmask : st.mask=fixedBadMask*idealGenerator 1)
    (W : ℝ→ℂ) (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
    (t : ℝ) (u : FreeRow) :
    RefinedSupplier.slotMass rayM Hr hHr st base W
      (fun i:(Finset.univ:Finset Slot)=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>v i.val)
      t (rowMap (u,highRootOne))=
      ∏ i,‖originalMark rayM Hr hHr old base θ W U w σ v t i u‖^2 := by
  rw [high_rowMap_one]
  simp only [RefinedSupplier.slotMass,hchar,hmask]
  change (∏ i:(Finset.univ:Finset Slot),‖originalMark rayM Hr hHr old base θ W U w σ v t i.val u‖^2)=_
  exact Finset.prod_coe_sort (Finset.univ:Finset Slot)
    (fun i=>‖originalMark rayM Hr hHr old base θ W U w σ v t i u‖^2)

theorem high_measuredResponse_eq {U bΦ : ℝ} (st : NaturalState U 0 bΦ)
    (old base : Character) (hchar : st.character=old)
    (hmask : st.mask=fixedBadMask*idealGenerator 1)
    (W : ℝ→ℂ) (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
    (t pay : ℝ) (u : FreeRow) :
    MeasuredPair.response rayM Hr hHr st base W (Finset.univ:Finset Slot)
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>v i.val)
      t pay (rowMap (u,highRootOne))=
      LowActual.originalResponse old (fixedBadMask*idealGenerator 1) 1 t U pay w
        (originalPools rayM Hr 2 U w) (originalCoefficients rayM Hr hHr base θ W U w σ v)
        (fun i=>U^(w i)) u.val := by
  rw [high_rowMap_one]
  unfold MeasuredPair.response LowActual.originalResponse
  rw [hchar,hmask]
  change LowActual.response U pay (fun i:(Finset.univ:Finset Slot)=>w i.val)
    (fun i=>‖originalMark rayM Hr hHr old base θ W U w σ v t i.val u‖^2)=
    LowActual.response U pay w (fun i=>‖originalMark rayM Hr hHr old base θ W U w σ v t i u‖^2)
  exact high_response_univ (Slot:=Slot) U pay w
    (fun i=>‖originalMark rayM Hr hHr old base θ W U w σ v t i u‖^2)

#print axioms high_rowMap_one
#print axioms high_response_univ
#print axioms high_slotMass_eq
#print axioms high_measuredResponse_eq
#print axioms high_diagonal_ge_one
end
end QRH.Cycle092.StrongPair
