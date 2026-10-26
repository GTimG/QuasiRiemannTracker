/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual selected allocation ideals and the literal LOW positive value. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedLowDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedLowPaid
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedLowPaidWeight
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.RetainedLowPaid
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalPositiveCornerSplit
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedLowSource
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform CenteredMomentCanonicalFirst Cycle61Moment
open CenteredMomentSecondHeightFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open OAI.SevenEighths.Record1252270103Source Record1252270103Second
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
open CenteredMomentFiniteProfileExceptional
open SelectedHighCofactorFamily High.GlobalPhysical
local notation "O"=>HeckeFamily.O
local instance selectedDictionaryDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _
variable {α:Type}[Fintype α]{s:Input α}{reflected second:Bool}
    {l:FirstSourceLabel}{C₂ D₂ R:Ideal O}

theorem selected_puncture_eq (sel:Selection s reflected second l C₂ D₂ R)
    (Rchild:Ideal O)(hRchild:Rchild=R*(if reflected then l.1.2 else l.1.1)):
    (Rchild*(if second then D₂ else C₂))*sel.Cf=Selection.puncture sel := by
  rw [hRchild]
  rfl

theorem selected_positive_corner_eq (sel:Selection s reflected second l C₂ D₂ R)
    (T:Finset α)(corner:Bool)(b:ℝ)(S A:Finset (Ideal O))(τ:Character)(t:ℝ)(z:O):
    SelectedLowErasure.positiveCorner sel T corner (Selection.frozenLeft sel)
      (Selection.frozenRight sel) b S A τ t z=
    positiveNewtonCofactorPlain corner sel.finalInput (Selection.frozenLeft sel)
      (Selection.frozenRight sel) (Selection.puncture sel) b S A τ t z*
      (∏i:T,normalizedSlot τ (fixedBadMask*idealGenerator (Selection.puncture sel)) 1 z
        (s.slots i) (restoredSlotCoeff s i) t (s.P i)) := by
  rfl

end
end QRH.Record1252270103Source.Admission.SelectedLowSource
#print axioms QRH.Record1252270103Source.Admission.SelectedLowSource.selected_puncture_eq
#print axioms QRH.Record1252270103Source.Admission.SelectedLowSource.selected_positive_corner_eq
