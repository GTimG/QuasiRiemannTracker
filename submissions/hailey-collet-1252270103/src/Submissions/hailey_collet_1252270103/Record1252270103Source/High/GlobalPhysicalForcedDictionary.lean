/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The selected complete-prime child has the exact retained marked modifier,
original full slot embedding and three puncture invariants. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.JointForcedFamily
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalJointSupportedNewton
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonProfile
open CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput
open Record1252270103Source Record1252270103Second Collision Admission.JointForced
local notation "O"=>ActualEisensteinCubic.O
variable {ι α:Type*} [Fintype ι]

def inheritedSlotEmbedding (B:Tuple ι) (f:ι↪α) : liveIndices B↪α :=
  ⟨fun i=>f i.val,fun i j h=>Subtype.ext (f.injective h)⟩

theorem inherited_slot_fields (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C)
    (τ:Character) (t:ℝ) (f:ι↪α)
    (slots:α→Finset (Ideal O)) (coeff:α→Ideal O→ℂ) (scale:α→ℝ)
    (hs:∀i,s.slots i=slots (f i)) (hc:∀i,restoredSlotCoeff s i=coeff (f i))
    (hp:∀i,s.P i=scale (f i)) :
    (∀i,(child s C R B τ t).slots i=slots (inheritedSlotEmbedding B.val f i)) ∧
    (∀i,restoredSlotCoeff (child s C R B τ t) i=coeff (inheritedSlotEmbedding B.val f i)) ∧
    (∀i,(child s C R B τ t).P i=scale (inheritedSlotEmbedding B.val f i)) :=
  ⟨fun i=>hs i.val,fun i=>hc i.val,fun i=>hp i.val⟩

theorem selected_marked_child_value (s:Input ι) (A₁ A₂ D K R L:Ideal O)
    (F:Ideal O→ℂ) (τ:Character) (t:ℝ) (z:O)
    (p:ChildIndex s (markedSourceModifier A₁ A₂ D K F) R L) :
    childValue s (markedSourceModifier A₁ A₂ D K F) R L τ t z p=
      ‖normalizedRow (child s p.1 R p.2 τ t)
        (markedSourceModifier (A₁*p.2.val (Sum.inr 0)) (A₂*p.2.val (Sum.inr 1))
          (D*p.1) (K*markedProduct p.2.val) F) (R*p.1) 1 τ t z‖^2 := by
  unfold childValue
  rw [funext (markedSourceModifier_common_allocation A₁ A₂ D K p.1 F p.2.val
    (Finset.mem_filter.mp p.2.property).2)]

theorem selected_marked_puncture_invariants (s:Input ι) (A₁ A₂ D K R L:Ideal O)
    (F:Ideal O→ℂ) (hAR:A₁*A₂∣R) (hDR:D∣R) (hKR:K∣R)
    (p:ChildIndex s (markedSourceModifier A₁ A₂ D K F) R L) :
    (A₁*p.2.val (Sum.inr 0))*(A₂*p.2.val (Sum.inr 1))∣R*p.1 ∧
      D*p.1∣R*p.1 ∧ K*markedProduct p.2.val∣R*p.1 := by
  have hb:= (Finset.mem_filter.mp p.2.property).2
  obtain ⟨hA,hD⟩:=puncture_invariants_allocation A₁ A₂ D R p.1 p.2.val hAR hDR hb
  exact ⟨hA,hD,marked_puncture_invariant K R p.1 p.2.val hKR hb⟩

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.inherited_slot_fields
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.selected_marked_child_value
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.selected_marked_puncture_invariants
