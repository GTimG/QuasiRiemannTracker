import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Moment.ActualJointDictionary

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical
open HeckeFamily CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondLedger CenteredMomentPartition
local notation "O" => HeckeFamily.O

/-- Negating the residual Fourier row preserves the canonical partition. -/
theorem canonical_partition_neg (C D : Ideal O) (U : Finset (CommonIndex C D)) (z : O) :
    canonicalPartition C D U (-z) ↔ canonicalPartition C D U z := by
  simp only [canonicalPartition,actualUnitSet,dividedFrequency,mul_neg,dvd_neg]
  rfl

def reflectedJointLabel (l : JointSourceLabel) : JointSourceLabel :=
  ⟨l.1,l.2.1,⟨(l.2.2.val.1,-l.2.2.val.2),by
    rw [mul_neg]
    exact (canonical_partition_neg _ _ _ _).mpr l.2.2.property⟩⟩

theorem reflected_joint_row (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (l : JointSourceLabel) :
    jointSourceRow left u₀ unit (reflectedJointLabel l) = -jointSourceRow left u₀ unit l := by
  simp only [jointSourceRow,reflectedJointLabel,effectiveRow]
  ring

theorem reflected_joint_involutive : Function.Involutive reflectedJointLabel := by
  rintro ⟨f,cd,⟨⟨u,z⟩,hp⟩⟩
  simp only [reflectedJointLabel,neg_neg]
  rfl

def reflectedNonzeroJointLabel {left : Bool} {u₀ : O} {unit : FirstSourceLabel→O}
    (l : NonzeroJointSourceLabel left u₀ unit) : NonzeroJointSourceLabel left u₀ unit :=
  ⟨reflectedJointLabel l.val,by rw [reflected_joint_row];exact neg_ne_zero.mpr l.property⟩

theorem reflected_joint_first_frequency (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (l : JointSourceLabel) :
    jointFirstFrequency left u₀ unit (reflectedJointLabel l)=jointFirstFrequency left u₀ unit l := rfl

theorem reflected_joint_norm {left : Bool} {u₀ : O} {unit : FirstSourceLabel→O}
    (l : NonzeroJointSourceLabel left u₀ unit) :
    LocalMoment.rawFrequencyNorm (nonzeroJointSourceRow (reflectedNonzeroJointLabel l))=
      LocalMoment.rawFrequencyNorm (nonzeroJointSourceRow l) := by
  simp only [LocalMoment.rawFrequencyNorm,nonzeroJointSourceRow,reflectedNonzeroJointLabel,
    reflected_joint_row,Ideal.span_singleton_neg]

end
end OAI.SevenEighths.Cycle61Moment
#print axioms OAI.SevenEighths.Cycle61Moment.canonical_partition_neg
#print axioms OAI.SevenEighths.Cycle61Moment.reflected_joint_row
#print axioms OAI.SevenEighths.Cycle61Moment.reflected_joint_involutive
#print axioms OAI.SevenEighths.Cycle61Moment.reflected_joint_first_frequency

#print axioms OAI.SevenEighths.Cycle61Moment.reflected_joint_norm
