import Candidate.Cycle63.Physical.InitialMass.SecondRows
import Candidate.Cycle63.Moment.ActualJointDictionary

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem actual_second_live_partition {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (r : SecondRow s) (hr : r∈secondLiveRows s) :
    canonicalPartition (s r.1).C (s r.1).D (s r.1).inactive
      (nonunitFrequencyGenerator (s r.1).C (s r.1).D (s r.1).inactive*r.2.2.2.val) := by
  have hw := (Finset.mem_filter.mp hr).2.2.2
  by_contra hn
  exact hw (by simp [SecondBlockSource.rowWeight,retainedScalar,canonicalPartitionScalar,hn])

theorem actual_second_live_retained_weight {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (r : SecondRow s) (hr : r∈secondLiveRows s) :
    retainedWeight (s r.1).radius (normValue ((s r.1).frequency*r.2.2.2.val))≠0 := by
  have hw := (Finset.mem_filter.mp hr).2.2.2
  have hs := (mul_ne_zero_iff.mp hw).1
  change retainedScalar (s r.1).C (s r.1).D (s r.1).inactive
    (s r.1).radius r.2.2.2.val≠0 at hs
  have he := (mul_ne_zero_iff.mp hs).2
  exact Complex.ofReal_ne_zero.mp he

/-- A physical row is encoded only after the residual projector has been
separated from the row coordinate. Its canonical partition is proved from
the literal retained scalar. -/
def secondEncodedRow {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (first : Label→FirstSourceLabel)
    (r : secondLiveRows s) : JointSourceLabel :=
  ⟨first r.val.1,((s r.val.1).C,(s r.val.1).D),
    ⟨((s r.val.1).inactive,r.val.2.2.2.val),actual_second_live_partition s r.val r.property⟩⟩

theorem actual_second_encoded_row_factorization {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (first : Label→FirstSourceLabel)
    (r : secondLiveRows s) (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O) :
    jointSourceRow left u₀ unit (secondEncodedRow s first r)=
      jointFirstFrequency left u₀ unit (secondEncodedRow s first r)*
        ((s r.val.1).frequency*r.val.2.2.2.val) :=
  joint_source_row_factorization left u₀ unit (secondEncodedRow s first r)

theorem actual_second_encoded_row_ne_zero {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (first : Label→FirstSourceLabel)
    (r : secondLiveRows s) (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (hf : jointFirstFrequency left u₀ unit (secondEncodedRow s first r)≠0) :
    jointSourceRow left u₀ unit (secondEncodedRow s first r)≠0 := by
  rw [actual_second_encoded_row_factorization]
  apply mul_ne_zero hf
  apply mul_ne_zero _ ((s r.val.1).rows_ne _ r.val.2.2.2.property)
  exact mul_ne_zero (commonFrequencyGenerator_ne_zero _ _ (s r.val.1).hC)
    (nonunitFrequencyGenerator_ne_zero _ _ (s r.val.1).hC _)

def secondEncodedNonzeroRow {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (first : Label→FirstSourceLabel)
    (r : secondLiveRows s) (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (hf : jointFirstFrequency left u₀ unit (secondEncodedRow s first r)≠0) :
    NonzeroJointSourceLabel left u₀ unit :=
  ⟨secondEncodedRow s first r,actual_second_encoded_row_ne_zero s first r left u₀ unit hf⟩

theorem actual_second_encoded_first_projector {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (first : Label→FirstSourceLabel)
    (r : secondLiveRows s) (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (L : Ideal O) (hL : Squarefree L) (hLC : L∣(s r.val.1).C) (hLD : L∣(s r.val.1).D) :
    L∣Ideal.span {jointSourceRow left u₀ unit (secondEncodedRow s first r)} :=
  actual_first_projector_dvd_joint_row left u₀ unit (secondEncodedRow s first r)
    L hL (s r.val.1).hC (s r.val.1).hD.1 hLC hLD

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_live_partition
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_live_retained_weight
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_encoded_row_factorization
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_encoded_row_ne_zero
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_encoded_first_projector
