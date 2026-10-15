import Candidate.Cycle62.Physical.InitialMass.SecondEncoding
import Candidate.Cycle62.Moment.CanonicalFirstNorm
import Candidate.Cycle62.Moment.ReflectedJointRow

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle62Moment
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
local notation "O" => HeckeFamily.O

/-- The signed first numerator cannot vanish on a supported first pair. -/
theorem first_source_numerator_ne_zero (left : Bool)(l : FirstSourceLabel)
    (hC : Supported l.1.1) : firstSourceNumerator left l≠0 := by
  have hn : 0<(Ideal.span {firstSourceNumerator left l}).absNorm := by
    cases left <;> exact powered_numerator_norm_pos _ _ _
      (fun P _=>firstSignedPrime_supported _ _ hC P)
  intro he
  simp only [he,Ideal.span_singleton_zero,Ideal.absNorm_bot] at hn
  omega

/-- Nonzero fixed factor and unit choices make every literal first
frequency nonzero; this is independent of subsequent block cancellation. -/
theorem actual_joint_first_frequency_ne_zero (left : Bool)(u₀ : O)
    (unit : FirstSourceLabel→O)(l : JointSourceLabel)
    (hu₀ : u₀≠0)(hunit : unit l.1≠0)(hC : Supported l.1.1.1) :
    jointFirstFrequency left u₀ unit l≠0 := by
  unfold jointFirstFrequency
  apply mul_ne_zero _ (first_source_numerator_ne_zero left l.1 hC)
  apply mul_ne_zero (mul_ne_zero hu₀ hunit)
  exact Ideal.span_singleton_eq_bot.not.mp
    (subsetGenerator_supported _ _ hC l.1.2.val).1

/-- Actual live second blocks supply both common-ideal support gates. -/
theorem actual_second_encoded_support {Label : Type*}[Fintype Label]
    (s : Label→SecondBlockSource)(first : Label→FirstSourceLabel)
    (hfirst : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2 ∧
      CompletedGauss.primeSupport (first l).1.1=CompletedGauss.primeSupport (first l).1.2)
    (r : secondLiveRows s) :
    let l := secondEncodedRow s first r
    (Supported l.1.1.1 ∧ l.1.1.2≠0 ∧ Supported l.2.1.1 ∧ l.2.1.2≠0) ∧
      (CompletedGauss.primeSupport l.1.1.1=CompletedGauss.primeSupport l.1.1.2 ∧
       CompletedGauss.primeSupport l.2.1.1=CompletedGauss.primeSupport l.2.1.2) := by
  exact ⟨⟨(hfirst r.val.1).1,(hfirst r.val.1).2.1.1,
    (s r.val.1).hC,(s r.val.1).hD.1⟩,⟨(hfirst r.val.1).2.2,(s r.val.1).sameSupport⟩⟩

/-- Reflection keeps distinct encoded rows distinct, so the right column
uses the same joint-count selection without a new multiplicity factor. -/
theorem reflected_nonzero_joint_injective {left : Bool}{u₀ : O}{unit : FirstSourceLabel→O} :
    Function.Injective (@reflectedNonzeroJointLabel left u₀ unit) := by
  intro l k he
  apply Subtype.ext
  exact reflected_joint_involutive.injective (congrArg Subtype.val he)

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.first_source_numerator_ne_zero
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_joint_first_frequency_ne_zero
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_second_encoded_support
#print axioms OAI.SevenEighths.Cycle62InitialMass.reflected_nonzero_joint_injective
