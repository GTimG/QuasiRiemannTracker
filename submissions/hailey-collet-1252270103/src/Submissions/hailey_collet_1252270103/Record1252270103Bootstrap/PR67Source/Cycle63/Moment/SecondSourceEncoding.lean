import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.FirstSourceCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalNonunit
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSupport
open CenteredMomentSecondLedger
local notation "O" => HeckeFamily.O

def SecondSourceFrequency (C D : Ideal O) :=
  {q : Finset (CommonIndex C D) × O //
    canonicalPartition C D q.1 (nonunitFrequencyGenerator C D q.1*q.2)}

def secondSourceFrequency (C D : Ideal O) (q : SecondSourceFrequency C D) : O :=
  nonunitFrequencyGenerator C D q.val.1*q.val.2

/-- The actual partition is determined by its pre-split frequency; after it
is known, cancellation recovers the residual frequency. -/
theorem second_source_frequency_injective (C D : Ideal O) (hC : Supported C) :
    Function.Injective (secondSourceFrequency C D) := by
  intro q r h
  have hU : q.val.1 = r.val.1 := q.property.symm.trans
    ((congrArg (fun z => actualUnitSet (commonPrime C D)
      (leftExponent C D) (rightExponent C D) z) h).trans r.property)
  apply Subtype.ext
  apply Prod.ext hU
  change nonunitFrequencyGenerator C D q.val.1*q.val.2 =
    nonunitFrequencyGenerator C D r.val.1*r.val.2 at h
  rw [←hU] at h
  exact mul_left_cancel₀ (nonunitFrequencyGenerator_ne_zero C D hC q.val.1) h

def JointSourceLabel :=
  Σ _first : FirstSourceLabel, Σ second : Ideal O × Ideal O,
    SecondSourceFrequency second.1 second.2

def jointSourceRow (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
    (label : JointSourceLabel) : O :=
  effectiveRow (u₀*unit label.1)
    (primeSubsetGenerator (fun P : CommonIndex label.1.1.1 label.1.1.2 => P.val) label.1.2.val)
    (firstSourceNumerator left label.1)
    (commonFrequencyGenerator label.2.1.1 label.2.1.2)
    (nonunitFrequencyGenerator label.2.1.1 label.2.1.2 label.2.2.val.1) label.2.2.val.2

def jointSourceKey (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
    (label : JointSourceLabel) : O × (((Ideal O × Ideal O) × Ideal O) × (Ideal O × Ideal O)) :=
  (jointSourceRow left u₀ unit label, (firstSourceKey left label.1,label.2.1))

theorem joint_source_key_injOn (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
    (labels : Set JointSourceLabel)
    (hrow : ∀ label ∈ labels, jointSourceRow left u₀ unit label ≠ 0)
    (hsupported : ∀ label ∈ labels, Supported label.2.1.1) :
    Set.InjOn (jointSourceKey left u₀ unit) labels := by
  rintro ⟨first,CD,q⟩ ha ⟨first',CD',r⟩ hb hkey
  have hf : first = first' := first_source_key_injective left
    (congrArg (fun x => x.2.1) hkey)
  cases hf
  have hp : CD = CD' := congrArg (fun x => x.2.2) hkey
  cases hp
  have hw := congrArg Prod.fst hkey
  have hrowa := hrow _ ha
  let rowFactor := (u₀*unit first)*
    primeSubsetGenerator (fun P : CommonIndex first.1.1 first.1.2 => P.val) first.2.val*
    firstSourceNumerator left first*commonFrequencyGenerator CD.1 CD.2
  have heq (s : SecondSourceFrequency CD.1 CD.2) :
      jointSourceRow left u₀ unit ⟨first,CD,s⟩ = rowFactor*secondSourceFrequency CD.1 CD.2 s := by
    dsimp [jointSourceRow, rowFactor, effectiveRow, secondSourceFrequency]
    ring
  rw [heq] at hrowa
  have hprefix := (mul_ne_zero_iff.mp hrowa).1
  have hfreq : secondSourceFrequency CD.1 CD.2 q = secondSourceFrequency CD.1 CD.2 r := by
    apply mul_left_cancel₀ hprefix
    change jointSourceRow left u₀ unit ⟨first,CD,q⟩ =
      jointSourceRow left u₀ unit ⟨first,CD,r⟩ at hw
    simpa only [heq] using hw
  have hqr := second_source_frequency_injective CD.1 CD.2 (hsupported _ ha) hfreq
  cases hqr
  rfl

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
