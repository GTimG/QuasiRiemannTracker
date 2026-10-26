/- The reflection of a pair of a child prefix and a second-level label negates the pair's row and keeps its norm.
Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.DepthTwoCount
import Candidate.Cycle63.Moment.ReflectedJointRow

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical
local notation "O" => HeckeFamily.O

/-- The pair with the same prefix and the reflected second-level label. -/
def reflectedPair {P : Type*} (x : P × JointSourceLabel) : P × JointSourceLabel :=
  (x.1, reflectedJointLabel x.2)

/-- Reflecting a pair negates its row. -/
theorem depth_two_reflected_row {P : Type*} (v : P → O) (left : Bool) (unit : P → FirstSourceLabel → O)
    (x : P × JointSourceLabel) :
    depthTwoRow v left unit (reflectedPair x) = -depthTwoRow v left unit x :=
  reflected_joint_row left (v x.1) (unit x.1) x.2

/-- Reflecting a pair twice gives the pair back. -/
theorem reflected_pair_involutive {P : Type*} : Function.Involutive (reflectedPair (P := P)) := by
  rintro ⟨p, l⟩
  change (p, reflectedJointLabel (reflectedJointLabel l)) = (p, l)
  rw [reflected_joint_involutive l]

/-- The reflection of a pair with a nonzero row. -/
def reflectedNonzeroDepthTwoPair {P : Type*} {v : P → O} {left : Bool} {unit : P → FirstSourceLabel → O}
    (x : NonzeroDepthTwoPair v left unit) : NonzeroDepthTwoPair v left unit :=
  ⟨reflectedPair x.val, by rw [depth_two_reflected_row]; exact neg_ne_zero.mpr x.property⟩

/-- Reflecting a pair with a nonzero row keeps the norm of the row. -/
theorem reflected_depth_two_norm {P : Type*} {v : P → O} {left : Bool} {unit : P → FirstSourceLabel → O}
    (x : NonzeroDepthTwoPair v left unit) :
    LocalMoment.rawFrequencyNorm (nonzeroDepthTwoRow (reflectedNonzeroDepthTwoPair x)) =
      LocalMoment.rawFrequencyNorm (nonzeroDepthTwoRow x) := by
  simp only [LocalMoment.rawFrequencyNorm, nonzeroDepthTwoRow, reflectedNonzeroDepthTwoPair,
    depth_two_reflected_row, Ideal.span_singleton_neg]

end
end OAI.SevenEighths.Cycle63Moment
