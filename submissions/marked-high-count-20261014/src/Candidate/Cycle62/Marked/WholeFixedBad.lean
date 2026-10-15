import Candidate.Cycle62.Marked.WholeFamilyAnchor
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceInternal

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62MarkedPlain
noncomputable section
open HeckeFamily CenteredMomentNaturalFixedRaySource CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def markedFixedIdeal (M : Ideal O) : Ideal O:=M⊓Ideal.span {(72:O)}

lemma markedFixedIdeal_ne_zero (M : Ideal O) [NeZero M] : markedFixedIdeal M≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne M)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma span72_ne_top : (Ideal.span {(72:O)})≠⊤ := by
  intro h
  have hu : IsUnit (72:O):=Ideal.span_singleton_eq_top.mp h
  have h2 : (-2:O)∣72:=⟨-36,by norm_num⟩
  exact CanonicalRowCompletion.negative_two_prime.not_isUnit (isUnit_of_dvd_unit h2 hu)

lemma markedFixedIdeal_ne_top (M : Ideal O) : markedFixedIdeal M≠⊤ := by
  intro h
  exact span72_ne_top (top_le_iff.mp (h ▸ (inf_le_right : markedFixedIdeal M≤Ideal.span {(72:O)})))

/-- One fixed nonzero bad ideal works for every detector anchor and every
geometric dictionary member, independently of moving source allocations. -/
theorem marked_fixed_ideal_gates (M : Ideal O) [NeZero M] (η : Character) :
    markedFixedIdeal M≤M ∧ internalQ (markedFixedIdeal M) η≠0 ∧
      internalQ (markedFixedIdeal M) η≠⊤ ∧
      internalQ (markedFixedIdeal M) η≤Ideal.span {(72:O)} :=
  ⟨inf_le_left,internalQ_ne_zero _ (markedFixedIdeal_ne_zero M) η,
    internalQ_ne_top _ (markedFixedIdeal_ne_top M) η,inf_le_left.trans inf_le_right⟩

end
end OAI.SevenEighths.Cycle62MarkedPlain
#print axioms OAI.SevenEighths.Cycle62MarkedPlain.marked_fixed_ideal_gates
