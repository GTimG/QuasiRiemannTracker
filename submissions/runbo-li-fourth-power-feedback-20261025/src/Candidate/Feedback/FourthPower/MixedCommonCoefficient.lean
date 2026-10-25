/- Copyright (c) 2026 Sil. Apache-2.0.
Actual restricted coefficients under complete common extraction. Reuse
baseline's residual_source_profile with its arbitrary remaining-tuple
multiplier. The fifth-free and injectivity masks are preserved exactly;
the resulting live coefficient has the original profile and puncture R*C.
-/
import Candidate.Feedback.FourthPower.MixedCommonAllocation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceLiveColumn

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.MixedCommonCoefficient
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox CenteredMomentCommonPrimeSlots
open CenteredMomentSourceLiveAllocation CenteredMomentSourceLiveColumn
open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open MixedCommonAllocation
local notation "Id" => Ideal ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def tupleWeight (H : Id) (v : Tuple ι) : ℂ := if tupleRestriction H v then 1 else 0
def frozenWeight (H : Id) (B : Tuple ι) : ℂ := if frozenRestriction H B then 1 else 0

theorem actual_weight_split (H : Id) (S : (ι⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (C : Id) (hC : C≠0)
    (B : actualAllocations S C) (u : Tuple ι)
    (hu : u∈residualBoxes S C B.val
      (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1)
    (hp : ∀i,∀I∈S (Sum.inl i),Prime I) :
    tupleWeight H (fun j=>B.val j*u j)=
      frozenWeight H B.val*tupleWeight H (remainingTuple B.val u) := by
  unfold tupleWeight frozenWeight
  rw [actual_restriction_split H S hS C hC B u hu hp]
  split_ifs <;> simp_all

theorem residual_restricted_column (H : Id) (S : (ι⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (C R s a : Id) (hC : C≠0) (hsC : s∣C) (B : actualAllocations S C)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) :
    (∑u∈residualBoxes S C B.val
        (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1,
      if finiteTupleProduct u=a then
        tupleWeight H (fun j=>B.val j*u j)*
          profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun j=>B.val j*u j)
      else 0)=
      (frozenWeight H B.val*frozenCoefficient B.val C R ν Wslot P)*
        finiteColumnCoefficient
          (liveBox S B.val (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1)
          (fun v=>tupleWeight H v*liveProfile B.val C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v) a := by
  let hB := (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1
  let F := fun v : Tuple (liveIndices B.val)=>tupleWeight H v*
    (if finiteTupleProduct v=a then 1 else 0)
  have hh := residual_source_profile S hp B.val hB C R s
    (Finset.mem_filter.mp B.property).2 hsC ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ F
  rw [ite_eq_left (allocation_frozen_gate S hp C B.val (Finset.mem_filter.mp B.property).1)] at hh
  have hcol : (∑u∈residualBoxes S C B.val hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun j=>B.val j*u j)*
        F (remainingTuple B.val u))=
      frozenCoefficient B.val C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B.val hB)
          (fun v=>tupleWeight H v*liveProfile B.val C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v) a := by
    apply hh.trans
    unfold frozenCoefficient finiteColumnCoefficient liveBox liveProfile
    rw [Finset.sum_filter]
    congr 1
    apply Finset.sum_congr
    · ext v
      simp only [Fintype.mem_piFinset]
    · intro v hv
      dsimp only [F]
      split_ifs <;> ring
  calc
    _ = frozenWeight H B.val * (∑u∈residualBoxes S C B.val hB,
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun j=>B.val j*u j)*
          F (remainingTuple B.val u)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have hf := actual_frozen_slots S hS C hC B.val hB
        (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).2 u hu hp
      rw [remaining_product B.val u hf,actual_weight_split H S hS C hC B u hu hp]
      dsimp only [F]
      split_ifs <;> ring
    _ = _ := by rw [hcol];ring

/-- The exact whole column after genuine common extraction. Its live
coefficient is the original baseline liveProfile times our literal mask.
All common support conditions, fifth-free gates and marked collisions stay
in the identity, so no unrestricted child theorem is substituted here. -/
theorem original_restricted_column (H : Id) (S : (ι⊕Fin 2)→Finset Id)
    (hS : ∀j,∀I∈S j,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (C R s a : Id) (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a) (hsC : s∣C)
    (ν : ι→Id→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) :
    finiteColumnCoefficient (Fintype.piFinset S)
      (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v) (C*a)=
      ∑B : actualAllocations S C,
        (frozenWeight H B.val*frozenCoefficient B.val C R ν Wslot P)*
          finiteColumnCoefficient
            (liveBox S B.val (allocation_data S C B.val (Finset.mem_filter.mp B.property).1).1)
            (fun v=>tupleWeight H v*liveProfile B.val C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v) a := by
  have halloc := original_coefficient_allocated S hS C a hC ha hCa
    (fun v=>tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v)
  change (∑v∈Fintype.piFinset S,if finiteTupleProduct v=C*a then
    tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v else 0)=_ at halloc
  change (∑v∈(Fintype.piFinset S).filter (fun v=>finiteTupleProduct v=C*a),
    tupleWeight H v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v)=_
  rw [Finset.sum_filter,halloc]
  apply Finset.sum_congr rfl
  intro B hB
  exact residual_restricted_column H S hS hp C R s a hC hsC B ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂

end
end Candidate.Feedback.FourthPower.MixedCommonCoefficient
