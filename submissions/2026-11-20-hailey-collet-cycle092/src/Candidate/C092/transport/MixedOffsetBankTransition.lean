/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The first transition is shared by every original row in one descriptor class. -/
import Candidate.C092.transport.MixedOffsetBankGuards
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetBank
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows

/-- This class contains original physical rows, with unchanged weights.
Every earlier offset is long at the first short index; the final offset is
retained if no transition occurs. Thus current and preceding counts have
one common cardinality target. No response monotonicity is assumed. -/
theorem class_transition_data {Row Label : Type*}
    (rows : Finset Row) (χ : Row→Label→Character) (U a ε t₀ γ T allowance : ℝ) (i : ℕ)
    (w : ∀j : Offset,∀u,SupportedWitness (χ u) U a ε (cutoff t₀ γ j) T allowance i)
    (label : Row→Label) (σ : Descriptor Label (dyadicLength U)) (hU : 1<U) :
    let common:=classRows rows label (fun j u=>(w j u).left) (fun j u=>(w j u).right) σ
    ((∀j : Offset,∀u∈common,1 ≤ (w j u).r) ∧
      (∀u∈common,1 ≤ (w ⟨65536,by omega⟩ u).r)) ∨
    ∃j : Offset,firstShort (inverseLength U σ)=some j ∧
      (∀u∈common,(w j u).r<1) ∧
      (∀k : Offset,k<j → ∀u∈common,1 ≤ (w k u).r) ∧
      (j.val=0 ∨ ∀u∈common,1 ≤ (w (previous j) u).r) := by
  dsimp only
  have hr (u : Row) (hu : u∈classRows rows label (fun j u=>(w j u).left) (fun j u=>(w j u).right) σ)
      (j : Offset) : (w j u).r=inverseLength U σ j :=
    (frozen_lengths rows χ U a ε t₀ γ T allowance i w label σ hU u hu j).1
  rcases transition_cases (inverseLength U σ) with hall|⟨j,hj,hshort,hbefore,hprevious⟩
  · refine Or.inl ⟨?_,?_⟩
    · intro j u hu;rw [hr u hu j];exact hall.1 j
    · intro u hu;rw [hr u hu _];exact hall.2
  · refine Or.inr ⟨j,hj,?_,?_,?_⟩
    · intro u hu;rw [hr u hu j];exact hshort
    · intro k hk u hu;rw [hr u hu k];exact hbefore k hk
    · rcases hprevious with hj0|hprev
      · exact Or.inl hj0
      · exact Or.inr (fun u hu=>by rw [hr u hu _];exact hprev)

#print axioms class_transition_data
end
end QRH.Cycle092.MixedOffsetBank
