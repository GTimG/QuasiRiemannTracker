/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual support collars and first-short/preceding-long data on one bank subclass. -/
import Candidate.C092.transport.MixedOffsetBankClasses
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetBank
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness

def inverseLength {Label : Type*} {L : ℕ} (U : ℝ) (σ : Descriptor Label L) (j : Offset) : ℝ :=
  Real.logb U ((2:ℝ)^((σ.2.1 j).val))
def ordinaryLength {Label : Type*} {L : ℕ} (U : ℝ) (σ : Descriptor Label L) (j : Offset) : ℝ :=
  Real.logb U ((2:ℝ)^((σ.2.2 j).val))

/-- Every actual witness on the common subclass has the same literal dyad
lengths. All support and annular collars remain those of SupportedWitness. -/
theorem frozen_lengths {Row Label : Type*}
    (rows : Finset Row) (χ : Row→Label→Character) (U a ε t₀ γ T allowance : ℝ) (i : ℕ)
    (w : ∀j : Offset,∀u,SupportedWitness (χ u) U a ε (cutoff t₀ γ j) T allowance i)
    (label : Row→Label) (σ : Descriptor Label (dyadicLength U)) (hU : 1<U)
    (u : Row) (hu : u∈classRows rows label (fun j u=>(w j u).left) (fun j u=>(w j u).right) σ)
    (j : Offset) :
    (w j u).r=inverseLength U σ j ∧ (w j u).m=ordinaryLength U σ j ∧
    cutoff t₀ γ j-inverseLength U σ j-ε ≤ ordinaryLength U σ j ∧
    inverseLength U σ j ≤ cutoff t₀ γ j+ε ∧
    0 ≤ ordinaryLength U σ j ∧ ordinaryLength U σ j ≤ 1/2+75*ε ∧
    cutoff t₀ γ j-1/2-76*ε ≤ inverseLength U σ j := by
  have hf:=class_fields rows label (fun j u=>(w j u).left) (fun j u=>(w j u).right) σ u hu
  have hr : (w j u).r=inverseLength U σ j := by
    rw [(w j u).toWitness.left_exponent hU,hf.2.1 j];rfl
  have hm : (w j u).m=ordinaryLength U σ j := by
    rw [(w j u).toWitness.right_exponent hU,hf.2.2 j];rfl
  refine ⟨hr,hm,?_,?_,?_,?_,?_⟩
  · simpa only [←hr,←hm] using (w j u).product_length_lower
  · simpa only [←hr] using (w j u).inverse_length_upper
  · simpa only [←hm] using (w j u).plain_length_lower
  · simpa only [←hm] using (w j u).plain_length_upper
  · simpa only [←hr] using (w j u).inverse_length_lower

/-- The final offset is retained in the all-long branch. In the other
branch j is the first short inverse and every earlier inverse is long;
thus the preceding cutoff is available for the H_j count. -/
theorem transition_cases (r : Offset→ℝ) :
    ((∀j,1 ≤ r j) ∧ 1 ≤ r ⟨65536,by omega⟩) ∨
    ∃j : Offset,firstShort r=some j ∧ r j<1 ∧
      (∀k : Offset,k<j → 1 ≤ r k) ∧ (j.val=0 ∨ 1 ≤ r (previous j)) := by
  cases he : firstShort r with
  | none =>
    have hall:=(firstShort_none r).mp he
    exact Or.inl ⟨hall,hall _⟩
  | some j =>
    have hf:=firstShort_some r j he
    refine Or.inr ⟨j,rfl,hf.1,hf.2,?_⟩
    by_cases hj : j.val=0
    · exact Or.inl hj
    · exact Or.inr (previous_long r j he (Nat.pos_of_ne_zero hj))

/-- The exact previous offset, including j=0, has Q.2's 1/65536 step.
Its collar can be subtracted without replacing it by the current cutoff. -/
theorem previous_collar (γ εa : ℝ) (hγ : 0 ≤ γ) (j : Offset) :
    max 0 (offset γ (previous j)-3*εa)=
      max 0 (max 0 (offset γ j-γ/65536)-3*εa) := by
  rw [previous_offset γ hγ j]

#print axioms frozen_lengths
#print axioms transition_cases
#print axioms previous_collar
end
end QRH.Cycle092.MixedOffsetBank
