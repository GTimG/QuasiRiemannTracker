import Candidate.Research.RecursiveAffine.WeightedAttainer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity

/- Selection of an actual positive source daughter, with the literal
reciprocal residual normalization and common-allocation Cauchy coefficient.
The input source bound is the recursive regional producer. Selection does
not prove that bound and never drops its reciprocal factors. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153SourceReturn
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentAllocatedNaturalSource
local notation "O" => HeckeFamily.O

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The literal positive row of the actual residual daughter, including its
actual orientation. This is definitionally the PR67 sourcePositiveRow. -/
def physicalDaughterRow (s : Input α) (C R : Ideal O) (Ds : Finset (Ideal O))
    (d : PhysicalDaughter s C R Ds) (z : O) : ℂ :=
  let t := (commonData s C R d.1).toSource
  let X : Fin 2 → ℝ := if d.2.2.2 then ![t.Y₁, t.Y₂] else ![t.X₁, t.X₂]
  allocatedPositiveRow t.η t.m t.A z t.t t.slots
    (fun i I => t.ν i I * t.W i ((Ideal.absNorm I : ℝ) / t.P i)) t.P
    d.2.1.1 d.2.2.1.1 t.W₁ t.W₂ (X 0) (X 1)

def physicalDaughterEnergy (s : Input α) (C R : Ideal O) (Ds : Finset (Ideal O))
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (rad : ℝ)
    (d : PhysicalDaughter s C R Ds) : ℝ :=
  ∑' z : O, if keep z then ‖physicalDaughterRow s C R Ds d z‖ ^ 2 *
    (Φ (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / rad)).re else 0

/-- The exact common Cauchy coefficient times the residual retained
coefficient. The original reciprocal formalReductionFactor remains present.
The orientation is summed by the finite daughter index. -/
def physicalDaughterCoefficient (s : Input α) (C R : Ideal O) (Ds : Finset (Ideal O))
    (d : PhysicalDaughter s C R Ds) : ℝ :=
  let t := commonData s C R d.1
  ((actualAllocations s.pools C).card : ℝ) * ‖commonScalar s C R d.1‖ ^ 2 *
    ((2 * (max 1 t.b₁ * max 1 t.b₂)) *
      (∏ i ∈ frozenIndices d.2.1.1 d.2.2.1.1, t.M i) ^ 2 /
      formalReductionFactor d.2.1.1 d.2.2.1.1 t.P)

theorem physicalDaughterCoefficient_nonneg (s : Input α) (C R : Ideal O)
    (Ds : Finset (Ideal O)) (d : PhysicalDaughter s C R Ds) :
    0 ≤ physicalDaughterCoefficient s C R Ds d := by
  dsimp [physicalDaughterCoefficient]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (div_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
      ((commonData s C R d.1).reduction_pos d.2.1.1 d.2.2.1.1).le)

/-- Maximize the entire normalized return produced for a physical daughter
before the final rows, and preserve its actual source index. The hypothesis
is an actual source-energy inequality, rather than an assumed length cap.
This theorem proves only selection and the weighted aggregation; the regional
producer must discharge `hsource` using its native HIGH/LOW source proof. -/
theorem actual_weighted_source_selection
    (s : Input α) (C R : Ideal O) (Ds : Finset (Ideal O))
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (rad sourceConstant oldPart : ℝ)
    (hconstant : 0 ≤ sourceConstant)
    (SourceReturn : PhysicalDaughter s C R Ds → ℝ → Prop)
    (hsource : ∀ d : PhysicalDaughter s C R Ds, commonScalar s C R d.1 ≠ 0 →
      ∃ ret : ℝ, 0 ≤ ret ∧ SourceReturn d ret ∧
        physicalDaughterEnergy s C R Ds keep Φ rad d ≤ sourceConstant * (oldPart + ret)) :
    ∃ ret : ℝ, 0 ≤ ret ∧
      ((ret = 0 ∧ ∀ d : PhysicalDaughter s C R Ds, commonScalar s C R d.1 = 0) ∨
        ∃ d : PhysicalDaughter s C R Ds, commonScalar s C R d.1 ≠ 0 ∧
          SourceReturn d ret ∧
          physicalDaughterEnergy s C R Ds keep Φ rad d ≤ sourceConstant * (oldPart + ret)) ∧
      (∑ d : PhysicalDaughter s C R Ds, physicalDaughterCoefficient s C R Ds d *
        physicalDaughterEnergy s C R Ds keep Φ rad d) ≤
        (∑ d : PhysicalDaughter s C R Ds, physicalDaughterCoefficient s C R Ds d) *
          (sourceConstant * (oldPart + ret)) := by
  obtain ⟨ret, hret, hselected, hbound⟩ := exists_weighted_attainer
    (fun d : PhysicalDaughter s C R Ds => commonScalar s C R d.1 ≠ 0)
    (fun d r => SourceReturn d r ∧
      physicalDaughterEnergy s C R Ds keep Φ rad d ≤ sourceConstant * (oldPart + r))
    (by
      intro d hd
      obtain ⟨r, hr, hp, he⟩ := hsource d hd
      exact ⟨r, hr, hp, he⟩)
  refine ⟨ret, hret, ?_, ?_⟩
  · rcases hselected with hnone | ⟨d, hd, hp, he⟩
    · exact Or.inl ⟨hnone.1, fun d => not_ne_iff.mp (hnone.2 d)⟩
    · exact Or.inr ⟨d, hd, hp, he⟩
  · rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d _
    by_cases hd : commonScalar s C R d.1 = 0
    · simp [physicalDaughterCoefficient, hd]
    · obtain ⟨r, _, ⟨_, he⟩, hr⟩ := hbound d hd
      apply mul_le_mul_of_nonneg_left _ (physicalDaughterCoefficient_nonneg s C R Ds d)
      exact he.trans (mul_le_mul_of_nonneg_left (by linarith only [hr]) hconstant)

end
end OAI.SevenEighths.Cycle153SourceReturn

#print axioms OAI.SevenEighths.Cycle153SourceReturn.actual_weighted_source_selection
