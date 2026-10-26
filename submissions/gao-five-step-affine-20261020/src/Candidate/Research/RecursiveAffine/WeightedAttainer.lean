import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonLinearNormalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity

/- The selector acts on entire weighted daughter bounds before the final rows.
It retains the actual source index; neither its residual allocation nor its
normalizing weight is replaced by a separately maximizing choice. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153SourceReturn
noncomputable section
open scoped Classical BigOperators

/-- A finite family of nonnegative weighted returns has an actual attaining
source, unless the active family is empty. The property `P` can contain the
literal residual source, reduction F, returned records and class caps. -/
theorem exists_weighted_attainer {ι : Type*} [Finite ι]
    (valid : ι → Prop) (P : ι → ℝ → Prop)
    (hday : ∀ i, valid i → ∃ r, 0 ≤ r ∧ P i r) :
    ∃ r : ℝ, 0 ≤ r ∧
      ((r = 0 ∧ ∀ i, ¬valid i) ∨ ∃ i, valid i ∧ P i r) ∧
      ∀ i, valid i → ∃ r', 0 ≤ r' ∧ P i r' ∧ r' ≤ r := by
  let Active := {i : ι // valid i}
  by_cases hne : Nonempty Active
  · letI : Nonempty Active := hne
    let r : Active → ℝ := fun i => Classical.choose (hday i.val i.property)
    have hr (i : Active) : 0 ≤ r i ∧ P i.val (r i) :=
      Classical.choose_spec (hday i.val i.property)
    obtain ⟨imax, hmax⟩ := Finite.exists_max r
    refine ⟨r imax, (hr imax).1, Or.inr ⟨imax.val, imax.property, (hr imax).2⟩, ?_⟩
    intro i hi
    exact ⟨r ⟨i, hi⟩, (hr ⟨i, hi⟩).1, (hr ⟨i, hi⟩).2, hmax ⟨i, hi⟩⟩
  · refine ⟨0, le_rfl, Or.inl ⟨rfl, ?_⟩, ?_⟩
    · intro i hi
      exact hne ⟨⟨i, hi⟩⟩
    · intro i hi
      exact False.elim (hne ⟨⟨i, hi⟩⟩)

/-- For an actual common allocation, the surviving daughter choices consist
of an actual dyadic residual ideal, an active allocation and an orientation.
This finite index is selected before the final row family. -/
abbrev PhysicalDaughter {α : Type*} [Fintype α] [DecidableEq α]
    (s : CenteredMomentCommonRadialData.Input α)
    (C R : Ideal HeckeFamily.O) (Ds : Finset (Ideal HeckeFamily.O)) :=
  Σ (B : ↥(CenteredMomentCommonAllocationSum.actualAllocations s.pools C)),
    Σ (D : ↥Ds),
      Σ (_ : ↥((CenteredMomentCommonRadialData.commonData s C R B).toSource.active D.1)), Bool

/-- Every selected daughter is a member of the actual common/residual/active
menu. In particular no independently selected residual ideal is introduced. -/
theorem physical_daughter_is_active {α : Type*} [Fintype α] [DecidableEq α]
    (s : CenteredMomentCommonRadialData.Input α)
    (C R : Ideal HeckeFamily.O) (Ds : Finset (Ideal HeckeFamily.O))
    (d : PhysicalDaughter s C R Ds) :
    d.2.1.1 ∈ Ds ∧
      d.2.2.1.1 ∈ (CenteredMomentCommonRadialData.commonData s C R d.1).toSource.active d.2.1.1 :=
  ⟨d.2.1.2, d.2.2.1.2⟩

/-- The retained reduction belongs to the literal selected daughter. It is
not the maximum or minimum reduction among its siblings. -/
def PhysicalDaughter.reductionLog {α : Type*} [Fintype α] [DecidableEq α]
    (s : CenteredMomentCommonRadialData.Input α)
    (C R : Ideal HeckeFamily.O) (Ds : Finset (Ideal HeckeFamily.O))
    (Z : ℝ) (d : PhysicalDaughter s C R Ds) : ℝ :=
  Real.logb Z (CenteredMomentDivisorRaw.formalReductionFactor
    d.2.1.1 d.2.2.1.1 (CenteredMomentCommonRadialData.commonData s C R d.1).P)

/-- Select the maximum of the *normalized* actual daughter returns. Source
weights are included before maximization. The whole attaining production
witness remains attached to that same source; all other sources are then
bounded by it with no cardinality multiplier. This is the max-selection step
only: `hproduce` is the regional native producer, not proved by this lemma. -/
theorem exists_normalized_physical_return {α : Type*} [Fintype α] [DecidableEq α]
    (s : CenteredMomentCommonRadialData.Input α)
    (C R : Ideal HeckeFamily.O) (Ds : Finset (Ideal HeckeFamily.O))
    (sourceWeight : PhysicalDaughter s C R Ds → ℝ)
    (hweight : ∀ d, 0 ≤ sourceWeight d)
    (Produce : PhysicalDaughter s C R Ds → ℝ → Prop)
    (hproduce : ∀ d : PhysicalDaughter s C R Ds,
      CenteredMomentCommonLinearNormalization.commonScalar s C R d.1 ≠ 0 →
      ∃ r : ℝ, 0 ≤ r ∧ Produce d r) :
    ∃ Ret : ℝ, 0 ≤ Ret ∧
      ((Ret = 0 ∧ ∀ d : PhysicalDaughter s C R Ds,
          CenteredMomentCommonLinearNormalization.commonScalar s C R d.1 = 0) ∨
        ∃ (d : PhysicalDaughter s C R Ds) (r : ℝ),
          CenteredMomentCommonLinearNormalization.commonScalar s C R d.1 ≠ 0 ∧
          0 ≤ r ∧ Produce d r ∧ Ret = sourceWeight d * r) ∧
      ∀ d : PhysicalDaughter s C R Ds,
        CenteredMomentCommonLinearNormalization.commonScalar s C R d.1 ≠ 0 →
        ∃ r : ℝ, 0 ≤ r ∧ Produce d r ∧ sourceWeight d * r ≤ Ret := by
  obtain ⟨Ret, hRet, hselected, hbound⟩ := exists_weighted_attainer
    (fun d : PhysicalDaughter s C R Ds =>
      CenteredMomentCommonLinearNormalization.commonScalar s C R d.1 ≠ 0)
    (fun d x => ∃ r : ℝ, 0 ≤ r ∧ Produce d r ∧ x = sourceWeight d * r)
    (by
      intro d hd
      obtain ⟨r, hr, hp⟩ := hproduce d hd
      exact ⟨sourceWeight d * r, mul_nonneg (hweight d) hr, r, hr, hp, rfl⟩)
  refine ⟨Ret, hRet, ?_, ?_⟩
  · rcases hselected with hnone | ⟨d, hd, r, hr, hp, heq⟩
    · exact Or.inl ⟨hnone.1, fun d => not_ne_iff.mp (hnone.2 d)⟩
    · exact Or.inr ⟨d, r, hd, hr, hp, heq⟩
  · intro d hd
    obtain ⟨x, _, ⟨r, hr, hp, heq⟩, hx⟩ := hbound d hd
    exact ⟨r, hr, hp, heq ▸ hx⟩

end
end OAI.SevenEighths.Cycle153SourceReturn

#print axioms OAI.SevenEighths.Cycle153SourceReturn.exists_weighted_attainer
#print axioms OAI.SevenEighths.Cycle153SourceReturn.exists_normalized_physical_return
