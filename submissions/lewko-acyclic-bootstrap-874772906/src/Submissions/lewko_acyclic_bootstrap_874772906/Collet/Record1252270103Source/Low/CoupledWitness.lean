/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.CoupledEnergy
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.CommonRounded

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentRemainingBox
open CenteredMomentRectangle CenteredMomentFirstSectors Record1252270103Source
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The literal selected common summand, with the squarefree pair and entire
corrected column multiplier still inside its finite coefficient. -/
def coupledCommonColumn (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (A₁ A₂ D : Ideal O) (F : Ideal O → ℂ) (a : Ideal O) : ℂ :=
  frozenCoefficient B.val C R s.ν s.W s.P *
    finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
      (coupledLiveProfile A₁ A₂ D F B.val C R s.ν s.W s.P s.W₁ s.W₂
        s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) a

/-- An arbitrary remaining-tuple modifier stays inside the exact finite sum.
This includes the ordinary-only small-prime hole and further literal masks. -/
def modifiedCoupledCommonColumn (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (A₁ A₂ D : Ideal O) (F : Ideal O → ℂ)
    (modifier : Tuple (liveIndices B.val) → ℂ) (a : Ideal O) : ℂ :=
  frozenCoefficient B.val C R s.ν s.W s.P *
    finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
      (fun v=>modifier v*coupledLiveProfile A₁ A₂ D F B.val C R s.ν s.W s.P s.W₁ s.W₂
        s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 v) a

theorem modifiedCoupledCommonColumn_one (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (A₁ A₂ D : Ideal O) (F : Ideal O → ℂ) (a : Ideal O) :
    modifiedCoupledCommonColumn s C R B A₁ A₂ D F (fun _=>1) a =
      coupledCommonColumn s C R B A₁ A₂ D F a := by
  simp only [modifiedCoupledCommonColumn,coupledCommonColumn,one_mul]

/-- Exact nonzero tuple witness in the literal remaining box. Its product is
the selected column, and its coupled multiplier and original profile are both
nonzero. This conclusion never replaces a sum by its uncoupled counterpart. -/
theorem coupled_first_common_tuple (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (A₁ A₂ D : Ideal O) (F : Ideal O → ℂ)
    (modifier : Tuple (liveIndices B.val) → ℂ) (a : Ideal O)
    (hne : modifiedCoupledCommonColumn s C R B A₁ A₂ D F modifier a ≠ 0) :
    frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 ∧
    ∃ v : Tuple (liveIndices B.val),v ∈ liveBox s.pools B.val (alloc_ne s C B) ∧
      finiteTupleProduct v = a ∧ modifier v ≠ 0 ∧
      coupledFactor (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) (D*C) F v ≠ 0 ∧
      liveProfile B.val C R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 v ≠ 0 ∧
      ∀j : Fin 2,v (Sum.inr j) ≠ 0 := by
  obtain ⟨hfrozen,hcolumn⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨v,hv,hvne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcolumn
  obtain ⟨hv,hprod⟩ := Finset.mem_filter.mp hv
  obtain ⟨hmodifier,hvlive⟩ := mul_ne_zero_iff.mp hvne
  refine ⟨hfrozen,v,hv,hprod,hmodifier,(mul_ne_zero_iff.mp hvlive).1,(mul_ne_zero_iff.mp hvlive).2,?_⟩
  intro j
  have hv' := hv
  simp only [liveBox,Fintype.mem_piFinset] at hv'
  have hp := hv' (Sum.inr j)
  change v (Sum.inr j) ∈ residualPool (B.val (Sum.inr j)) (alloc_ne s C B _) (s.pools (Sum.inr j)) at hp
  exact right_ne_zero_of_mul (s.pools_ne (Sum.inr j) _ ((mem_residualPool _ _ _ _).mp hp))

/-- A nonzero centered rectangle has one supported pair. No assertion is made
that its uncoupled column sum is nonzero. -/
theorem idealRectangle_nonzero_pair (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (I J : Ideal O)
    (hne : idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J ≠ 0) :
    (W₁ ((I.absNorm:ℝ)/X₁) ≠ 0 ∧ W₂ ((J.absNorm:ℝ)/X₂) ≠ 0) ∨
    (W₁ ((I.absNorm:ℝ)/Y₁) ≠ 0 ∧ W₂ ((J.absNorm:ℝ)/Y₂) ≠ 0) := by
  by_cases hx : W₁ ((I.absNorm:ℝ)/X₁)*W₂ ((J.absNorm:ℝ)/X₂) = 0
  · apply Or.inr
    apply mul_ne_zero_iff.mp
    intro hy
    exact hne (by simp only [idealRectangle,hx,hy,sub_self])
  · exact Or.inl (mul_ne_zero_iff.mp hx)

/-- A nonzero finite coupled column has an actual remaining tuple whose
literal centered profile is nonzero. Cancellation in the uncoupled sum is
irrelevant to this witness. -/
theorem coupled_first_common_support (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (A₁ A₂ D : Ideal O) (F : Ideal O → ℂ)
    (modifier : Tuple (liveIndices B.val) → ℂ) (a : Ideal O)
    (hne : modifiedCoupledCommonColumn s C R B A₁ A₂ D F modifier a ≠ 0) :
    frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 ∧
    ∃ I J : Ideal O,I ≠ 0 ∧ J ≠ 0 ∧
      ((s.W₁ ((I.absNorm:ℝ)/(s.X₁/(B.val (Sum.inr 0)).absNorm)) ≠ 0 ∧
        s.W₂ ((J.absNorm:ℝ)/(s.X₂/(B.val (Sum.inr 1)).absNorm)) ≠ 0) ∨
       (s.W₁ ((I.absNorm:ℝ)/(s.Y₁/(B.val (Sum.inr 0)).absNorm)) ≠ 0 ∧
        s.W₂ ((J.absNorm:ℝ)/(s.Y₂/(B.val (Sum.inr 1)).absNorm)) ≠ 0)) := by
  obtain ⟨hfrozen,v,hv,hprod,hmodifier,hfactor,hprofile,hi⟩ :=
    coupled_first_common_tuple s C R B A₁ A₂ D F modifier a hne
  have hrect : idealRectangle s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂
      (B.val (Sum.inr 0)*v (Sum.inr 0)) (B.val (Sum.inr 1)*v (Sum.inr 1)) ≠ 0 := by
    have hh := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprofile).1).2
    simpa only [one_mul] using hh
  refine ⟨hfrozen,v (Sum.inr 0),v (Sum.inr 1),hi 0,hi 1,?_⟩
  have hh := idealRectangle_nonzero_pair s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ _ _ hrect
  simpa only [map_mul,Nat.cast_mul,div_div_eq_mul_div,mul_comm] using hh

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.coupled_first_common_tuple
#print axioms QRH.Record1252270103Low.coupled_first_common_support
