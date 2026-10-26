import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.CommonStageSupply
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.OriginalSlotPartition
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.SmallSlotDiscard
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open Cycle63CommonSupply Cycle63MarkedPlain CenteredMomentSourceLiveColumn
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two common allocations and the tiny-slot discard consume at most the supply loss of the
original logarithmic width, which is at least `e`. -/
theorem eventual_geometry_large_slot_supply (N : ℕ) (a wmin : ℝ)
    (ha : 0<a)(hmin : 0 ≤ wmin)(hsmall : (N:ℝ)*wmin ≤ Cycle63.Optimization.tinySlotLoss) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(s : Input ι),Fintype.card ι ≤ N → a ≤ s.lower →
    ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁),
    frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0 →
    ∀(χ : Character)(t : ℝ)(C₂ R₂ : Ideal O)
      (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂),
    (let first:=child s C₁ R₁ B₁ χ t;
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0) →
    ∀w : ι→ℝ,(∀j,s.P j=Z^(w j)) → (∀j,0 ≤ w j) →
    ∀e : ℝ,e ≤ ∑j,w j → (∑j,w j) ≤ Cycle63.Optimization.slotTop →
    let slots:=originalSlots (fun j : liveIndices B₂.val=>j.val.val)
    let large:=largeSlots slots w wmin
    0 ≤ ∑j∈large,w j ∧ (∑j∈large,w j) ≤ Cycle63.Optimization.slotTop ∧
      e-Cycle63.Optimization.supplyLoss ≤
        Real.logb Z (C₁.absNorm:ℝ)+Real.logb Z (C₂.absNorm:ℝ)+∑j∈large,w j := by
  filter_upwards [eventual_two_stage_supplied_width (ι:=ι) N a Cycle63.Optimization.commonAllocationLoss ha
    Cycle63.Optimization.commonAllocationLoss_pos] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hcard hs C₁ R₁ B₁ hf₁ χ t C₂ R₂ B₂ hf₂ w hscale hw e hsupply hupper slots large
  have hcommon:=hZ.2 s hcard hs C₁ R₁ B₁ hf₁ χ t C₂ R₂ B₂ hf₂ w hscale
  have hid : (∑j : liveIndices B₂.val,w j.val.val)=∑j∈slots,w j :=
    double_subtype_sum (liveIndices B₁.val) (liveIndices B₂.val) w
  rw [hid] at hcommon
  have hlarge:=large_width_lower slots w wmin N ((Finset.card_le_univ _).trans hcard) hmin
  refine ⟨Finset.sum_nonneg (fun j _=>hw j),?_,?_⟩
  · exact (Finset.sum_le_univ_sum_of_nonneg hw).trans hupper
  · change (∑j∈slots,w j)-(N:ℝ)*wmin ≤ ∑j∈large,w j at hlarge
    unfold Cycle63.Optimization.supplyLoss
    linarith only [hcommon,hlarge,hsmall,hsupply]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
