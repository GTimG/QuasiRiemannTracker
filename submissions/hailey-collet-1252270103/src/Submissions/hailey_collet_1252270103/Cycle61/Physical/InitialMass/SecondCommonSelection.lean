import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondFamily
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.FirstProjectorMultiplicity

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
local instance secondSelectionDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Common-allocation selection after residual shells have been summed,
including the actual outside scalar and different surviving slot sets. -/
theorem actual_heterogeneous_common_cost_selection {α κ : Type*}
    [Fintype α] [DecidableEq α] (rows : Finset κ) (slots : κ→Finset α)
    (s : (k : κ)→Input (slots k)) (C R : κ→Ideal O) (Ds : κ→Finset (Ideal O))
    (z : κ→O) (scalar : κ→ℂ) (W E : ℝ) (hW : 0≤W)
    (hmass : ∀k∈rows,‖scalar k‖^2*((actualAllocations (s k).pools (C k)).card:ℝ)*
      (∑B : actualAllocations (s k).pools (C k),‖commonScalar (s k) (C k) (R k) B‖^2)≤W)
    (hjoint : ∀S : Finset rows,
      ∀pick : (k : S)→actualAllocations (s k.val.val).pools (C k.val.val),
      (∀k,commonScalar (s k.val.val) (C k.val.val) (R k.val.val) (pick k)≠0) →
      (∑k : S,∑L∈Ds k.val.val,
        ∑a∈(commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k)).toSource.active L,
          retainedAllocationCost (commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k))
            L a (z k.val.val))≤E) :
    (∑k∈rows,‖scalar k‖^2*∑L∈Ds k,commonRetainedCost (s k) (C k) (R k) L (z k))≤W*E := by
  have hh := joint_supported_weighted_selection
    (fun (k : rows) (B : actualAllocations (s k.val).pools (C k.val))=>
      ‖scalar k.val‖^2*((actualAllocations (s k.val).pools (C k.val)).card:ℝ)*
        ‖commonScalar (s k.val) (C k.val) (R k.val) B‖^2)
    (fun (k : rows) (B : actualAllocations (s k.val).pools (C k.val))=>
      ∑L∈Ds k.val,∑a∈(commonData (s k.val) (C k.val) (R k.val) B).toSource.active L,
        retainedAllocationCost (commonData (s k.val) (C k.val) (R k.val) B) L a (z k.val))
    W E hW (fun _ _=>by positivity)
    (fun _ _=>Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>
      retained_allocation_cost_nonneg _ _ _ _)))
    (fun k=>by rw [←Finset.mul_sum];exact hmass k.val k.property)
    (fun S pick hne=>hjoint S pick (fun k hc=>hne k (by simp [hc])))
  apply le_trans (le_of_eq ?_) hh
  rw [Finset.sum_coe_sort rows (fun k=>∑B : actualAllocations (s k).pools (C k),
    (‖scalar k‖^2*((actualAllocations (s k).pools (C k)).card:ℝ)*
      ‖commonScalar (s k) (C k) (R k) B‖^2)*
    (∑L∈Ds k,∑a∈(commonData (s k) (C k) (R k) B).toSource.active L,
      retainedAllocationCost (commonData (s k) (C k) (R k) B) L a (z k)))]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [commonRetainedCost,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

theorem actual_second_common_mass_selection {α : Type*} [Fintype α] [DecidableEq α]
    (b ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→Finset α)
      (s : (k : κ)→Input (slots k)) (C R : κ→Ideal O) (Ds : κ→Finset (Ideal O))
      (z : κ→O) (scalar : κ→ℂ) (G E : ℝ),0≤G →
      (∀k∈rows,(s k).upper≤b) → (∀k∈rows,C k≠0) →
      (∀k∈rows,‖scalar k‖^2*(∏i,(s k).M i)^2*((C k).absNorm:ℝ)^(ε-1)≤G) →
      (∀S : Finset rows,
        ∀pick : (k : S)→actualAllocations (s k.val.val).pools (C k.val.val),
        (∀k,commonScalar (s k.val.val) (C k.val.val) (R k.val.val) (pick k)≠0) →
        (∑k : S,∑L∈Ds k.val.val,
          ∑a∈(commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k)).toSource.active L,
            retainedAllocationCost (commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k))
              L a (z k.val.val))≤E) →
      (∑k∈rows,‖scalar k‖^2*∑L∈Ds k,commonRetainedCost (s k) (C k) (R k) L (z k))≤
        (K*G)*E := by
  obtain ⟨K,hK,hbound⟩ := uniform_common_scalar_mass (Fintype.card α) b ε hε
  refine ⟨K,hK,?_⟩
  intro κ rows slots s C R Ds z scalar G E hG hupper hC hscalar hjoint
  apply actual_heterogeneous_common_cost_selection rows slots s C R Ds z scalar (K*G) E
    (mul_nonneg hK.le hG) _ hjoint
  intro k hk
  have hh := hbound (ι:=slots k) (by simpa using Finset.card_le_univ (slots k))
    (s k) (hupper k hk) (C k) (R k) (hC k hk)
  calc
    _=‖scalar k‖^2*(((actualAllocations (s k).pools (C k)).card:ℝ)*
      ∑B : actualAllocations (s k).pools (C k),‖commonScalar (s k) (C k) (R k) B‖^2) := by ring
    _≤‖scalar k‖^2*(K*(∏i,(s k).M i)^2*((C k).absNorm:ℝ)^(ε-1)) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _=K*(‖scalar k‖^2*(∏i,(s k).M i)^2*((C k).absNorm:ℝ)^(ε-1)) := by ring
    _≤K*G := mul_le_mul_of_nonneg_left (hscalar k hk) hK.le

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_heterogeneous_common_cost_selection
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_common_mass_selection
