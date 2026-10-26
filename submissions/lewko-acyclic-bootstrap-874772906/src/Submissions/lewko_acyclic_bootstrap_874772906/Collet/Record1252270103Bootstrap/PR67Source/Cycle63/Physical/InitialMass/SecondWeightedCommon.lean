import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondFamily
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.FirstProjectorMultiplicity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonLinearNormalization CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
local instance secondWeightedSelectionDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Keep the actual scalar and common-ideal normalization inside the joint
energy. Only the uniformly bounded allocation mass is taken outside. -/
theorem actual_second_weighted_common_selection {α : Type*} [Fintype α] [DecidableEq α]
    (b ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→Finset α)
      (s : (k : κ)→ Input (slots k)) (C R : κ→ Ideal O) (Ds : κ→Finset (Ideal O))
      (z : κ→O) (scalar : κ→ℂ) (E : ℝ),
      (∀k∈rows,(s k).upper≤b) → (∀k∈rows,C k≠0) →
      (∀S : Finset rows,
        ∀pick : (k : S)→actualAllocations (s k.val.val).pools (C k.val.val),
        (∀k,commonScalar (s k.val.val) (C k.val.val) (R k.val.val) (pick k)≠0) →
        (∑k : S,(‖scalar k.val.val‖^2*(∏i,(s k.val.val).M i)^2*((C k.val.val).absNorm:ℝ)^(ε-1))*
          (∑L∈Ds k.val.val,
          ∑a∈(commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k)).toSource.active L,
            retainedAllocationCost (commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k))
              L a (z k.val.val)))≤E) →
      (∑k∈rows,‖scalar k‖^2*∑L∈Ds k,commonRetainedCost (s k) (C k) (R k) L (z k))≤
        K*E := by
  have hbound := uniform_common_scalar_mass (Fintype.card α) b ε hε
  obtain ⟨K,hK,hbound⟩ := hbound
  refine ⟨K,hK,?_⟩
  intro κ rows slots s C R Ds z scalar E hupper hC hjoint
  let mass (k : rows) := (∏i,(s k.val).M i)^2*((C k.val).absNorm:ℝ)^(ε-1)
  have hmpos (k : rows) : 0< mass k := by
    have hp : 0<∏i,(s k.val).M i := Finset.prod_pos (fun i _=>lt_of_lt_of_le zero_lt_one ((s k.val).M_ge_one i))
    have hn := CenteredMomentFirstScale.norm_pos (C k.val) (hC k.val k.property)
    dsimp [mass]
    exact mul_pos (sq_pos_of_pos hp) (Real.rpow_pos_of_pos hn _)
  let cost (k : rows)(B : actualAllocations (s k.val).pools (C k.val)) :=
    ∑L∈Ds k.val,∑a∈(commonData (s k.val) (C k.val) (R k.val) B).toSource.active L,
      retainedAllocationCost (commonData (s k.val) (C k.val) (R k.val) B) L a (z k.val)
  have hcpos (k : rows)(B : actualAllocations (s k.val).pools (C k.val)) : 0≤ cost k B :=
    Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>retained_allocation_cost_nonneg _ _ _ _))
  have hh:=joint_supported_weighted_selection
    (fun (k : rows)(B : actualAllocations (s k.val).pools (C k.val))=>
      (((actualAllocations (s k.val).pools (C k.val)).card:ℝ)*‖commonScalar (s k.val) (C k.val) (R k.val) B‖^2)/mass k)
    (fun (k : rows)(B : actualAllocations (s k.val).pools (C k.val))=>
      (‖scalar k.val‖^2*mass k)*cost k B)
    K E hK.le (fun k _=>div_nonneg (by positivity) (hmpos k).le)
    (fun k B=>mul_nonneg (mul_nonneg (sq_nonneg _) (hmpos k).le) (hcpos k B))
    (by
      intro k
      rw [←Finset.sum_div,←Finset.mul_sum]
      apply (div_le_iff₀ (hmpos k)).mpr
      simpa only [mass,mul_assoc] using hbound (ι:=slots k.val) (by simpa using Finset.card_le_univ (slots k.val))
        (s k.val) (hupper k.val k.property) (C k.val) (R k.val) (hC k.val k.property))
    (by
      intro S pick hne
      simpa only [mass,cost,mul_assoc] using hjoint S pick (fun k hc=>hne k (by simp [hc])))
  have hcancel (k : rows)(B : actualAllocations (s k.val).pools (C k.val)) :
      (((actualAllocations (s k.val).pools (C k.val)).card:ℝ)*‖commonScalar (s k.val) (C k.val) (R k.val) B‖^2)/mass k*
        ((‖scalar k.val‖^2*mass k)*cost k B)=
      (‖scalar k.val‖^2*((actualAllocations (s k.val).pools (C k.val)).card:ℝ)*
        ‖commonScalar (s k.val) (C k.val) (R k.val) B‖^2)*cost k B := by
    field_simp [(hmpos k).ne']
  simp_rw [hcancel] at hh
  apply le_trans (le_of_eq ?_) hh
  dsimp only [cost]
  rw [Finset.sum_coe_sort rows (fun k=>∑B : actualAllocations (s k).pools (C k),
    (‖scalar k‖^2*((actualAllocations (s k).pools (C k)).card:ℝ)*
      ‖commonScalar (s k) (C k) (R k) B‖^2)*
    (∑L∈Ds k,∑a∈(commonData (s k) (C k) (R k) B).toSource.active L,
      retainedAllocationCost (commonData (s k) (C k) (R k) B) L a (z k)))]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [commonRetainedCost,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
