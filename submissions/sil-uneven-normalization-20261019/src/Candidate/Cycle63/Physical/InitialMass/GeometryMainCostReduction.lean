/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainNormalized

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

/-- The complete positive column cost of one physical datum. Both ray
indices and the entire retained frequency set remain inside this cost. -/
def mainNormalizedBlockCost {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (a ap : ℝ) (reflected : Bool) (d : SecondInputDatum α) (t u : ℝ) : ℝ :=
  (d.K/lowerFactor N a ap)*normalizer d.C d.D d.inactive*
    (∑χ : RayCharacter,∑ψ : RayCharacter,
      ∑D∈d.block.divisors.filter Squarefree,∑z∈secondLiveColumnRows d.block,
        if reflected then
          ‖normalizedColumn (withHeight d.input (d.τ ψ⁻¹)
            (d.input.t+2*Real.pi*(u-(-t)))) d.D d.hD d.R d.seed D (-z.val)‖^2
        else
          ‖normalizedColumn (withHeight d.input (d.τ χ)
            (d.input.t+2*Real.pi*(u-t))) d.C d.hC d.R d.seed D z.val‖^2)

theorem main_normalized_block_cost_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (a ap : ℝ) (ha : 0<a) (hap : 0<ap)
    (reflected : Bool) (d : SecondInputDatum α) (t u : ℝ) :
    0≤mainNormalizedBlockCost N a ap reflected d t u := by
  unfold mainNormalizedBlockCost
  apply mul_nonneg
  · exact mul_nonneg (div_nonneg d.K_pos.le (lowerFactor_pos N a ap ha hap).le)
      (normalizer_pos d.C d.D d.hC d.inactive).le
  · apply Finset.sum_nonneg; intro χ _
    apply Finset.sum_nonneg; intro ψ _
    apply Finset.sum_nonneg; intro D _
    apply Finset.sum_nonneg; intro z _
    split_ifs <;> exact sq_nonneg _

/-- Pay the actual effective weight once, leaving a complete block cost
which can be selected before any row, projector or frequency choice. -/
theorem actual_main_normalized_block_cost {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (a ap : ℝ) (ha : 0<a) (hap : 0<ap)
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ))
    (hcard : Fintype.card α≤N) (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0→ap≤x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0→ap≤x)
    (reflected : Bool) (t u : ℝ) :
    secondNormalizedSum reflected d
      (secondEffectiveWeight (fun l=>(d l).block) w W) t u≤
      ∑l,‖w l‖*mainNormalizedBlockCost N a ap reflected (d l) t u := by
  apply (actual_main_effective_normalized_columns N a ap ha hap d w W
    hcard hlower hW₁ hW₂ reflected t u).trans_eq
  simp only [mainNormalizedBlockCost,Finset.mul_sum,mul_assoc]

/-- A nonnegative physical coefficient majorant can replace the norm
of the original complex block weight without changing the column cost. -/
theorem actual_main_normalized_coefficient_cost {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (a ap : ℝ) (ha : 0<a) (hap : 0<ap)
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ))
    (coefficient : Label→ℝ) (hw : ∀l,‖w l‖≤coefficient l)
    (hcard : Fintype.card α≤N) (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0→ap≤x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0→ap≤x)
    (reflected : Bool) (t u : ℝ) :
    secondNormalizedSum reflected d
      (secondEffectiveWeight (fun l=>(d l).block) w W) t u≤
      ∑l,coefficient l*mainNormalizedBlockCost N a ap reflected (d l) t u := by
  apply (actual_main_normalized_block_cost N a ap ha hap d w W
    hcard hlower hW₁ hW₂ reflected t u).trans
  exact Finset.sum_le_sum (fun l _=>mul_le_mul_of_nonneg_right (hw l)
    (main_normalized_block_cost_nonneg N a ap ha hap reflected (d l) t u))

/-- Finite disintegration keeps an arbitrary original-block filter inside
each complete first-index cost. -/
theorem filtered_sigma_weighted_cost {I : Type*} [Fintype I]
    {J : I→Type*} [∀i,Fintype (J i)] [DecidableEq (Sigma J)]
    (live : Finset (Sigma J)) (weight vol : I→ℝ) (cost : Sigma J→ℝ) :
    (∑q : live,weight q.val.1/vol q.val.1*cost q.val)=
      ∑i,weight i*((∑j : J i,if (⟨i,j⟩ : Sigma J)∈live then cost ⟨i,j⟩ else 0)/vol i) := by
  classical
  rw [Finset.sum_coe_sort live (fun q=>weight q.1/vol q.1*cost q)]
  calc
    _=(∑q : Sigma J,if q∈live then weight q.1/vol q.1*cost q else 0) := by
      rw [←Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    _=_ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring

/-- The fixed cardinality bound can replace the actual slot count in an
allocation weight. This leaves the underlying allocation and filter intact. -/
theorem geometry_allocation_weight_mono {α : Type*} [Fintype α] [DecidableEq α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (n N : ℕ) (hn : n≤N) (b : ℝ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j)) :
    geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight n b j B ≤
    geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B := by
  unfold geometryAllocationWeight
  dsimp only
  split_ifs
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (le_max_left 1 b) hn) (Nat.cast_nonneg _)
  · exact le_rfl

section Literal
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainCostSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
variable (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)

/-- All original-nonzero second blocks belonging to one first allocation
are kept together. The original nonzero test precedes the ordinary filter. -/
def geometryMainFirstCost (χ : RayCharacter) (Q : Ideal O) (m : O)
    (slotlo plainlo : ℝ) (second : Bool) (t₀ u : ℝ)
    (j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) : ℝ :=
  (∑n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key j,
    if (⟨j,n⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)∈
        geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂
    then mainNormalizedBlockCost N slotlo plainlo second
      (geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
        hz₁ hz₂ χ Q m ⟨j,n⟩) t₀ u
    else 0) /
    volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t j)

theorem geometry_main_first_cost_nonneg (χ : RayCharacter) (Q : Ideal O) (m : O)
    (slotlo plainlo : ℝ) (hslot : 0<slotlo) (hplain : 0<plainlo)
    (second : Bool) (t₀ u : ℝ)
    (j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) :
    0≤geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo second t₀ u j := by
  apply div_nonneg _ (CenteredMomentAmplificationChildInput.volume_pos _).le
  apply Finset.sum_nonneg
  intro n _
  split_ifs
  · exact main_normalized_block_cost_nonneg N slotlo plainlo hslot hplain second _ t₀ u
  · exact le_refl _

/-- Exact first-allocation disintegration of the complete positive cost.
No count of first ideal labels, allocations or second labels is introduced. -/
theorem actual_main_first_cost_disintegration
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (slotlo plainlo Mprice Aprice : ℝ)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (second : Bool) (t₀ u : ℝ) :
    (∑j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂,
      geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.val.1 *
      mainNormalizedBlockCost N slotlo plainlo second
        (geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m j.val) t₀ u) =
    ∑j : firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) (fun _=>logAnnulus),
      ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.val),
        geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight (Fintype.card α) b j.val B *
        geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨j,B⟩ := by
  let live := geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂
  let weights := fun j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key=>
    geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight (Fintype.card α) b j.1.val j.2
  let vol := fun j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key=>
    CenteredMomentAmplificationChildInput.volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t j)
  let cost := fun j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key=>
    mainNormalizedBlockCost N slotlo plainlo second
      (geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
        hz₁ hz₂ χ Q m j) t₀ u
  let First := GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key
  let Second := fun j : First=>GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key j
  have hh : (∑q : live,weights q.val.1/vol q.val.1*cost q.val)=
      ∑j : First,weights j*((∑n : Second j,if (⟨j,n⟩ : Sigma Second)∈live then cost ⟨j,n⟩ else 0)/vol j) :=
    @filtered_sigma_weighted_cost First (inferInstance : Fintype First)
      Second (fun j=>inferInstance) (inferInstance : DecidableEq (Sigma Second)) live weights vol cost
  calc
    _ = ∑j : First,weights j*((∑n : Second j,if (⟨j,n⟩ : Sigma Second)∈live then cost ⟨j,n⟩ else 0)/vol j) := hh
    _ = _ := by
      rw [Fintype.sum_sigma]
      rfl

/-- The original-nonzero ordinary main family is reduced to one complete
cost per first allocation. The standard first-allocation mass selector can
now choose allocations and injective first labels using exactly this cost. -/
theorem actual_geometry_main_first_cost
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (Mprice Aprice slotlo plainlo : ℝ) (hslot : 0<slotlo) (hplain : 0<plainlo)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (hcard : Fintype.card α≤N) (hlower : slotlo≤s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→plainlo≤x) (hW₂ : ∀x,s.W₂ x≠0→plainlo≤x)
    (W : 𝓢(ℝ,ℂ)) (second : Bool) (t₀ u : ℝ) :
    let datum := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
      geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m j.val
    let w := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
      geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j.val
    secondNormalizedSum second datum (secondEffectiveWeight (fun j=>(datum j).block) w W) t₀ u≤
    ∑j : firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) (fun _=>logAnnulus),
      ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.val),
        geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight (Fintype.card α) b j.val B *
        geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨j,B⟩ := by
  intro datum w
  have hh := actual_main_normalized_coefficient_cost N slotlo plainlo hslot hplain datum w W
    (fun j=>geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t j.val.1)
    (fun j=>actual_geometry_main_block_weight_norm reflected s R seed Z Mrow amp ξ reserve b t
      N hZ key Mprice Aprice weight j.val)
    hcard (fun _=>hlower) (fun _=>hW₁) (fun _=>hW₂) second t₀ u
  exact hh.trans_eq (actual_main_first_cost_disintegration reflected s R seed Z Mrow amp ξ
    reserve b t N hZ key hz₁ hz₂ χ Q m slotlo plainlo Mprice Aprice weight second t₀ u)

/-- Uniform-slot-count form for the fixed first-allocation selector. -/
theorem actual_geometry_main_first_cost_uniform
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (Mprice Aprice slotlo plainlo : ℝ) (hslot : 0<slotlo) (hplain : 0<plainlo)
    (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
    (hcard : Fintype.card α≤N) (hlower : slotlo≤s.lower)
    (hW₁ : ∀x,s.W₁ x≠0→plainlo≤x) (hW₂ : ∀x,s.W₂ x≠0→plainlo≤x)
    (W : 𝓢(ℝ,ℂ)) (second : Bool) (t₀ u : ℝ) :
    let datum := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
      geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m j.val
    let w := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
      geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j.val
    secondNormalizedSum second datum (secondEffectiveWeight (fun j=>(datum j).block) w W) t₀ u≤
    ∑j : firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) (fun _=>logAnnulus),
      ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.val),
        geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight N b j.val B *
        geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨j,B⟩ := by
  intro datum w
  apply (actual_geometry_main_first_cost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    hz₁ hz₂ χ Q m Mprice Aprice slotlo plainlo hslot hplain weight hcard hlower hW₁ hW₂ W second t₀ u).trans
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro B _
  exact mul_le_mul_of_nonneg_right
    (geometry_allocation_weight_mono reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight (Fintype.card α) N hcard b j.val B)
    (geometry_main_first_cost_nonneg reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo hslot hplain second t₀ u ⟨j,B⟩)

end Literal

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.main_normalized_block_cost_nonneg
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_normalized_block_cost
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_normalized_coefficient_cost
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_main_first_cost_nonneg
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_first_cost_disintegration
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_main_first_cost

#print axioms OAI.SevenEighths.Cycle63InitialMass.filtered_sigma_weighted_cost
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_allocation_weight_mono
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_main_first_cost_uniform
