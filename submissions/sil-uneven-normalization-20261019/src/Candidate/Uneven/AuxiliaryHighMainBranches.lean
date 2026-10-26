import Candidate.Uneven.AuxiliaryHighParameters
import Candidate.Target830.High.BalancedMass
import Candidate.Target830.Parameters
import Candidate.Uneven.AuxiliaryMainLowPhysicalCost
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPhysicalPayment
import Candidate.Cycle63.Physical.InitialMass.SecondFullNormalizedContraction
import Candidate.Cycle63.Physical.InitialMass.GeometryMainSelectedCompleteCost
import Candidate.Uneven.AuxiliaryAcceptedIncumbent
import Candidate.Uneven.AuxiliaryHighAffinePayment
import Candidate.Target830.High.MassMonotonicity
import Candidate.Uneven.AuxiliaryAffineMainLowPayment

/- Original module: Candidate.Uneven.AuxiliaryHighMainCompletePartition. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.AuxiliaryHigh
open TargetHigh830 SaturatedPlain
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentAmplificationChildInput CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondLiveBlock CenteredMomentSourceRow
open LocalMoment CenteredMomentSecondInputCapacitySource CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondEnergySplit ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

theorem main_low_physical_predicate_iff  (second : Bool) (d : Label→SecondInputDatum α) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=> True)→BufferIndex e)
    (r : secondLiveRows (fun l=>(d l).block)) :
    AuxiliaryPhysical.mainLowPhysicalSourcePredicate  (mainLowSourceRows second (d r.val.1) (fun _=> True))
      (select r.val.1 r.val.2.1 r.val.2.2.1) (mainLowSignedRow second r.val.2.2.2.val) ↔
    bufferValue e (mainPhysicalFamilySelector second d select r)<(1+Sil.Uneven.AuxiliarySource.q)/2 := by
  have hz : mainLowSignedRow second r.val.2.2.2.val∈
      mainLowSourceRows second (d r.val.1) (fun _=> True) := by
    apply (mem_main_low_source_rows second _ (fun _=> True) _).mpr
    exact ⟨r.val.2.2.2,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩,rfl,True.intro⟩
  simp only [AuxiliaryPhysical.mainLowPhysicalSourcePredicate,dite_eq_left hz,mainPhysicalFamilySelector]

/-- Exact complementary physical costs on one selector. Both ray sums,
both signed Mellin heights, the lower factor, and all residual divisors remain
literal. No arithmetic-label or allocation count is introduced. -/
theorem actual_main_complete_low_high_partition 
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=> True)→BufferIndex e) :
    (∑l,coefficient l*OAI.SevenEighths.Cycle63InitialMass.mainNormalizedBlockCost N a ap second (d l) t u)=
      AuxiliaryPhysical.mainLowPhysicalCompleteCost  N a ap second d coefficient t u select+
      ∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(d l).block)=>
        (1+Sil.Uneven.AuxiliarySource.q)/2≤ bufferValue e (mainPhysicalFamilySelector second d select r)),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_block_cost_rows]
  rw [←Finset.sum_coe_sort]
  rw [AuxiliaryPhysical.actual_main_low_physical_ordinary_row_cost]
  unfold AuxiliaryPhysical.mainLowPhysicalOrdinaryRows
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have hcost : (∑D∈secondResidualIdeals (fun l=>(d l).block) r.val,
      mainNormalizedPhysicalCost N a ap second d coefficient t u r.val D)=
      (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
        normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
      highNormalizedRowCost second d r
        ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
        ((d r.val.1).block.divisors.filter Squarefree) := by
    rw [actual_second_residual_ideals_label]
    cases second <;> simp [mainNormalizedPhysicalCost,highNormalizedRowCost,Finset.mul_sum]
  rw [hcost]
  have hp:=main_low_physical_predicate_iff  second d select r
  by_cases hl : bufferValue e (mainPhysicalFamilySelector second d select r)<(1+Sil.Uneven.AuxiliarySource.q)/2
  · simp only [hp,hl,ite_true,not_le.mpr hl,ite_false,add_zero]
  · simp only [hp,hl,ite_false,le_of_not_gt hl,ite_true,zero_add]


end
end OAI.SevenEighths.AuxiliaryHigh
end

/- Original module: Candidate.Uneven.AuxiliaryHighMainSelectedPartition. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.AuxiliaryHigh
open TargetHigh830 SaturatedPlain
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource LocalMoment
open CenteredMomentSecondCanonicalScalar
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance selectedPartitionSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- Partition the exact supported first-selection cost on its complete
second family. The low and high bounds share one selector and preserve the
original full-zero filter. No selected-label count is introduced. -/
theorem actual_main_selected_low_high_cost 
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (mass : Label→ℝ) (χ : RayCharacter) (Q : Ideal O) (m : O)
    (a ap : ℝ) (second : Bool) (t₀ u : ℝ) :
    let rows := mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ firstIndex
    let datum := fun r : rows=> geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m ⟨firstIndex r.val.1,r.val.2⟩
    let coefficient := fun r : rows=> mass r.val.1/volume
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t (firstIndex r.val.1))
    ∀(e : ℝ)(select : (r : rows)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (datum r) (fun _=> True)→BufferIndex e)(CL CH : ℝ),
    AuxiliaryPhysical.mainLowPhysicalCompleteCost  N a ap second datum coefficient t₀ u select≤ CL →
    (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(datum l).block)=>
      (1+Sil.Uneven.AuxiliarySource.q)/2≤ bufferValue e (mainPhysicalFamilySelector second datum select r)),
      (coefficient r.val.1*((datum r.val.1).K/lowerFactor N a ap)*
        normalizer (datum r.val.1).C (datum r.val.1).D (datum r.val.1).inactive)*
      highNormalizedRowCost second datum r
        ((datum r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((datum r.val.1).block.divisors.filter Squarefree))≤ CH →
    (∑l,mass l*OAI.SevenEighths.Cycle63InitialMass.geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m a ap second t₀ u (firstIndex l))≤ CL+CH := by
  intro rows datum coefficient e select CL CH hlow hhigh
  have he := actual_main_selected_complete_cost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    hz₁ hz₂ firstIndex mass χ Q m a ap second t₀ u
  change _=(∑r : rows,coefficient r*OAI.SevenEighths.Cycle63InitialMass.mainNormalizedBlockCost N a ap second (datum r) t₀ u) at he
  rw [he,actual_main_complete_low_high_partition  N a ap second datum coefficient t₀ u select]
  exact add_le_add hlow hhigh

end
end OAI.SevenEighths.AuxiliaryHigh
end

/- Original module: Candidate.Uneven.AuxiliaryCostMonotonicity. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.AuxiliaryHigh
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondEnergySplit
open CenteredMomentCommonLinearNormalization CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentSourceRow CenteredMomentSecondLiveBlock
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
open CenteredMomentSectorLocalization LocalMoment Cycle63Moment Cycle63Moment.LowBranch
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]

theorem main_low_complete_cost_mono {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (ha : 0< a) (hap : 0< ap) (second : Bool)
    (d : Label→SecondInputDatum α) (c c' : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=> True)→BufferIndex e)
    (hcc : ∀l,c l≤ c' l) :
    AuxiliaryPhysical.mainLowPhysicalCompleteCost N a ap second d c t u select ≤
      AuxiliaryPhysical.mainLowPhysicalCompleteCost N a ap second d c' t u select := by
  unfold AuxiliaryPhysical.mainLowPhysicalCompleteCost
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  split_ifs
  · unfold mainNormalizedPhysicalCost
    apply mul_le_mul_of_nonneg_right
    · apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right (hcc r.1)
        exact div_nonneg (d r.1).K_pos.le (lowerFactor_pos N a ap ha hap).le
      · exact (normalizer_pos (d r.1).C (d r.1).D (d r.1).hC (d r.1).inactive).le
    · split_ifs <;> exact sq_nonneg _
  · exact le_rfl

end
end OAI.SevenEighths.AuxiliaryHigh
end

/- Original module: Candidate.Uneven.AuxiliaryHighMainBranches. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.AuxiliaryHigh
open TargetHigh830 SaturatedPlain
noncomputable section
open OAI.SevenEighths.Target830
open OAI.SevenEighths.Target830.Source
open OAI.SevenEighths.AuxiliaryPhysical
open OAI.SevenEighths.AuxiliaryPhysical
open OAI.SevenEighths.Cycle63InitialMass OAI.SevenEighths.Cycle63Physical OAI.SevenEighths.Cycle63SecondZero
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands
local notation "O" => HeckeFamily.O
local instance affineMainPaymentSumDecidable {α : Type} : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local irreducible] Finset.univ AuxiliaryPhysical.mainLowPhysicalCompleteCost


variable {α : Type} [Fintype α] [DecidableEq α]

theorem affine_main_two_height_join (CL CH t u : ℝ) (dl dh : ℕ)
    (hCL : 0≤ CL) (hCH : 0≤ CH) :
    (CL*(1+‖t‖)^dl)*(1+‖u‖)^dl+(CH*(1+‖t‖)^dh)*(1+‖u‖)^dh≤
      ((CL+CH)*(1+‖t‖)^(max dl dh))*(1+‖u‖)^(max dl dh) := by
  have ht : 1≤1+‖t‖ := by linarith [norm_nonneg t]
  have hu : 1≤1+‖u‖ := by linarith [norm_nonneg u]
  have hm (C : ℝ) (k : ℕ) (hC : 0≤ C) (hk : k≤ max dl dh) :
      (C*(1+‖t‖)^k)*(1+‖u‖)^k≤
        (C*(1+‖t‖)^(max dl dh))*(1+‖u‖)^(max dl dh) := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hk) hC)
      (pow_le_pow_right₀ hu hk) (pow_nonneg (zero_le_one.trans hu) _)
      (mul_nonneg hC (pow_nonneg (zero_le_one.trans ht) _))
  convert add_le_add (hm CL dl hCL (le_max_left _ _))
    (hm CH dh hCH (le_max_right _ _)) using 1; ring



def GeometryAffineMainSelectedBranches 
    (ε ξ Z amp reserve baseHeight CL CH : ℝ) (dl dh : ℕ) (hZ : 1< Z)
    (reflected : Bool) (s : Input α) (key : ℤ×(Fin 5→ℤ)) (Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter) (Q : Ideal O) (m : O) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) : Prop :=
  ∀(second : Bool)(t₀ u : ℝ),
    let hKfirst:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
    let rows:=firstLiveColumns (geometryFirstSource s 1 1 (Z^(1:ℝ)) Z ξ hKfirst key) (fun _=> logAnnulus)
    let ideal:=fun j : rows=> geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z ξ hKfirst key j.val
    let mass:=fun j : rows=> balancedFirstHighMass reflected s 1 1 Ψ 1 Z ξ ε hKfirst key j.val
    ∀{Label : Type}[Fintype Label](column : Label → rows),
      Function.Injective (fun j=>(geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z ξ hKfirst key (column j).val,
        (column j).val.2.1.val)) →
    ∀alloc : (j : Label)→actualAllocations s.pools (ideal (column j)),
      (∀j,frozenCoefficient (alloc j).val (ideal (column j)) 1 s.ν s.W s.P≠0) →
    let firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z ξ hKfirst key:=
      fun j=>⟨column j,alloc j⟩
    let selected:=mainLowSelectedNonzeroRows reflected s 1 1 Z 1 amp ξ reserve (9/4) baseHeight
      (Fintype.card α) hZ key hz₁ hz₂ firstIndex
    let datum:=fun r : selected=> geometryMainOrdinaryDatum reflected s 1 1 Z 1 amp ξ reserve (9/4)
      baseHeight (Fintype.card α) hZ key hz₁ hz₂ χ Q m ⟨firstIndex r.val.1,r.val.2⟩
    let coefficient:=fun r : selected=> mass (column r.val.1)/volume
      (geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z ξ hKfirst key baseHeight (firstIndex r.val.1))
    ∃e : ℝ,∃select : (r : selected)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (datum r) (fun _=> True)→BufferIndex e,
      AuxiliaryPhysical.mainLowPhysicalCompleteCost  (Fintype.card α) 1 (1/4) second datum coefficient t₀ u select≤
        (CL*(1+‖t₀‖)^dl)*(1+‖u‖)^dl ∧
      (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(datum l).block)=>
        (1+Sil.Uneven.AuxiliarySource.q)/2≤ bufferValue e (mainPhysicalFamilySelector second datum select r)),
        (coefficient r.val.1*((datum r.val.1).K/lowerFactor (Fintype.card α) 1 (1/4))*
          normalizer (datum r.val.1).C (datum r.val.1).D (datum r.val.1).inactive)*
        highNormalizedRowCost second datum r
          ((datum r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
          ((datum r.val.1).block.divisors.filter Squarefree))≤
        (CH*(1+‖t₀‖)^dh)*(1+‖u‖)^dh



theorem affine_main_branch_control_mono (p : Profiles (1/4) (9/4))
    (S S' : Finset (ℕ×ℕ)) (K side x Z target : ℝ) (d D : ℕ)
    (hS : S⊆S') (hK : 0≤ K) (hside : 0≤ side) (hx : 1≤ x) (hZ : 1< Z) (hd : d≤ D) :
    K*(p.control S)^2*side*Z^target*x^d≤
      K*(p.control S')^2*side*Z^target*x^D := by
  have hc:=pow_le_pow_left₀ (p.control_nonneg S) (Cycle63Physical.profile_control_mono p hS) 2
  have hp:=pow_le_pow_right₀ hx hd
  have hz:=Real.rpow_nonneg (zero_lt_one.trans hZ).le target
  gcongr


/-- Enlarging only the scalar branch constants preserves the same selector,
selected carriers, and actual physical costs. -/


theorem affine_main_selected_branches_mono 
    (ε ξ Z amp reserve baseHeight CL CH CL' CH' : ℝ)(dl dh : ℕ)(hZ : 1< Z)
    (reflected : Bool)(s : Input α)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter)(Q : Ideal O)(m : O)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hCL : CL≤ CL')(hCH : CH≤ CH')
    (hbranches : GeometryAffineMainSelectedBranches  ε ξ Z amp reserve baseHeight CL CH dl dh hZ
      reflected s key Ψ χ Q m hz₁ hz₂) :
    GeometryAffineMainSelectedBranches  ε ξ Z amp reserve baseHeight CL' CH' dl dh hZ
      reflected s key Ψ χ Q m hz₁ hz₂ := by
  intro second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf firstIndex selected datum coefficient
  obtain ⟨e,select,hlow,hhigh⟩:=hbranches second t₀ u column hinj alloc hf
  refine ⟨e,select,hlow.trans ?_,hhigh.trans ?_⟩ <;> gcongr






theorem affine_main_selected_branches_common_control 
    (ε ξ Z amp reserve baseHeight KL KH side low high height : ℝ)(dl dh D : ℕ)(hZ : 1< Z)
    (reflected : Bool)(s : Input α)(p : Profiles (1/4) (9/4))
    (SL SH S : Finset (ℕ×ℕ))(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter)(Q : Ideal O)(m : O)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hKL : 0≤ KL)(hKH : 0≤ KH)(hside : 0≤ side)(hheight : 0≤ height)
    (hSL : SL⊆S)(hSH : SH⊆S)(hdl : dl≤ D)(hdh : dh≤ D)
    (hbranches : GeometryAffineMainSelectedBranches  ε ξ Z amp reserve baseHeight
      (KL*(p.control SL)^2*side*Z^low*(1+|baseHeight|+height)^dl)
      (KH*(p.control SH)^2*side*Z^high*(1+|baseHeight|+height)^dh) dl dh hZ
      reflected s key Ψ χ Q m hz₁ hz₂) :
    let control:=(p.control S)^2*side*(1+|baseHeight|+height)^D
    GeometryAffineMainSelectedBranches  ε ξ Z amp reserve baseHeight
      ((KL*control)*Z^low) ((KH*control)*Z^high) dl dh hZ
      reflected s key Ψ χ Q m hz₁ hz₂ := by
  intro control
  have hb : 1≤1+|baseHeight|+height := by linarith [abs_nonneg baseHeight]
  apply affine_main_selected_branches_mono  ε ξ Z amp reserve baseHeight _ _ _ _ dl dh hZ
    reflected s key Ψ χ Q m hz₁ hz₂ _ _ hbranches
  · convert affine_main_branch_control_mono p SL S KL side (1+|baseHeight|+height) Z low dl D
      hSL hKL hside hb hZ hdl using 1;dsimp only [control];ring
  · convert affine_main_branch_control_mono p SH S KH side (1+|baseHeight|+height) Z high dh D
      hSH hKH hside hb hZ hdh using 1;dsimp only [control];ring

omit [DecidableEq α] in


theorem affine_main_amplifier_of_actual_scales 
    (s : Input α)(Z : ℝ)(hZ : 1< Z)(w : α→ℝ)(hP : ∀i,s.P i=Z^(w i)) :
    (1:ℝ)*Sil.Uneven.AuxiliarySource.amp (Sil.Uneven.AuxiliarySource.widthCellUpper ((∑j,Real.logb Z (s.P j))/(1:ℝ)))=
    Sil.Uneven.AuxiliarySource.amp (Sil.Uneven.AuxiliarySource.widthCellUpper (∑i,w i)) := by
  have hsum : (∑i,Real.logb Z (s.P i))=∑i,w i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hP i]
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  simp only [hsum,div_one,one_mul]






variable (M : Ideal O) [NeZero M]
local instance affineMainBranchesQuotient : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

def GeometryAffineMainCanonicalHighReceipt 
    (g : GeometryAffineLowSchedule) (η₀ : Character) (Q : Ideal O) (hQM : Q≤ M)
    (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (Z : ℝ) (hZ : 1< Z) (hT : 2< Z^g.τ)
    (reflected : Bool) (s : Input α) (p : Profiles (1/4) (9/4))
    (amp baseHeight height : ℝ) (key : ℤ×(Fin 5→ℤ)) (Ψ : 𝓢(ℝ,ℂ)) (χ₀ : RayCharacter)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (KH : ℝ) (SH : Finset (ℕ×ℕ)) (dh : ℕ) (highSaving : ℝ) : Prop :=
  ∀(second : Bool)(t₀ u : ℝ),
    let hKfirst:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
    let rows:=firstLiveColumns (geometryFirstSource s 1 1 (Z^(1:ℝ)) Z (g.μ/64) hKfirst key) (fun _=> logAnnulus)
    let ideal:=fun j : rows=> geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64) hKfirst key j.val
    let mass:=fun j : rows=> balancedFirstHighMass reflected s 1 1 Ψ 1 Z (g.μ/64) g.δ hKfirst key j.val
    ∀{Label : Type}[Fintype Label](column : Label → rows),
      Function.Injective (fun j=>(geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (g.μ/64) hKfirst key (column j).val,
        (column j).val.2.1.val)) →
    ∀alloc : (j : Label)→actualAllocations s.pools (ideal (column j)),
      (∀j,frozenCoefficient (alloc j).val (ideal (column j)) 1 s.ν s.W s.P≠0) →
    let firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64) hKfirst key:=
      fun j=>⟨column j,alloc j⟩
    let selected:=mainLowSelectedNonzeroRows reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
      baseHeight (Fintype.card α) hZ key hz₁ hz₂ firstIndex
    let raw:=fun r : selected=> mainLowSelectedDatum reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
      baseHeight (Fintype.card α) hZ key hz₁ hz₂ firstIndex r
    let datum:=fun r : selected=> ordinarySecondDatum (raw r) χ₀ (internalQ Q η₀) fixedBadMask
    let coefficient:=fun r : selected=> mass (column r.val.1)/volume
      (geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64) hKfirst key baseHeight (firstIndex r.val.1))
    ∀(hP : ∀r,(raw r).R*(if second then (raw r).D else (raw r).C)≠0)
      (hPN : ∀r,((((raw r).R*(if second then (raw r).D else (raw r).C)).absNorm:ℝ))≤ Z^(28:ℝ)),
    let canonical:=fun (r : selected)(χ ψ : RayCharacter)=> AuxiliaryPhysical.mainLowCanonicalSelector M H hH
      (raw r) χ₀ χ ψ (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero
      (dvd_mul_right _ _) (dvd_mul_left _ _) Z 28 hZ second (hP r) (hPN r) η₀
      (inf_le_left.trans hQM) inf_le_right g.e (Z^g.τ) g.e_pos hT hβlo hβhi
    (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(datum l).block)=>
      (1+Sil.Uneven.AuxiliarySource.q)/2≤ bufferValue g.e (mainPhysicalFamilySelector second datum canonical r)),
      (coefficient r.val.1*((datum r.val.1).K/lowerFactor (Fintype.card α) 1 (1/4))*
        normalizer (datum r.val.1).C (datum r.val.1).D (datum r.val.1).inactive)*
      highNormalizedRowCost second datum r
        ((datum r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((datum r.val.1).block.divisors.filter Squarefree))≤
      KH*(p.control SH)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*
        Z^(amp+highSaving)*(1+|baseHeight|+height)^dh*(1+‖t₀‖)^dh*(1+‖u‖)^dh



theorem actual_affine_main_selected_branches 
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)
    (ηseed : Character)(SL : Finset (ℕ×ℕ))(dl : ℕ)(KL : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (Z : ℝ)(hlow : AuxiliaryPhysical.GeometryAffineMainLowSpec  (α:=α) M H hH W hW hWs hβlo AuxiliaryLow.incumbent_kappa_bound g ηseed SL dl KL η₀ Q hQM hQ72 Z)
    (hZ : 1< Z)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(tplain X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂)
    (height mesh : ℝ)(hw : ∀i,0≤ w i)(hmesh : 0≤ mesh)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))(hwm : ∀i,w i≤ mesh)
    (hheight : 0≤ height)(hfreq : ∀i,|freq i|≤ height)(hT : 2< Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hlo₁ : (81/200:ℝ)≤ length Z X₁)(hlo₂ : (81/200:ℝ)≤ length Z X₂)
    (hhi₁ : length Z X₁≤(45/100:ℝ))(hhi₂ : length Z X₂≤(45/100:ℝ))
    (hslots : (1/50:ℝ)≤∑i,w i ∧ (∑i,w i)≤7/250)
    (hcone : length Z X₁+length Z X₂+Sil.Uneven.AuxiliarySource.lambda*(∑i,w i)≤ Sil.Uneven.AuxiliarySource.B)
    (reflected : Bool)(baseHeight : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))(χ₀ : RayCharacter)
    (KH : ℝ)(SH : Finset (ℕ×ℕ))(dh : ℕ)(highSaving : ℝ) :
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=AuxiliaryPhysical.affine_main_low_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=AuxiliaryPhysical.affine_main_low_profile_zero p 1
    let amp:=(1:ℝ)*Sil.Uneven.AuxiliarySource.amp (Sil.Uneven.AuxiliarySource.widthCellUpper ((∑j,Real.logb Z (s.P j))/(1:ℝ)))
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    GeometryAffineMainCanonicalHighReceipt M H hH  g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT
      reflected s p amp baseHeight height key Ψ χ₀ hz₁ hz₂ KH SH dh highSaving →
    GeometryAffineMainSelectedBranches  g.δ (g.μ/64) Z amp (g.μ/8) baseHeight
      (KL*(p.control SL)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*
        Z^(lowTarget  g (Fintype.card α) amp omega mesh)*(1+|baseHeight|+height)^dl)
      (KH*(p.control SH)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*
        Z^(amp+highSaving)*(1+|baseHeight|+height)^dh)
      dl dh hZ reflected s key Ψ χ₀ (internalQ Q η₀) fixedBadMask hz₁ hz₂ := by
  intro s hz₁ hz₂ amp omega hhigh second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf firstIndex selected datum coefficient
  have hb:=hlow hZ θ w σ freq hσ bΦ state hη p tplain X₁ X₂ hX₁ hX₂ height mesh
    hw hmesh hmeshcap hwm hheight hfreq hT hβhi hlo₁ hlo₂ hhi₁ hhi₂ hslots hcone
    reflected second key baseHeight firstIndex hf hinj (fun _=>χ₀) fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Ψ t₀ u
  obtain ⟨hP,hPN,hpaid⟩:=hb
  have hh:=hhigh second t₀ u column hinj alloc hf hP hPN
  refine ⟨g.e,_,?_,hh⟩
  let oldCoefficient := fun r : selected=> geometryFirstHighMass reflected s 1 1 Ψ 1 Z (g.μ/64) g.δ
      hKfirst key (column r.val.1).val / volume
        (geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64) hKfirst key baseHeight (firstIndex r.val.1))
  apply le_trans (main_low_complete_cost_mono  (Fintype.card α) 1 (1/4)
    (by norm_num) (by norm_num) second datum coefficient oldCoefficient t₀ u _ ?_) ?_
  · intro r
    exact div_le_div_of_nonneg_right
      (balanced_first_high_mass_le reflected s 1 1 Ψ 1 Z (g.μ/64) g.δ hKfirst key
        (column r.val.1).val hZ) (CenteredMomentExceptionalAmplitudePair.volume_pos _).le
  · simpa only [Real.norm_eq_abs, datum, oldCoefficient, firstIndex,
      geometryMainOrdinaryDatum, mainLowSelectedDatum, Cycle63InitialMass.mainLowCanonicalSelector,
      AuxiliaryPhysical.mainLowCanonicalSelector] using hpaid




end
end OAI.SevenEighths.AuxiliaryHigh
end
