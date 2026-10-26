/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B123
import Candidate.Bundles.B133
import Candidate.Bundles.B152
import Candidate.Bundles.B161
import Candidate.Bundles.B170
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondActualWidth

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighCoarseGates; sha256 1f3ba4b3f785f435b164c5def412baf46b60eba8754f48fa5ddd970e6767871e -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                 
                                                        
                                                            

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale
open CenteredMomentFirstCanonicalFamily Cycle61Moment
open CenteredMomentFirstPhysicalSource CenteredMomentSecondRadicalBudget
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondActualWidth CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius
local notation "O" => HeckeFamily.O

/-- Fixed dictionary and profile logarithms are absorbed before any moving
source, allocation, ray, or retained row is chosen. -/
theorem eventual_high_fixed_width_cost (η : Character) (N : ℕ) (b ε : ℝ)
    (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧
      Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost+
        2*(N:ℝ)*Real.logb Z b+Real.logb Z (4*(fixedFactor:ℝ))≤ε := by
  let c:=Real.log (η.modulus.absNorm:ℝ)+Real.log fixedPresentationCost+
    2*(N:ℝ)*Real.log b+Real.log (4*(fixedFactor:ℝ))
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (c/ε)),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  have he : Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z fixedPresentationCost+
      2*(N:ℝ)*Real.logb Z b+Real.logb Z (4*(fixedFactor:ℝ))=c/Real.log Z := by
    dsimp only [Real.logb,c]
    ring
  rw [he]
  exact (div_le_iff₀ (Real.log_pos hZ)).mpr
    (by nlinarith [(div_le_iff₀ hε).mp hc])

/-- Width-one original sources have a common retained-width ceiling of two.
The inactive ideal is paid by the common frequency generator, not by its
coarse source-norm cap. All arithmetic labels follow the eventual threshold. -/
theorem eventual_high_width_one_gate (η : Character) (N : ℕ) (b : ℝ) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀(C D : Ideal O)(_hC : Supported C)(U : Finset (CommonIndex C D))
        (c e a reserve ξ : ℝ),0≤ a → 0≤ reserve → 0≤ξ → ξ≤1 →
      (Real.logb Z Z+Real.logb Z (η.modulus.absNorm:ℝ)-max (c-e) 0-6*a-
        frequencyLoss Z 32 ξ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏p∈U,p.val).absNorm:ℝ))+
      (Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z (4*(fixedFactor:ℝ)))≤2 := by
  filter_upwards [eventual_high_fixed_width_cost η N b (1/2) (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro C D hC U c e a reserve ξ ha hr hξ hξ1
  have hcommon:=actual_common_log_ge_unit C D hC U Z hz.1
  have hfreq:=frequencyLoss_nonneg Z 32 ξ hz.1 (by norm_num) hξ
  have hlog : Real.logb Z Z=1 := by
    exact Real.logb_self_eq_one hz.1
  rw [hlog]
  linarith [hz.2,le_max_right (c-e) 0]

/-- A small coordinate box suffices for the larger high-density ceiling.
The lower-volume correction changes only coordinate zero. -/
theorem high_child_coordinate_ceiling (reflected left second : Bool)
    (l : FirstSourceLabel)(hC : Supported l.1.1)(hD : Supported l.1.2)
    (C D : Ideal O)(hC₂ : Supported C)(hD₂ : Supported D)
    (heq : primeSupport C=primeSupport D)(U : Finset (CommonIndex C D))
    (Z M A a ξ reserve ε εv width : ℝ)(hZ : 1< Z)
    (hfirst : (l.1.1.absNorm:ℝ)≤ Z^(4:ℝ) ∧ (l.1.2.absNorm:ℝ)≤ Z^(4:ℝ))
    (hsecond : (C.absNorm:ℝ)≤ Z^(4:ℝ) ∧ (D.absNorm:ℝ)≤ Z^(4:ℝ))
    (hM : |M|≤4)(hA : |A|≤4)(ha : |a|≤4)
    (hω : |frequencyLoss Z 32 ξ+reserve|≤4)(hε : |ε|≤4)(hwidth : width≤1) :
    childHighCoordinates (actualHighCoordinates reflected left second l C D U
      Z M A a ξ reserve ε) εv 2+width≤130 := by
  have hh:=(actual_high_coordinate_box reflected left second l hC hD C D hC₂ hD₂
    heq U Z M A a ξ reserve ε 4 hZ (by norm_num) hfirst hsecond hM hA ha hω hε 2).2
  simp only [childHighCoordinates,show (2:Fin 4)≠0 by decide,ite_false,add_zero]
  linarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_high_fixed_width_cost
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_high_width_one_gate
#print axioms OAI.SevenEighths.Cycle61InitialMass.high_child_coordinate_ceiling

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighCoarseGates -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCostPartition; sha256 f8310304a4574ca29bc0a9fe9ef77447e32b0bc2892ac6a3a97f840448e3d456 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             
                                                        
                                                         

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
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
open CenteredMomentWholeDivisorShell
open CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

section Literal
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainCostPartitionSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
variable (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)


/-- The selected first cost is expanded without changing its original
nonzero filter. Complete second blocks remain inside each first index. -/
theorem actual_geometry_selected_cost_disintegration {Label : Type*} [Fintype Label]
    (first : Label → GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (mass : Label → ℝ) (χ : RayCharacter) (Q : Ideal O) (m : O)
    (slotlo plainlo : ℝ) (second : Bool) (t₀ u : ℝ) :
    (∑j,mass j*geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo second t₀ u (first j))=
    ∑j,∑n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key (first j),
      if (⟨first j,n⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)∈
          geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂
      then mass j/volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t (first j))*
        mainNormalizedBlockCost N slotlo plainlo second
          (geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
            hz₁ hz₂ χ Q m ⟨first j,n⟩) t₀ u
      else 0 := by
  apply Finset.sum_congr rfl
  intro j hj
  simp only [geometryMainFirstCost,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> ring

end Literal
section Rows
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- Literal normalized column cost, indexed by the actual physical row.
The reflected side changes both the ray character and the raw frequency. -/
def mainNormalizedPhysicalCost (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : Label → SecondInputDatum α) (coefficient : Label → ℝ) (t u : ℝ)
    (r : SecondRow (fun l=>(d l).block)) (D : Ideal O) : ℝ :=
  coefficient r.1*((d r.1).K/lowerFactor N a ap)*normalizer (d r.1).C (d r.1).D (d r.1).inactive*
    (if second then
      ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
        ((d r.1).input.t+2*Real.pi*(u-(-t))))
        (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed D (-r.2.2.2.val)‖^2
    else
      ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
        ((d r.1).input.t+2*Real.pi*(u-t)))
        (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed D r.2.2.2.val‖^2)

/-- All rays and physical frequencies survive the block-to-row reindex. -/
theorem actual_main_block_cost_rows (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : Label → SecondInputDatum α) (coefficient : Label → ℝ) (t u : ℝ) :
    (∑l,coefficient l*mainNormalizedBlockCost N a ap second (d l) t u)=
      ∑r∈secondLiveRows (fun l=>(d l).block),
        ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
          mainNormalizedPhysicalCost N a ap second d coefficient t u r D := by
  rw [actual_second_column_reindex]
  simp only [mainNormalizedBlockCost,mainNormalizedPhysicalCost,Finset.mul_sum,mul_assoc]

/-- The union of the complete family's second projectors is formed before
norm-shell grouping. The original membership test remains inside each shell. -/
theorem actual_main_block_cost_shared_shells (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : Label → SecondInputDatum α) (coefficient : Label → ℝ) (t u : ℝ) :
    let rows := secondLiveRows (fun l=>(d l).block)
    let Ds := fun r : rows=>secondResidualIdeals (fun l=>(d l).block) r.val
    (∑l,coefficient l*mainNormalizedBlockCost N a ap second (d l) t u)=
      ∑n∈selectedShells (sharedProjectors Ds),∑r : rows,
        ∑D∈shell (sharedProjectors Ds) n,
          if D∈Ds r then mainNormalizedPhysicalCost N a ap second d coefficient t u r.val D else 0 := by
  intro rows Ds
  rw [actual_main_block_cost_rows]
  rw [←Finset.sum_coe_sort rows]
  apply shared_projector_shell_sum Ds
  intro r D hD
  exact (mem_second_residual_ideals (fun l=>(d l).block) r.val D).mp hD |>.2

end Rows

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_cost_disintegration
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_block_cost_rows
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_block_cost_shared_shells

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainCostPartition -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowRows; sha256 b61a3e53727831e17e41a2e2534eabc08418ca8cfa8f30a445f726ee110d5309 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
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
open Cycle61FinalNatural CenteredMomentEnergyState Cycle61Moment.LowBranch
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondInputCapacitySource CenteredMomentSecondHeightFamily Cycle61Moment
open CenteredMomentFirstDiscardedEnergy LocalMoment
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainLowRowsSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The original, unrestricted block fixes its common allocation and row
witness once. No nonzero ordinary or low block is required. -/
theorem actual_geometry_main_low_choices
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂)
    (second : Bool) :
    let d:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.val.1 hz₁ hz₂ j.val.2
    ∃B₂ : actualAllocations d.input.pools (if second then d.D else d.C),
      ∃_rwitness : secondLiveRows (fun _:Unit=>d.block),
        frozenCoefficient B₂.val (if second then d.D else d.C) d.R
          d.input.ν d.input.W d.input.P≠0 ∧ d.inactive∈inactiveSubsets d.C d.D := by
  intro d
  obtain ⟨B₂,hB₂⟩ := actual_geometry_main_live_common_allocation
    reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ j second
  obtain ⟨hr,hU⟩ := actual_geometry_main_original_admission
    reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ j
  obtain ⟨r,hr⟩ := hr
  exact ⟨B₂,⟨r,hr⟩,hB₂,hU⟩

/-- Reflection acts only on the row and selected ray; it never requests
closure of the original finite source row set under negation. -/
def mainLowSignedRow (second : Bool) (z : O) : O := if second then -z else z

theorem main_low_signed_row_injective (second : Bool) :
    Function.Injective (mainLowSignedRow second) := by
  cases second
  · exact Function.injective_id
  · exact neg_injective

/-- Complete signed physical rows on a fixed pair of rays. The predicate
may select one literal buffered bin; no row or label multiplicity is lost. -/
def mainLowSourceRows (second : Bool) (d : SecondInputDatum α)
    (low : O→ Prop) : Finset O :=
  ((secondLiveColumnRows d.block).filter (fun z=>low (mainLowSignedRow second z.val))).image
    (fun z=>mainLowSignedRow second z.val)

theorem mem_main_low_source_rows (second : Bool) (d : SecondInputDatum α)
    (low : O→ Prop) (z : O) :
    z∈mainLowSourceRows second d low ↔
      ∃x∈secondLiveColumnRows d.block,mainLowSignedRow second x.val=z ∧ low z := by
  simp only [mainLowSourceRows,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨x,⟨hx,hl⟩,he⟩
    exact ⟨x,hx,he,he ▸ hl⟩
  · rintro ⟨x,hx,he,hl⟩
    exact ⟨x,⟨hx,he.symm ▸ hl⟩,he⟩

theorem main_low_source_sum (second : Bool) (d : SecondInputDatum α)
    (low : O→ Prop) (f : O→ℝ) :
    (∑x∈secondLiveColumnRows d.block,
      if low (mainLowSignedRow second x.val) then f (mainLowSignedRow second x.val) else 0)=
      ∑z∈mainLowSourceRows second d low,f z := by
  rw [mainLowSourceRows,Finset.sum_image]
  · exact (Finset.sum_filter _ _).symm
  · intro x _ y _ h
    exact Subtype.ext ((main_low_signed_row_injective second) h)

/-- The ordinary physical filter provides both the natural keep gate and
unit weight domination by the actual radial profile. -/
theorem actual_main_low_source_admission
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1< Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤ Z^Bmask)
    (low : O→ Prop) (z : O)
    (hz : z∈mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) low) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    st.radial.keep z ∧ low z ∧
      1≤(st.radial.profile (normValue z/st.radial.scale)).re := by
  obtain ⟨x,hx,he,hl⟩ := (mem_main_low_source_rows _ _ _ _).mp hz
  have ha := actual_main_ordinary_row_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN x.val x.property
  change _ ∧ _ ∧ _
  rw [←he]
  exact ⟨ha.1,he.symm ▸ hl,ha.2⟩

/-- A supported row in a strict low buffered bin satisfies the genuine
whole-family low predicate, at that bin's next height. -/
theorem actual_main_low_bin_admission
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : st.fixedModulus≤ M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e)
    (hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p)
    (hlow : bufferValue e p<21/25)
    (hweight : 1≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) :
    ActualLow M H hH st η₀ hQM hQη (21/25) e (3*(p.1.val+1:ℕ)*T) z := by
  apply hbin.2.2.2.2.2.2.2.2.1 hlow
  intro heq
  rw [heq] at hweight
  norm_num at hweight

/-- Choose actual buffered bins on every complete signed ordinary row at
this fixed ray pair. Constants and allocations are not chosen per frequency. -/
theorem actual_main_low_buffered_rows
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1< Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤ Z^Bmask)
    (η₀ : Character) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    let rows:=mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)
    ∃select : rows→ BufferIndex e,∀z : rows,
      st.radial.keep z.val ∧
      1≤(st.radial.profile (normValue z.val/st.radial.scale)).re ∧
      (bufferValue e (select z)<21/25 →
        ActualLow M H hH st η₀ hQM hQη (21/25) e
          (3*((select z).1.val+1:ℕ)*T) z.val) := by
  intro st rows
  have ha (z : rows) := actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN (fun _=>True) z.val z.property
  have hp (z : rows) := actual_geometry_zero_partition M H hH st η₀ hQM hQη
    z.val (ha z).1 e T he hT hβlo hβhi
  let select : rows→ BufferIndex e := fun z=>Classical.choose (hp z)
  refine ⟨select,?_⟩
  intro z
  refine ⟨(ha z).1,(ha z).2.2,?_⟩
  intro hl
  apply actual_main_low_bin_admission M H hH st η₀ hQM hQη z.val (ha z).1 e T
    (select z) (Classical.choose_spec (hp z)) hl
  simpa only [normValue_eq_embedding] using (ha z).2.2

section Costs
variable {Label : Type*} [Fintype Label]
/-- Low filtering commutes with the exact physical row disintegration.
Each first coefficient and original-block label stays inside its own sum. -/
theorem actual_main_low_physical_cost_reindex
    (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : Label→ SecondInputDatum α) (coefficient : Label→ℝ) (t u : ℝ)
    (low : Label→ RayCharacter→ RayCharacter→ O→ Prop) :
    (∑r∈secondLiveRows (fun l=>(d l).block),
      ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
      if low r.1 r.2.1 r.2.2.1 (mainLowSignedRow second r.2.2.2.val) then
        mainNormalizedPhysicalCost N a ap second d coefficient t u r D else 0)=
    ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
      ∑D∈(d l).block.divisors.filter Squarefree,
        (coefficient l*((d l).K/lowerFactor N a ap)*
          normalizer (d l).C (d l).D (d l).inactive)*
        ∑z∈mainLowSourceRows second (d l) (low l χ ψ),
          ‖normalizedColumn
            (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
              ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
            (if second then (d l).D else (d l).C)
            (by cases second; exact (d l).hC; exact (d l).hD)
            (d l).R (d l).seed D z‖^2 := by
  rw [actual_second_column_reindex]
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro χ _
  apply Finset.sum_congr rfl; intro ψ _
  apply Finset.sum_congr rfl; intro D _
  rw [←main_low_source_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  cases second
  · simp only [mainNormalizedPhysicalCost,mainLowSignedRow]
    split_ifs <;> simp only [mul_zero]
  · simp only [mainNormalizedPhysicalCost,mainLowSignedRow,ite_true]
    split_ifs <;> simp only [mul_zero]
end Costs
end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_low_choices
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_low_source_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_source_admission
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_bin_admission
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_physical_cost_reindex
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_low_buffered_rows

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowRows -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighRows; sha256 6617e99c3a05fc5f14b96e4f5dd6f45159c6d87c73b8350d02a3710f5b1136fe -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                       

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSourceRow
open Cycle61FinalNatural CenteredMomentEnergyState Cycle61Moment.LowBranch
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentFiniteProfileExceptional
open LocalMoment
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainHighRowsSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The inclusive high cut keeps both literal buffered height intervals.
No zero, character, puncture or row is replaced by an abstract datum. -/
theorem actual_main_high_bin_intervals
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : st.fixedModulus≤ M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e)
    (hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p)
    (hhigh : 21/25≤ bufferValue e p) :
    21/25≤ bufferValue e p ∧ bufferValue e p≤7/8 ∧
      bufferValue e p≤ geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3*p.1.val:ℕ)*T) ∧
      geometryRowMaximum M H hH st η₀ hQM hQη z hz ((3*p.1.val:ℕ)*T)< bufferValue e p+e ∧
      bufferValue e p≤ geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T) ∧
      geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T)< bufferValue e p+2*e := by
  obtain ⟨_,_,_,hb,hcl,hcu,hnl,hnu,_⟩ := hbin
  exact ⟨hhigh,hb,hcl,hcu,hnl,hnu⟩

/-- The complete signed ordinary row set has actual buffered bins. The
high source filter can use this one selector on each fixed physical ray pair;
the same keep witness is retained in all zero-maximum gates. -/
theorem actual_main_high_buffered_rows
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1< Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ)≤ Z^Bmask)
    (η₀ : Character) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    let rows:=mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=>True)
    ∃keep : ∀z : rows,st.radial.keep z.val,
    ∃select : rows→ BufferIndex e,∀z : rows,
      1≤(st.radial.profile (normValue z.val/st.radial.scale)).re ∧
      st.radial.profile (normValue z.val/st.radial.scale)≠0 ∧ z.val≠0 ∧
      GeometryZeroBin M H hH st η₀ hQM hQη z.val (keep z) e T (select z) ∧
      (21/25≤ bufferValue e (select z) →
        21/25≤ bufferValue e (select z) ∧ bufferValue e (select z)≤7/8 ∧
        bufferValue e (select z)≤ geometryRowMaximum M H hH st η₀ hQM hQη
          z.val (keep z) ((3*(select z).1.val:ℕ)*T) ∧
        geometryRowMaximum M H hH st η₀ hQM hQη z.val (keep z)
          ((3*(select z).1.val:ℕ)*T)< bufferValue e (select z)+e ∧
        bufferValue e (select z)≤ geometryRowMaximum M H hH st η₀ hQM hQη
          z.val (keep z) (3*((select z).1.val+1:ℕ)*T) ∧
        geometryRowMaximum M H hH st η₀ hQM hQη z.val (keep z)
          (3*((select z).1.val+1:ℕ)*T)< bufferValue e (select z)+2*e) := by
  intro st rows
  have ha (z : rows) := actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN (fun _=>True) z.val z.property
  let keep : ∀z : rows,st.radial.keep z.val := fun z=>(ha z).1
  have hp (z : rows) := actual_geometry_zero_partition M H hH st η₀ hQM hQη
    z.val (keep z) e T he hT hβlo hβhi
  let select : rows→ BufferIndex e := fun z=>Classical.choose (hp z)
  refine ⟨keep,select,?_⟩
  intro z
  have hs : st.radial.profile (normValue z.val/st.radial.scale)≠0 := by
    intro hzero
    have hb := (ha z).2.2
    rw [hzero] at hb
    norm_num at hb
  have hbin := Classical.choose_spec (hp z)
  exact ⟨(ha z).2.2,hs,st.row_ne_zero z.val (keep z),hbin,
    actual_main_high_bin_intervals M H hH st η₀ hQM hQη z.val (keep z) e T (select z) hbin⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_high_bin_intervals
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_high_buffered_rows

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighRows -/
