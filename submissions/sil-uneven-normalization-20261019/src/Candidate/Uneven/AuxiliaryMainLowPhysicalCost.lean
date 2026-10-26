/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliarySchedule
import Candidate.Uneven.AuxiliaryLowPaidMain
import Candidate.Uneven.AuxiliaryMainLowSelectedCost
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPhysicalPayment
import Candidate.Uneven.AuxiliaryLowPaidMain
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowQuantitativePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowNormalizedPayment
import Candidate.Cycle63.Physical.InitialMass.SecondLowSourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryShiftedHeight
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.AuxiliaryPhysical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.AuxiliaryLow
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle63FinalNatural Cycle63Moment.LowBranch
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment LocalMoment
open CenteredMomentSecondInputCapacitySource
open CenteredMomentChildRows CenteredMomentSecondCanonical CenteredMomentSecondEnergySplit
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

local notation "O" => HeckeFamily.O
local instance geometryMainLowPhysicalDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _


theorem mainLowPhysicalSupported  (second : Bool) (d : SecondInputDatum α) :
    Supported (if second then d.D else d.C) := by
  cases second
  · exact d.hC
  · exact d.hD

/-- Extend the literal selector only to express an ordinary finite-set
filter. No unsupported row receives a buffered-bin certificate. -/
def mainLowPhysicalSourcePredicate  (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (z : O) : Prop :=
  if hz : z∈rows then bufferValue e (select ⟨z,hz⟩) < ((1+Sil.Uneven.AuxiliarySource.q)/2) else False

theorem main_low_physical_source_sum  (second : Bool) (d : SecondInputDatum α)
    {e : ℝ} (select : mainLowSourceRows second d (fun _=>True)→BufferIndex e)
    (f : O→ℝ) :
    (∑z∈mainLowSourceRows second d
      (mainLowPhysicalSourcePredicate  (mainLowSourceRows second d (fun _=>True)) select),f z)=
    ∑z : mainLowSourceRows second d (fun _=>True),
      if bufferValue e (select z) < ((1+Sil.Uneven.AuxiliarySource.q)/2) then f z.val else 0 := by
  let rows:=mainLowSourceRows second d (fun _=>True)
  have heq : mainLowSourceRows second d (mainLowPhysicalSourcePredicate  rows select)=
      rows.filter (mainLowPhysicalSourcePredicate  rows select) := by
    ext z
    simp only [Finset.mem_filter]
    change (_ ↔ z∈mainLowSourceRows second d (fun _=>True) ∧ _)
    simp only [mem_main_low_source_rows]
    constructor
    · rintro ⟨x,hx,he,hl⟩
      exact ⟨⟨x,hx,he,True.intro⟩,hl⟩
    · rintro ⟨⟨x,hx,he,_⟩,hl⟩
      exact ⟨x,hx,he,hl⟩
  rw [heq,Finset.sum_filter]
  change (∑z∈rows,if mainLowPhysicalSourcePredicate  rows select z then f z else 0)=_
  rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro z _
  simp only [mainLowPhysicalSourcePredicate,dite_eq_left z.property]

/-- The complete fixed-ray physical low cost. The original block label
may already carry its full-nonzero filter; restriction never tests a new
ordinary-block norm. Both actual rays and signed source rows are retained. -/
def mainLowPhysicalCompleteCost  {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) : ℝ :=
  ∑r∈secondLiveRows (fun l=>(d l).block),
    ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
      if mainLowPhysicalSourcePredicate  (mainLowSourceRows second (d r.1) (fun _=>True))
          (select r.1 r.2.1 r.2.2.1) (mainLowSignedRow second r.2.2.2.val) then
        mainNormalizedPhysicalCost N a ap second d coefficient t u r D else 0

/-- Exact source-to-physical transport. The physical lower factor is
outside the complete source sum; no child volume or normalizer is lost. -/
theorem actual_main_low_complete_physical_reindex  {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    mainLowPhysicalCompleteCost  N a ap second d coefficient t u select=
      (1/lowerFactor N a ap)*
      ∑χ : RayFourExpansion.RayCharacter,∑ψ : RayFourExpansion.RayCharacter,
        mainLowCompleteSelectedCost 
          (fun l=>mainLowSourceRows second (d l) (fun _=>True))
          (fun l=>select l χ ψ) (fun l=>(d l).block.divisors.filter Squarefree)
          (fun l _=>coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive)
          (fun l D z=>‖normalizedColumn
            (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
              ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
            (if second then (d l).D else (d l).C)
            (mainLowPhysicalSupported  second (d l))
            (d l).R (d l).seed D z‖^2) := by
  unfold mainLowPhysicalCompleteCost
  rw [actual_main_low_physical_cost_reindex N a ap second d coefficient t u
    (fun l χ ψ=>mainLowPhysicalSourcePredicate  (mainLowSourceRows second (d l) (fun _=>True)) (select l χ ψ))]
  have hsources : ∀l χ ψ D,
      (∑z∈mainLowSourceRows second (d l)
        (mainLowPhysicalSourcePredicate  (mainLowSourceRows second (d l) (fun _=>True))
          (select l χ ψ)),
        ‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
          (if second then (d l).D else (d l).C)
          (mainLowPhysicalSupported  second (d l))
          (d l).R (d l).seed D z‖^2)=
      ∑z : mainLowSourceRows second (d l) (fun _=>True),
        if bufferValue e (select l χ ψ z) < ((1+Sil.Uneven.AuxiliarySource.q)/2) then
          ‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
            ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
            (if second then (d l).D else (d l).C)
            (mainLowPhysicalSupported  second (d l))
            (d l).R (d l).seed D z.val‖^2 else 0 := by
    intro l χ ψ D
    exact main_low_physical_source_sum  second (d l) (select l χ ψ) _
  simp_rw [hsources]
  rw [←Finset.sum_comm]
  apply congrArg (fun x=>x) -- stage the second ray before the label sum
  calc
    _=∑χ : RayFourExpansion.RayCharacter,∑ψ : RayFourExpansion.RayCharacter,
        ∑l,∑D∈(d l).block.divisors.filter Squarefree,
          (coefficient l*((d l).K/lowerFactor N a ap)*normalizer (d l).C (d l).D (d l).inactive)*
          (∑z : mainLowSourceRows second (d l) (fun _=>True),
            if bufferValue e (select l χ ψ z) < ((1+Sil.Uneven.AuxiliarySource.q)/2) then
              ‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
                ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
                (if second then (d l).D else (d l).C)
                (mainLowPhysicalSupported  second (d l))
                (d l).R (d l).seed D z.val‖^2 else 0) := by
      apply Finset.sum_congr rfl
      intro χ _
      exact Finset.sum_comm
    _=_ := by
      unfold mainLowCompleteSelectedCost
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ψ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D _
      ring

/-- Fixed rays and a complete original live column, before any frequency
choice. This is the literal physical summand used by the buffered partition. -/
def mainLowFixedRayPhysicalCost  {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (l : Label)→mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) : ℝ :=
  ∑l,∑D∈(d l).block.divisors.filter Squarefree,
    ∑z∈secondLiveColumnRows (d l).block,
      if mainLowPhysicalSourcePredicate  (mainLowSourceRows second (d l) (fun _=>True))
          (select l) (mainLowSignedRow second z.val) then
        mainNormalizedPhysicalCost N a ap second d coefficient t u ⟨l,χ,ψ,z⟩ D else 0

theorem actual_main_low_fixed_ray_physical_reindex  {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (l : Label)→mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    mainLowFixedRayPhysicalCost  N a ap second d coefficient t u χ ψ select=
      (1/lowerFactor N a ap)*mainLowCompleteSelectedCost 
        (fun l=>mainLowSourceRows second (d l) (fun _=>True)) select
        (fun l=>(d l).block.divisors.filter Squarefree)
        (fun l _=>coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive)
        (fun l D z=>‖normalizedColumn
          (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
            ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
          (if second then (d l).D else (d l).C)
          (mainLowPhysicalSupported  second (d l))
          (d l).R (d l).seed D z‖^2) := by
  unfold mainLowFixedRayPhysicalCost mainLowCompleteSelectedCost
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  have hfactor : ∀z,
      (if mainLowPhysicalSourcePredicate  (mainLowSourceRows second (d l) (fun _=>True))
          (select l) (mainLowSignedRow second z.val) then
        mainNormalizedPhysicalCost N a ap second d coefficient t u ⟨l,χ,ψ,z⟩ D else 0)=
      (coefficient l*((d l).K/lowerFactor N a ap)*normalizer (d l).C (d l).D (d l).inactive)*
      (if mainLowPhysicalSourcePredicate  (mainLowSourceRows second (d l) (fun _=>True))
          (select l) (mainLowSignedRow second z.val) then
        ‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
          (if second then (d l).D else (d l).C)
          (mainLowPhysicalSupported  second (d l))
          (d l).R (d l).seed D (mainLowSignedRow second z.val)‖^2 else 0) := by
    intro z
    cases second <;> simp only [mainNormalizedPhysicalCost,mainLowSignedRow,ite_true]
    all_goals split_ifs <;> simp only [mul_zero]
  simp_rw [hfactor]
  rw [←Finset.mul_sum,main_low_source_sum second (d l)
    (mainLowPhysicalSourcePredicate  (mainLowSourceRows second (d l) (fun _=>True)) (select l))
    (fun z=>‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
      ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
      (if second then (d l).D else (d l).C)
      (mainLowPhysicalSupported  second (d l)) (d l).R (d l).seed D z‖^2),
    main_low_physical_source_sum ]
  ring


theorem fixed_ray_source_transport  {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (l : Label)→mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e)
    (c : Label→Ideal O→ℝ) (value : Label→Ideal O→O→ℝ) (bound : ℝ)
    (hlower : 0 < lowerFactor N a ap)
    (hc : ∀l D,coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive=c l D)
    (hv : ∀l D z,‖normalizedColumn
      (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
        ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
      (if second then (d l).D else (d l).C)
      (mainLowPhysicalSupported  second (d l))
      (d l).R (d l).seed D z‖^2=value l D z)
    (hb : mainLowCompleteSelectedCost  (fun l=>mainLowSourceRows second (d l) (fun _=>True))
      select (fun l=>(d l).block.divisors.filter Squarefree) c value ≤ bound) :
    mainLowFixedRayPhysicalCost  N a ap second d coefficient t u χ ψ select ≤ 
      (1/lowerFactor N a ap)*bound := by
  rw [actual_main_low_fixed_ray_physical_reindex ]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1/lowerFactor N a ap)
  have heq : mainLowCompleteSelectedCost  (fun l=>mainLowSourceRows second (d l) (fun _=>True))
      select (fun l=>(d l).block.divisors.filter Squarefree)
      (fun l _=>coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive)
      (fun l D z=>‖normalizedColumn
        (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
        (if second then (d l).D else (d l).C)
        (mainLowPhysicalSupported  second (d l))
        (d l).R (d l).seed D z‖^2)=
      mainLowCompleteSelectedCost  (fun l=>mainLowSourceRows second (d l) (fun _=>True))
        select (fun l=>(d l).block.divisors.filter Squarefree) c value := by
    have hceq : (fun l (_ : Ideal O)=>coefficient l*(d l).K*
        normalizer (d l).C (d l).D (d l).inactive)=c := by
      funext l D
      exact hc l D
    have hveq : (fun l D z=>‖normalizedColumn
        (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
        (if second then (d l).D else (d l).C)
        (mainLowPhysicalSupported  second (d l))
        (d l).R (d l).seed D z‖^2)=value := by
      funext l D z
      exact hv l D z
    rw [hceq,hveq]
  exact heq ▸ hb

attribute [local irreducible] mainLowFixedRayPhysicalCost mainLowCompleteSelectedCost
  selectedFirstProjectors


set_option maxHeartbeats 320000 in

/-- All fixed rays share the same first projector union. A shell payment
therefore incurs its norm-dyad count once, after both ray sums. -/
theorem main_low_physical_complete_ray_sum  {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    mainLowPhysicalCompleteCost  N a ap second d coefficient t u select=
      ∑χ : RayFourExpansion.RayCharacter,∑ψ : RayFourExpansion.RayCharacter,
        mainLowFixedRayPhysicalCost  N a ap second d coefficient t u χ ψ
          (fun l=>select l χ ψ) := by
  rw [actual_main_low_complete_physical_reindex ,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ψ _
  exact (actual_main_low_fixed_ray_physical_reindex  N a ap second d coefficient t u χ ψ _).symm



/-- The complete ordinary low subset, before any projector grouping.
The row's block label is unchanged, including its original-nonzero subtype. -/
def mainLowPhysicalOrdinaryRows  {Label : Type*} [Fintype Label]
    (second : Bool) (d : Label→SecondInputDatum α) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    Finset (secondLiveRows (fun l=>(d l).block)) :=
  Finset.univ.filter (fun r=>mainLowPhysicalSourcePredicate 
    (mainLowSourceRows second (d r.val.1) (fun _=>True))
    (select r.val.1 r.val.2.1 r.val.2.2.1) (mainLowSignedRow second r.val.2.2.2.val))

/-- The exact physical cost is the normalized row family consumed by the
all-height splice. The height retains both signed Mellin shifts. -/
theorem actual_main_low_physical_ordinary_row_cost  {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    mainLowPhysicalCompleteCost  N a ap second d coefficient t u select=
      ∑r∈mainLowPhysicalOrdinaryRows  second d select,
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  unfold mainLowPhysicalCompleteCost mainLowPhysicalOrdinaryRows
  rw [Finset.sum_filter,←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro r _
  rw [actual_second_residual_ideals_label]
  by_cases hp : mainLowPhysicalSourcePredicate 
      (mainLowSourceRows second (d r.val.1) (fun _=>True))
      (select r.val.1 r.val.2.1 r.val.2.2.1) (mainLowSignedRow second r.val.2.2.2.val)
  · simp only [hp,ite_true]
    cases second <;> simp [mainNormalizedPhysicalCost,highNormalizedRowCost,Finset.mul_sum]
  · simp only [hp,ite_false,Finset.sum_const_zero]

private theorem ordinary_physical_divisors  (d : SecondInputDatum α)
    (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (m : O) :
    (ordinarySecondDatum d χ Q m).block.divisors=d.block.divisors := rfl

set_option maxHeartbeats 320000 in
/-- Ordinary low rows are transported to the original source family
before the genuine coarse theorem. The original label/ray/frequency image
is injective; an ordinary block need not be nonzero. -/
theorem actual_main_low_physical_original_row_cost  {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (χ₀ : Label→RayFourExpansion.RayCharacter) (Q : Label→Ideal O) (m : Label→O)
    (hrows : ∀l,(d l).rows=sourceRows
      (d l).C (d l).D (d l).inactive (d l).radius)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (ordinarySecondDatum (d l) (χ₀ l) (Q l) (m l))
        (fun _=>True)→BufferIndex e) :
    mainLowPhysicalCompleteCost  N a ap second
      (fun l=>ordinarySecondDatum (d l) (χ₀ l) (Q l) (m l)) coefficient t u select=
      ∑r∈(mainLowPhysicalOrdinaryRows  second
        (fun l=>ordinarySecondDatum (d l) (χ₀ l) (Q l) (m l)) select).image
          (ordinaryHighOriginalRow d χ₀ Q m hrows),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_low_physical_ordinary_row_cost ]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro r _
    rw [ordinary_high_original_row_cost]
    have hlabel : (ordinaryHighOriginalRow d χ₀ Q m hrows r).val.1=r.val.1 := rfl
    rw [hlabel]
    have hdiv:=ordinary_physical_divisors  (d r.val.1) (χ₀ r.val.1) (Q r.val.1) (m r.val.1)
    rw [hdiv]
    congr 1
  · intro r _ z _ heq
    exact ordinary_high_original_row_injective d χ₀ Q m hrows heq

/-- Inclusion of a selected original block-label family into the full
second family. Both rays and the literal frequency are unchanged. -/
def mainLowOriginalLabelRow  {Label Original : Type*} [Fintype Label] [Fintype Original]
    (embed : Label→Original) (d : Original→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d (embed l)).block)) :
    secondLiveRows (fun l=>(d l).block) := by
  refine ⟨⟨embed r.val.1,r.val.2⟩,?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩

theorem main_low_original_label_row_injective  {Label Original : Type*}
    [Fintype Label] [Fintype Original]
    (embed : Label→Original) (hinj : Function.Injective embed)
    (d : Original→SecondInputDatum α) :
    Function.Injective (mainLowOriginalLabelRow  embed d) := by
  intro r s h
  have hl : r.val.1=s.val.1 := hinj (congrArg (fun q=>q.val.1) h)
  rcases r with ⟨⟨l,χr,ψr,zr⟩,hr⟩
  rcases s with ⟨⟨k,χs,ψs,zs⟩,hs⟩
  dsimp only at hl
  subst k
  have hc : χr=χs := congrArg (fun q=>q.val.2.1) h
  have hp : ψr=ψs := congrArg (fun q=>q.val.2.2.1) h
  have hz : zr=zs := Subtype.ext (congrArg (fun q=>q.val.2.2.2.val) h)
  subst χs ψs zs
  rfl

@[simp] theorem main_low_original_label_row_cost  {Label Original : Type*}
    [Fintype Label] [Fintype Original]
    (embed : Label→Original) (d : Original→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d (embed l)).block))
    (second : Bool) (t : ℝ) (Ds : Finset (Ideal O)) :
    highNormalizedRowCost second d (mainLowOriginalLabelRow  embed d r) t Ds=
      highNormalizedRowCost second (fun l=>d (embed l)) r t Ds := rfl

/-- The complete low ordinary image embeds into the full original second
family before its coarse theorem, without a row or label fee. -/
theorem actual_main_low_physical_full_original_row_cost  {Label Original : Type*}
    [Fintype Label] [Fintype Original]
    (embed : Label→Original) (hinj : Function.Injective embed)
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Original→SecondInputDatum α)
    (χ₀ : Label→RayFourExpansion.RayCharacter) (Q : Label→Ideal O) (m : Label→O)
    (hrows : ∀l,(d (embed l)).rows=sourceRows
      (d (embed l)).C (d (embed l)).D (d (embed l)).inactive (d (embed l)).radius)
    (coefficient : Original→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l))
        (fun _=>True)→BufferIndex e) :
    mainLowPhysicalCompleteCost  N a ap second
      (fun l=>ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l))
      (fun l=>coefficient (embed l)) t u select=
      ∑r∈((mainLowPhysicalOrdinaryRows  second
        (fun l=>ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l)) select).image
          (ordinaryHighOriginalRow (fun l=>d (embed l)) χ₀ Q m hrows)).image
            (mainLowOriginalLabelRow  embed d),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_low_physical_original_row_cost  N a ap second
    (fun l=>d (embed l)) χ₀ Q m hrows (fun l=>coefficient (embed l)) t u select]
  rw [Finset.sum_image (fun r _ z _ heq=>
    main_low_original_label_row_injective  embed hinj d heq)]
  apply Finset.sum_congr rfl
  intro r _
  rfl

set_option linter.unusedVariables false in
set_option linter.defProp false in

end
end OAI.SevenEighths.AuxiliaryPhysical
