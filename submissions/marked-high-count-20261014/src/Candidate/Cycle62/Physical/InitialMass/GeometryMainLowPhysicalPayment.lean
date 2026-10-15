import Candidate.Cycle62.Physical.InitialMass.GeometryMainLowQuantitativePayment
import Candidate.Cycle62.Physical.InitialMass.GeometryMainLowNormalizedPayment
import Candidate.Cycle62.Physical.InitialMass.SecondLowSourceCaps
import Candidate.Cycle62.Physical.InitialMass.GeometryShiftedHeight
import Candidate.Cycle62.Physical.InitialMass.GeometryHighPayment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle62FinalNatural Cycle62Moment.LowBranch
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
open Cycle62Moment LocalMoment
open CenteredMomentSecondInputCapacitySource
open CenteredMomentChildRows CenteredMomentSecondCanonical CenteredMomentSecondEnergySplit
open Cycle62FinalLow
open Cycle62Moment.LowBranch Cycle62FinalNatural Cycle62FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle62FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

local notation "O" => HeckeFamily.O
local instance geometryMainLowPhysicalDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _


theorem mainLowPhysicalSupported (second : Bool) (d : SecondInputDatum α) :
    Supported (if second then d.D else d.C) := by
  cases second
  · exact d.hC
  · exact d.hD

/-- Extend the literal selector only to express an ordinary finite-set
filter. No unsupported row receives a buffered-bin certificate. -/
def mainLowPhysicalSourcePredicate (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (z : O) : Prop :=
  if hz : z∈rows then bufferValue e (select ⟨z,hz⟩)<21/25 else False

theorem main_low_physical_source_sum (second : Bool) (d : SecondInputDatum α)
    {e : ℝ} (select : mainLowSourceRows second d (fun _=>True)→BufferIndex e)
    (f : O→ℝ) :
    (∑z∈mainLowSourceRows second d
      (mainLowPhysicalSourcePredicate (mainLowSourceRows second d (fun _=>True)) select),f z)=
    ∑z : mainLowSourceRows second d (fun _=>True),
      if bufferValue e (select z)<21/25 then f z.val else 0 := by
  let rows:=mainLowSourceRows second d (fun _=>True)
  have heq : mainLowSourceRows second d (mainLowPhysicalSourcePredicate rows select)=
      rows.filter (mainLowPhysicalSourcePredicate rows select) := by
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
  change (∑z∈rows,if mainLowPhysicalSourcePredicate rows select z then f z else 0)=_
  rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro z _
  simp only [mainLowPhysicalSourcePredicate,dite_eq_left z.property]

/-- The complete fixed-ray physical low cost. The original block label
may already carry its full-nonzero filter; restriction never tests a new
ordinary-block norm. Both actual rays and signed source rows are retained. -/
def mainLowPhysicalCompleteCost {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) : ℝ :=
  ∑r∈secondLiveRows (fun l=>(d l).block),
    ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
      if mainLowPhysicalSourcePredicate (mainLowSourceRows second (d r.1) (fun _=>True))
          (select r.1 r.2.1 r.2.2.1) (mainLowSignedRow second r.2.2.2.val) then
        mainNormalizedPhysicalCost N a ap second d coefficient t u r D else 0

/-- Exact source-to-physical transport. The physical lower factor is
outside the complete source sum; no child volume or normalizer is lost. -/
theorem actual_main_low_complete_physical_reindex {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    mainLowPhysicalCompleteCost N a ap second d coefficient t u select=
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
            (mainLowPhysicalSupported second (d l))
            (d l).R (d l).seed D z‖^2) := by
  unfold mainLowPhysicalCompleteCost
  rw [actual_main_low_physical_cost_reindex N a ap second d coefficient t u
    (fun l χ ψ=>mainLowPhysicalSourcePredicate (mainLowSourceRows second (d l) (fun _=>True)) (select l χ ψ))]
  have hsources : ∀l χ ψ D,
      (∑z∈mainLowSourceRows second (d l)
        (mainLowPhysicalSourcePredicate (mainLowSourceRows second (d l) (fun _=>True))
          (select l χ ψ)),
        ‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
          (if second then (d l).D else (d l).C)
          (mainLowPhysicalSupported second (d l))
          (d l).R (d l).seed D z‖^2)=
      ∑z : mainLowSourceRows second (d l) (fun _=>True),
        if bufferValue e (select l χ ψ z)<21/25 then
          ‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
            ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
            (if second then (d l).D else (d l).C)
            (mainLowPhysicalSupported second (d l))
            (d l).R (d l).seed D z.val‖^2 else 0 := by
    intro l χ ψ D
    exact main_low_physical_source_sum second (d l) (select l χ ψ) _
  simp_rw [hsources]
  rw [←Finset.sum_comm]
  apply congrArg (fun x=>x) -- stage the second ray before the label sum
  calc
    _=∑χ : RayFourExpansion.RayCharacter,∑ψ : RayFourExpansion.RayCharacter,
        ∑l,∑D∈(d l).block.divisors.filter Squarefree,
          (coefficient l*((d l).K/lowerFactor N a ap)*normalizer (d l).C (d l).D (d l).inactive)*
          (∑z : mainLowSourceRows second (d l) (fun _=>True),
            if bufferValue e (select l χ ψ z)<21/25 then
              ‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
                ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
                (if second then (d l).D else (d l).C)
                (mainLowPhysicalSupported second (d l))
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
def mainLowFixedRayPhysicalCost {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (l : Label)→mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) : ℝ :=
  ∑l,∑D∈(d l).block.divisors.filter Squarefree,
    ∑z∈secondLiveColumnRows (d l).block,
      if mainLowPhysicalSourcePredicate (mainLowSourceRows second (d l) (fun _=>True))
          (select l) (mainLowSignedRow second z.val) then
        mainNormalizedPhysicalCost N a ap second d coefficient t u ⟨l,χ,ψ,z⟩ D else 0

theorem actual_main_low_fixed_ray_physical_reindex {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (l : Label)→mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    mainLowFixedRayPhysicalCost N a ap second d coefficient t u χ ψ select=
      (1/lowerFactor N a ap)*mainLowCompleteSelectedCost
        (fun l=>mainLowSourceRows second (d l) (fun _=>True)) select
        (fun l=>(d l).block.divisors.filter Squarefree)
        (fun l _=>coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive)
        (fun l D z=>‖normalizedColumn
          (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
            ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
          (if second then (d l).D else (d l).C)
          (mainLowPhysicalSupported second (d l))
          (d l).R (d l).seed D z‖^2) := by
  unfold mainLowFixedRayPhysicalCost mainLowCompleteSelectedCost
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  have hfactor : ∀z,
      (if mainLowPhysicalSourcePredicate (mainLowSourceRows second (d l) (fun _=>True))
          (select l) (mainLowSignedRow second z.val) then
        mainNormalizedPhysicalCost N a ap second d coefficient t u ⟨l,χ,ψ,z⟩ D else 0)=
      (coefficient l*((d l).K/lowerFactor N a ap)*normalizer (d l).C (d l).D (d l).inactive)*
      (if mainLowPhysicalSourcePredicate (mainLowSourceRows second (d l) (fun _=>True))
          (select l) (mainLowSignedRow second z.val) then
        ‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
          (if second then (d l).D else (d l).C)
          (mainLowPhysicalSupported second (d l))
          (d l).R (d l).seed D (mainLowSignedRow second z.val)‖^2 else 0) := by
    intro z
    cases second <;> simp only [mainNormalizedPhysicalCost,mainLowSignedRow,ite_true]
    all_goals split_ifs <;> simp only [mul_zero]
  simp_rw [hfactor]
  rw [←Finset.mul_sum,main_low_source_sum second (d l)
    (mainLowPhysicalSourcePredicate (mainLowSourceRows second (d l) (fun _=>True)) (select l))
    (fun z=>‖normalizedColumn (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
      ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
      (if second then (d l).D else (d l).C)
      (mainLowPhysicalSupported second (d l)) (d l).R (d l).seed D z‖^2),
    main_low_physical_source_sum]
  ring

/-- Fixed ray cardinalities are paid once after complete source columns.
The supplied source estimate is the quantitative receipt's literal last
inequality, not a norm estimate for an arithmetic label. -/
theorem main_low_physical_fixed_ray_sum_le {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e)
    (bound : ℝ) (hlower : 0<lowerFactor N a ap)
    (hsource : ∀χ ψ,mainLowCompleteSelectedCost
      (fun l=>mainLowSourceRows second (d l) (fun _=>True)) (fun l=>select l χ ψ)
      (fun l=>(d l).block.divisors.filter Squarefree)
      (fun l _=>coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive)
      (fun l D z=>‖normalizedColumn
        (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
        (if second then (d l).D else (d l).C)
        (mainLowPhysicalSupported second (d l))
        (d l).R (d l).seed D z‖^2)≤bound) :
    mainLowPhysicalCompleteCost N a ap second d coefficient t u select≤
      (1/lowerFactor N a ap)*(Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*bound := by
  rw [actual_main_low_complete_physical_reindex]
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun χ _=>
    Finset.sum_le_sum (s:=Finset.univ) (fun ψ _=>hsource χ ψ))
  have h' := mul_le_mul_of_nonneg_left h (by positivity : 0≤1/lowerFactor N a ap)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_two,mul_assoc] using h'

private theorem fixed_ray_source_transport {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (l : Label)→mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e)
    (c : Label→Ideal O→ℝ) (value : Label→Ideal O→O→ℝ) (bound : ℝ)
    (hlower : 0<lowerFactor N a ap)
    (hc : ∀l D,coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive=c l D)
    (hv : ∀l D z,‖normalizedColumn
      (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
        ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
      (if second then (d l).D else (d l).C)
      (mainLowPhysicalSupported second (d l))
      (d l).R (d l).seed D z‖^2=value l D z)
    (hb : mainLowCompleteSelectedCost (fun l=>mainLowSourceRows second (d l) (fun _=>True))
      select (fun l=>(d l).block.divisors.filter Squarefree) c value≤bound) :
    mainLowFixedRayPhysicalCost N a ap second d coefficient t u χ ψ select≤
      (1/lowerFactor N a ap)*bound := by
  rw [actual_main_low_fixed_ray_physical_reindex]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤1/lowerFactor N a ap)
  have heq : mainLowCompleteSelectedCost (fun l=>mainLowSourceRows second (d l) (fun _=>True))
      select (fun l=>(d l).block.divisors.filter Squarefree)
      (fun l _=>coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive)
      (fun l D z=>‖normalizedColumn
        (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
        (if second then (d l).D else (d l).C)
        (mainLowPhysicalSupported second (d l))
        (d l).R (d l).seed D z‖^2)=
      mainLowCompleteSelectedCost (fun l=>mainLowSourceRows second (d l) (fun _=>True))
        select (fun l=>(d l).block.divisors.filter Squarefree) c value := by
    have hceq : (fun l (_ : Ideal O)=>coefficient l*(d l).K*
        normalizer (d l).C (d l).D (d l).inactive)=c := by
      funext l D
      exact hc l D
    have hveq : (fun l D z=>‖normalizedColumn
        (withHeight (d l).input (if second then (d l).τ ψ⁻¹ else (d l).τ χ)
          ((d l).input.t+2*Real.pi*(u-(if second then -t else t))))
        (if second then (d l).D else (d l).C)
        (mainLowPhysicalSupported second (d l))
        (d l).R (d l).seed D z‖^2)=value := by
      funext l D z
      exact hv l D z
    rw [hceq,hveq]
  exact heq ▸ hb

attribute [local irreducible] mainLowFixedRayPhysicalCost mainLowCompleteSelectedCost
  selectedFirstProjectors

/-- A complete original-nonzero second family may be stored separately
under each chosen first column. This exact sigma identity preserves that
subtype, its common allocation and its literal signed frequency set. -/
theorem main_low_fixed_ray_sigma {Label : Type*} [Fintype Label]
    (Block : Label→Type*) [∀l,Fintype (Block l)]
    (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : ((l : Label)×Block l)→SecondInputDatum α)
    (coefficient : ((l : Label)×Block l)→ℝ) (t u : ℝ)
    (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (r : (l : Label)×Block l)→mainLowSourceRows second (d r) (fun _=>True)→BufferIndex e) :
    mainLowFixedRayPhysicalCost N a ap second d coefficient t u χ ψ select=
      ∑l,mainLowFixedRayPhysicalCost N a ap second
        (fun r : Block l=>d ⟨l,r⟩) (fun r=>coefficient ⟨l,r⟩) t u χ ψ
        (fun r=>select ⟨l,r⟩) := by
  unfold mainLowFixedRayPhysicalCost
  exact Fintype.sum_sigma _

set_option maxHeartbeats 320000 in
/-- The first projector union is taken on the selected original columns
before the complete second family, fixed rays or buffered bins are split.
No block or arithmetic-label cardinality appears. -/
theorem main_low_physical_first_shell_reindex {ι Label : Type*} [Fintype Label]
    {src : ι→FirstBlockSource}
    (column : Label→FirstColumnIndex src)
    (hs : ∀l,Squarefree (column l).2.1.val)
    (Block : Label→Type*) [∀l,Fintype (Block l)]
    (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : ((l : Label)×Block l)→SecondInputDatum α)
    (coefficient : ((l : Label)×Block l)→ℝ) (t u : ℝ)
    (χ ψ : RayFourExpansion.RayCharacter) {e : ℝ}
    (select : (r : (l : Label)×Block l)→mainLowSourceRows second (d r) (fun _=>True)→BufferIndex e) :
    mainLowFixedRayPhysicalCost N a ap second d coefficient t u χ ψ select=
      ∑n∈CenteredMomentWholeDivisorShell.selectedShells (selectedFirstProjectors column),
        mainLowFixedRayPhysicalCost N a ap second
          (fun r : (l : SelectedFirstShell column n)×Block l.val=>d ⟨r.1.val,r.2⟩)
          (fun r=>coefficient ⟨r.1.val,r.2⟩) t u χ ψ
          (fun r=>select ⟨r.1.val,r.2⟩) := by
  rw [main_low_fixed_ray_sigma,selected_first_shell_sum column hs]
  apply Finset.sum_congr rfl
  intro n _
  exact (main_low_fixed_ray_sigma (fun l : SelectedFirstShell column n=>Block l.val)
    N a ap second (fun r=>d ⟨r.1.val,r.2⟩) (fun r=>coefficient ⟨r.1.val,r.2⟩)
    t u χ ψ (fun r=>select ⟨r.1.val,r.2⟩)).symm

/-- All fixed rays share the same first projector union. A shell payment
therefore incurs its norm-dyad count once, after both ray sums. -/
theorem main_low_physical_complete_ray_sum {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    mainLowPhysicalCompleteCost N a ap second d coefficient t u select=
      ∑χ : RayFourExpansion.RayCharacter,∑ψ : RayFourExpansion.RayCharacter,
        mainLowFixedRayPhysicalCost N a ap second d coefficient t u χ ψ
          (fun l=>select l χ ψ) := by
  rw [actual_main_low_complete_physical_reindex,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ψ _
  exact (actual_main_low_fixed_ray_physical_reindex N a ap second d coefficient t u χ ψ _).symm

/-- Pure payment contraction on the actual nested physical family. The
per-shell source estimate is supplied by `actual_main_low_physical_bins`;
this step charges only the common first-projector shells and fixed rays. -/
theorem main_low_physical_first_shell_payment {ι Label : Type*} [Fintype Label]
    {src : ι→FirstBlockSource}
    (column : Label→FirstColumnIndex src)
    (hs : ∀l,Squarefree (column l).2.1.val)
    (Block : Label→Type*) [∀l,Fintype (Block l)]
    (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : ((l : Label)×Block l)→SecondInputDatum α)
    (coefficient : ((l : Label)×Block l)→ℝ) (t u : ℝ) {e : ℝ}
    (select : (r : (l : Label)×Block l)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d r) (fun _=>True)→BufferIndex e)
    (bound C Z ε : ℝ) (hbound : 0≤bound)
    (hcard : ((CenteredMomentWholeDivisorShell.selectedShells
      (selectedFirstProjectors column)).card:ℝ)≤C*Z^ε)
    (hpay : ∀n∈CenteredMomentWholeDivisorShell.selectedShells (selectedFirstProjectors column),
      ∀χ ψ,mainLowFixedRayPhysicalCost N a ap second
        (fun r : (l : SelectedFirstShell column n)×Block l.val=>d ⟨r.1.val,r.2⟩)
        (fun r=>coefficient ⟨r.1.val,r.2⟩) t u χ ψ
        (fun r=>select ⟨r.1.val,r.2⟩ χ ψ)≤bound) :
    mainLowPhysicalCompleteCost N a ap second d coefficient t u select≤
      (Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(C*Z^ε*bound) := by
  rw [main_low_physical_complete_ray_sum]
  have hray (χ ψ : RayFourExpansion.RayCharacter) :
      mainLowFixedRayPhysicalCost N a ap second d coefficient t u χ ψ
        (fun l=>select l χ ψ)≤C*Z^ε*bound := by
    rw [main_low_physical_first_shell_reindex column hs Block]
    calc
      _≤∑_n∈CenteredMomentWholeDivisorShell.selectedShells (selectedFirstProjectors column),bound :=
        Finset.sum_le_sum (fun n hn=>hpay n hn χ ψ)
      _≤C*Z^ε*bound := by
        simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
          mul_le_mul_of_nonneg_right hcard hbound
  calc
    _≤∑_χ : RayFourExpansion.RayCharacter,∑_ψ : RayFourExpansion.RayCharacter,C*Z^ε*bound :=
      Finset.sum_le_sum (fun χ _=>Finset.sum_le_sum (fun ψ _=>hray χ ψ))
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_two,mul_assoc]

/-- Original stored-pool caps pay the common FIRST projector shells
uniformly before all selected labels, original-nonzero second blocks and
Mellin shifts. The supplied shell receipt is the literal physical-bin
continuation, not a cardinality bound on arithmetic labels. -/
theorem eventual_actual_main_low_physical_first_shell_contraction
    (N : ℕ) (U εshell : ℝ) (hU : 0≤U) (hεshell : 0<εshell) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{ι Label : Type*}[Fintype ι][DecidableEq ι][Fintype Label]
        (s : Input ι),Fintype.card ι≤N →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
      ∀(R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
        (column : Label→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (_hs : ∀l,Squarefree (column l).2.1.val)
        (Block : Label→Type*)[∀l,Fintype (Block l)]
        (a ap : ℝ)(second : Bool)
        (d : ((l : Label)×Block l)→SecondInputDatum ι)
        (coefficient : ((l : Label)×Block l)→ℝ)(t u e bound : ℝ)
        (select : (r : (l : Label)×Block l)→(χ ψ : RayFourExpansion.RayCharacter)→
          mainLowSourceRows second (d r) (fun _=>True)→BufferIndex e),
      0≤bound →
      (∀n∈selectedShells (selectedFirstProjectors column),∀χ ψ,
        mainLowFixedRayPhysicalCost N a ap second
          (fun r : (l : SelectedFirstShell column n)×Block l.val=>d ⟨r.1.val,r.2⟩)
          (fun r=>coefficient ⟨r.1.val,r.2⟩) t u χ ψ
          (fun r=>select ⟨r.1.val,r.2⟩ χ ψ)≤bound) →
      mainLowPhysicalCompleteCost N a ap second d coefficient t u select≤
        (Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(C*Z^εshell*bound) := by
  obtain ⟨C,hC,hcount⟩:=eventual_actual_geometry_selected_first_shell_subpower N U εshell hU hεshell
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι Label _ _ _ s hN hpool R seed K ξ hK bin column hs Block _ a ap second
    d coefficient t u e bound select hbound hpay
  exact main_low_physical_first_shell_payment column hs Block N a ap second d coefficient t u
    select bound C Z εshell hbound (hz.2 s hN hpool R seed K ξ hK bin column) hpay

/-- The complete ordinary low subset, before any projector grouping.
The row's block label is unchanged, including its original-nonzero subtype. -/
def mainLowPhysicalOrdinaryRows {Label : Type*} [Fintype Label]
    (second : Bool) (d : Label→SecondInputDatum α) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    Finset (secondLiveRows (fun l=>(d l).block)) :=
  Finset.univ.filter (fun r=>mainLowPhysicalSourcePredicate
    (mainLowSourceRows second (d r.val.1) (fun _=>True))
    (select r.val.1 r.val.2.1 r.val.2.2.1) (mainLowSignedRow second r.val.2.2.2.val))

/-- The exact physical cost is the normalized row family consumed by the
all-height splice. The height retains both signed Mellin shifts. -/
theorem actual_main_low_physical_ordinary_row_cost {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    mainLowPhysicalCompleteCost N a ap second d coefficient t u select=
      ∑r∈mainLowPhysicalOrdinaryRows second d select,
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

private theorem ordinary_physical_divisors (d : SecondInputDatum α)
    (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (m : O) :
    (ordinarySecondDatum d χ Q m).block.divisors=d.block.divisors := rfl

set_option maxHeartbeats 320000 in
/-- Ordinary low rows are transported to the original source family
before the genuine coarse theorem. The original label/ray/frequency image
is injective; an ordinary block need not be nonzero. -/
theorem actual_main_low_physical_original_row_cost {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (χ₀ : Label→RayFourExpansion.RayCharacter) (Q : Label→Ideal O) (m : Label→O)
    (hrows : ∀l,(d l).rows=sourceRows
      (d l).C (d l).D (d l).inactive (d l).radius)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (ordinarySecondDatum (d l) (χ₀ l) (Q l) (m l))
        (fun _=>True)→BufferIndex e) :
    mainLowPhysicalCompleteCost N a ap second
      (fun l=>ordinarySecondDatum (d l) (χ₀ l) (Q l) (m l)) coefficient t u select=
      ∑r∈(mainLowPhysicalOrdinaryRows second
        (fun l=>ordinarySecondDatum (d l) (χ₀ l) (Q l) (m l)) select).image
          (ordinaryHighOriginalRow d χ₀ Q m hrows),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_low_physical_ordinary_row_cost]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro r _
    rw [ordinary_high_original_row_cost]
    have hlabel : (ordinaryHighOriginalRow d χ₀ Q m hrows r).val.1=r.val.1 := rfl
    rw [hlabel]
    have hdiv:=ordinary_physical_divisors (d r.val.1) (χ₀ r.val.1) (Q r.val.1) (m r.val.1)
    rw [hdiv]
    congr 1
  · intro r _ z _ heq
    exact ordinary_high_original_row_injective d χ₀ Q m hrows heq

/-- Inclusion of a selected original block-label family into the full
second family. Both rays and the literal frequency are unchanged. -/
def mainLowOriginalLabelRow {Label Original : Type*} [Fintype Label] [Fintype Original]
    (embed : Label→Original) (d : Original→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d (embed l)).block)) :
    secondLiveRows (fun l=>(d l).block) := by
  refine ⟨⟨embed r.val.1,r.val.2⟩,?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩

theorem main_low_original_label_row_injective {Label Original : Type*}
    [Fintype Label] [Fintype Original]
    (embed : Label→Original) (hinj : Function.Injective embed)
    (d : Original→SecondInputDatum α) :
    Function.Injective (mainLowOriginalLabelRow embed d) := by
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

@[simp] theorem main_low_original_label_row_cost {Label Original : Type*}
    [Fintype Label] [Fintype Original]
    (embed : Label→Original) (d : Original→SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d (embed l)).block))
    (second : Bool) (t : ℝ) (Ds : Finset (Ideal O)) :
    highNormalizedRowCost second d (mainLowOriginalLabelRow embed d r) t Ds=
      highNormalizedRowCost second (fun l=>d (embed l)) r t Ds := rfl

/-- The complete low ordinary image embeds into the full original second
family before its coarse theorem, without a row or label fee. -/
theorem actual_main_low_physical_full_original_row_cost {Label Original : Type*}
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
    mainLowPhysicalCompleteCost N a ap second
      (fun l=>ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l))
      (fun l=>coefficient (embed l)) t u select=
      ∑r∈((mainLowPhysicalOrdinaryRows second
        (fun l=>ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l)) select).image
          (ordinaryHighOriginalRow (fun l=>d (embed l)) χ₀ Q m hrows)).image
            (mainLowOriginalLabelRow embed d),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_low_physical_original_row_cost N a ap second
    (fun l=>d (embed l)) χ₀ Q m hrows (fun l=>coefficient (embed l)) t u select]
  rw [Finset.sum_image (fun r _ z _ heq=>
    main_low_original_label_row_injective embed hinj d heq)]
  apply Finset.sum_congr rfl
  intro r _
  rfl

set_option linter.unusedVariables false in
set_option linter.defProp false in
def MainLowPhysicalBinSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0<margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0<supply)(hev : 0<εv)
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0<ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L)
    (degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ ℝ)
        (heightV height mesh : ℝ)
        (hcard : Fintype.card α≤N)(hmass : ∀j,s.M j≤Cs)(hsupply' : supply≤s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)(hsη : s.η=ηseed)
        (hsupper : s.upper≤bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0≤w j)(hwL : ∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold)
        (hwr : ∀j,w j/d≤Rwidth)(hmesh : 0≤mesh)(hwm : ∀j,w j≤mesh)
        (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤hi)(hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)
        (hT : 2<Z^τ)
        (hfreqbin : |heightV|+height+Z^τ/2≤5*Z^τ)
        (hβhi : HeckeZeroSupremum.beta≤7/8)
        (Mrow reserve ξ : ℝ)(hMmin : Mmin≤Mrow)
        (hω : 0≤frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
        (hMcap' : Mrow+εwidth*Mrow+ξ/2≤Mcap)
        (hzslot : (17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow)
        (haff : length Z s.X₁+length Z s.X₂+Cycle62.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
          Cycle62.Arithmetic.B*Mrow)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Cycle62.Arithmetic.cellUpper
          (Cycle62.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp:=Mrow*Cycle62.Arithmetic.amp cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        let p:=((bin.2 2:ℝ)+1)*Real.logb Z 2
        let c : Fin 5:=if reflected then 1 else 0
        let exponent:=Real.logb Z (volume s)-(bin.2 c:ℝ)*Real.logb Z 2+
          ((bin.2 3:ℝ)+1)*Real.logb Z 2+((bin.2 4:ℝ)+1)*Real.logb Z 2
        let sideLower:=(bin.2 2:ℝ)*Real.logb Z 2+Real.logb Z (volume s)-
          ((bin.2 c:ℝ)+1)*Real.logb Z 2+(bin.2 3:ℝ)*Real.logb Z 2+(bin.2 4:ℝ)*Real.logb Z 2
        ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤Z^Bnorm)
          (Tfirst : ℝ)(hTfirst : 1≤Tfirst)(hp : p≤Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (hfirstshell : ∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst)
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hOriginal : ∀r∈rows,
            (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin)∈geometryMainNonzeroBlocks reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin hw₁ hw₂)
          (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
          (box : Finset (Fin 4→ ℤ))
          (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
            (K r.1) (Tsec r.1) Z ξ r.2∈box),
        let datum : rows→ SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        ∀(B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0),
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        ∀(χ₀ : rows→ RayFourExpansion.RayCharacter)(χ ψ : RayFourExpansion.RayCharacter)
          (m : O)(hm₀ : m≠0)(hml : goodLambda∣m)(hm₂ : (2:O)∣m)
          (hP : ∀r,(q r).R₂*(q r).E₂≠0)
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤Z^Bmask)
          (divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ ℂ))
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ ap≤x)(hplain₂ : ∀x,s.W₂ x≠0→ ap≤x)
          (hpool : ∀j I,I∈s.pools j→ (I.absNorm:ℝ)≤Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤window)
          (hplainScale : ∀side j,Cycle62.Physical.sourcePlainScales s.toData.toSource side j≤Z^L),
        let ray:=if second then ψ⁻¹ else χ
        let ordinaryRows:=fun r : rows=>mainLowSourceRows second
          (ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m) (fun _=>True)
        let canonical:=fun r : rows=>mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ
          (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
          (by exact hP r) (by exact hPN r) η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
        ∃select : (r : rows)→ ordinaryRows r→ BufferIndex e,
          (∀r,select r=canonical r) ∧
          (∀r pbin z,z∈mainLowPaymentRows (ordinaryRows r) (select r) pbin→ 1≤pbin.1.val) ∧
        let src:=fun r=>withHeight (q r).first ((g r).datum.τ ray) heightV
        let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
        let unionDs:=sharedProjectors Ds
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*Mrow+ξ/2-Mrow*(7/30000000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle62.Arithmetic.q0/9)*(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)+Cycle62.Arithmetic.q0*mesh+pad
        let exponentFull:=Bmass*εmass+amp+error+εv+Bnorm*εshell+εlabels
        let factor : ℝ:=mainLowQuantitativeFactor Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card
        let coefficient:=fun (r : rows)(_D : Ideal O)=>
          firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
            normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
        let value:=fun (r : rows)(D : Ideal O)(z : O)=>
          ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2
        ∀(t₀ u : ℝ),heightV=t+2*Real.pi*(u-(if second then -t₀ else t₀)) →
        (∀r,divisorSeed r=(datum r).seed) →
        mainLowFixedRayPhysicalCost N supply ap second
          (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
          (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u χ ψ select≤
          (1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*
            ((16*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)))

attribute [local irreducible] MainLowPhysicalBinSpec actual_main_low_quantitative_bins
  MainLowQuantitativeBinSpec geometryMainNonzeroBlocks
set_option maxHeartbeats 320000 in
def actual_main_low_physical_bins {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0<margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0<supply)(hev : 0<εv)
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels)
    (ap εmass Bmass : ℝ)(hap : 0<ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L) (hτgap : 2*τ<d*η) (hBmassNorm : Bmass≤Bnorm) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,
      PLift (0<Cu) ×
      (∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤M),
        internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},     
        ΣCg : ℝ,PLift (0<Cg ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
          MainLowPhysicalBinSpec (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      degree Sp Cg Cu η₀ Q hQM hQ72 Z)) := by
  let k:=actual_main_low_quantitative_bins (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0 hτgap hBmassNorm
  refine ⟨k.1,k.2.1,k.2.2.1,k.2.2.2.1,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  let hc:=k.2.2.2.2 η₀ Q hQM hQ0 hQt hQ72
  refine ⟨hc.1,PLift.up ⟨hc.2.down.1,?_⟩⟩
  filter_upwards [hc.2.down.2] with Z hz
  refine ⟨hz.1,?_⟩
  unfold MainLowPhysicalBinSpec
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p c exponent sideLower hf₁ hw₁ hw₂ hsource
    Tfirst hTfirst hp hs₀ hs₀0 hinj hfirstshell
    rows hOriginal hU box hbox datum B₂ rwitness hf₂ q g χ₀ χ ψ m hm₀ hml hm₂ hP hPN
    divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale ray ordinaryRows canonical
  have hzq:=hz.2
  unfold MainLowQuantitativeBinSpec at hzq
  obtain ⟨select,heq,hpos,hbins,hfull⟩:=hzq hZ s θ w σ freq heightV height mesh hcard hmass
    hsupply' hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff reflected second R seed₀ bin t firstIndex
    hf₁ hw₁ hw₂ hsource Tfirst hTfirst hp hs₀ hs₀0 hinj hfirstshell
    rows hOriginal hU box hbox B₂ rwitness hf₂ χ₀ χ ψ m hm₀ hml hm₂ hP hPN
    divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale
  refine ⟨select,heq,hpos,?_⟩
  intro src Ds unionDs firstMass physical error exponentFull factor coefficient value t₀ u hshift hseed
  have hb:=fixed_ray_source_transport (Label:=rows) N supply ap second
    (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
    (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u χ ψ select coefficient value _
    (lowerFactor_pos N supply ap hsupply hap)
    (fun _ _=>rfl)
    (fun r D z=>by
      change ‖normalizedColumn
        (withHeight (datum r).input (if second then (datum r).τ ψ⁻¹ else (datum r).τ χ)
          (t+2*Real.pi*(u-(if second then -t₀ else t₀))))
        (if second then (datum r).D else (datum r).C) _ (datum r).R (datum r).seed D z‖^2=_
      rw [←hshift,←hseed r]
      cases second <;> rfl)
    hfull
  convert hb using 1
  ring

/-- The kernel's actual signed height is paid by the same envelope used
by the all-height splice; neither Mellin variable is dropped. -/
theorem main_low_physical_signed_height (second : Bool) (v height t u : ℝ)
    (hh : 0≤height) :
    1+|v+2*Real.pi*(u-(if second then -t else t))|+height≤
      2*(1+|v|+height+2*Real.pi*(|t|+|u|)) := by
  have hs : |(if second then -t else t)|=|t| := by cases second <;> simp
  have hsub : |u-(if second then -t else t)|≤|u|+|t| := by
    simpa only [sub_zero,zero_sub,abs_neg,hs] using
      abs_sub_le u 0 (if second then -t else t)
  have hshift : |v+2*Real.pi*(u-(if second then -t else t))|≤
      |v|+2*Real.pi*(|u|+|t|) := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi)]
    simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hsub
      (show 0≤2*Real.pi by positivity)) |v|
  have hp : 0≤2*Real.pi*(|t|+|u|) := by positivity
  linarith [abs_nonneg v]

/-- Collapse the genuine kernel's exact sixteen, finite buffered-bin fee,
fixed rays and BOTH common-projector/absolute-box fees into the small-height
form. The original reciprocal seed and physical outer factor are retained. -/
theorem main_low_physical_small_fee_bound
    (N degree : ℕ) (e : ℝ) (second : Bool)
    (a ap Cg Cu Cfirst Cbox b Cs control v height t u physical Z exponent seedNorm
      εfirst εsecond εbox : ℝ) (boxCard : ℕ)
    (hlower : 0<lowerFactor N a ap)
    (hCg : 0≤Cg)(hCu : 0≤Cu)(hfirst : 0≤Cfirst)
    (hCs : 0≤Cs)(hh : 0≤height)(hphysical : 0≤physical)(hZ : 0<Z)(hseed : 0<seedNorm)
    (hbox : (boxCard:ℝ)≤Cbox*Z^εbox) :
    (Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(Cfirst*Z^εfirst*
      ((1/lowerFactor N a ap)*(Fintype.card (BufferIndex e):ℝ)*
        ((16*mainLowQuantitativeFactor Cg b Cs control
          (v+2*Real.pi*(u-(if second then -t else t))) height physical Z exponent seedNorm
          N degree boxCard)*(Cu*Z^εsecond))))≤
      ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*Cfirst*
        (1/lowerFactor N a ap)*(Fintype.card (BufferIndex e):ℝ)*16*Cg*
        (2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*Cu*Cbox)*
        control^2*physical*Z^(exponent+εfirst+εsecond+εbox)/seedNorm*
        (2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^degree := by
  have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
  have hheight:=pow_le_pow_left₀ (by positivity :
      0≤1+|v+2*Real.pi*(u-(if second then -t else t))|+height)
    (main_low_physical_signed_height second v height t u hh) degree
  unfold mainLowQuantitativeFactor
  calc
    _≤(Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(Cfirst*Z^εfirst*
      ((1/lowerFactor N a ap)*(Fintype.card (BufferIndex e):ℝ)*
        ((16*(Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*control^2*
          (2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^degree*(Cbox*Z^εbox)*physical*
          Z^exponent/seedNorm))*(Cu*Z^εsecond)))) := by
      gcongr
    _=_ := by rw [Real.rpow_add hZ,Real.rpow_add hZ,Real.rpow_add hZ]; ring

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_physical_source_sum
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_main_low_complete_physical_reindex

#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_main_low_fixed_ray_physical_reindex
#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_physical_fixed_ray_sum_le

#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_main_low_physical_bins

#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_fixed_ray_sigma
#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_physical_first_shell_reindex
#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_physical_complete_ray_sum
#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_physical_first_shell_payment

#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_main_low_physical_ordinary_row_cost
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_main_low_physical_original_row_cost

#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_original_label_row_injective
#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_original_label_row_cost
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_main_low_physical_full_original_row_cost

#print axioms OAI.SevenEighths.Cycle62InitialMass.eventual_actual_main_low_physical_first_shell_contraction

#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_physical_signed_height
#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_physical_small_fee_bound
