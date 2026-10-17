/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighRows
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion LocalMoment
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open Cycle63FinalNatural CenteredMomentEnergyState Cycle63Moment.LowBranch
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- One buffered bin contains each original row exactly when its single
selector chooses that bin. Projector costs remain inside the row cost. -/
def mainBufferedCostBin {ι : Type*} (rows : Finset ι) (e : ℝ)
    (select : rows→BufferIndex e) (cost : rows→ℝ) (p : BufferIndex e) : ℝ :=
  ∑r : rows,if select r=p then cost r else 0

/-- Exact finite disintegration, followed by the strict-low/inclusive-high
cut. This does not charge the number of source labels or rows. -/
theorem main_buffered_cost_partition {ι : Type*} (rows : Finset ι) (e : ℝ)
    (select : rows→BufferIndex e) (cost : rows→ℝ) :
    (∑r : rows,cost r)=
      (∑p∈Finset.univ.filter (fun p=>bufferValue e p<((1+Cycle63.Arithmetic.q0)/2)),
        mainBufferedCostBin rows e select cost p)+
      (∑p∈Finset.univ.filter (fun p=>((1+Cycle63.Arithmetic.q0)/2)≤bufferValue e p),
        mainBufferedCostBin rows e select cost p) := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have hf := geometry_zero_fiber_reassembly rows e select cost
  simp only [Finset.sum_filter,Finset.attach_eq_univ] at hf
  exact hf.trans (geometry_zero_low_high_reassembly e _)

/-- The projector union and its shells are formed from the whole original
row family, before either zero-bin grouping or low/high filtering. -/
def mainBufferedShellBin {ι : Type*} (rows : Finset ι) (e : ℝ)
    (select : rows→BufferIndex e) (Ds : rows→Finset (Ideal O))
    (cost : rows→Ideal O→ℝ) (n : ℤ) (p : BufferIndex e) : ℝ :=
  ∑r : rows,if select r=p then
    ∑D∈shell (sharedProjectors Ds) n,if D∈Ds r then cost r D else 0
  else 0

/-- Exact common-shell disintegration retains the original per-row ideal
membership filter. Both branches use the same global projector union. -/
theorem main_buffered_projector_partition {ι : Type*} (rows : Finset ι) (e : ℝ)
    (select : rows→BufferIndex e) (Ds : rows→Finset (Ideal O))
    (hs : ∀r D,D∈Ds r→Squarefree D) (cost : rows→Ideal O→ℝ) :
    (∑r : rows,∑D∈Ds r,cost r D)=
      (∑n∈selectedShells (sharedProjectors Ds),
        ∑p∈Finset.univ.filter (fun p=>bufferValue e p<((1+Cycle63.Arithmetic.q0)/2)),
          mainBufferedShellBin rows e select Ds cost n p)+
      (∑n∈selectedShells (sharedProjectors Ds),
        ∑p∈Finset.univ.filter (fun p=>((1+Cycle63.Arithmetic.q0)/2)≤bufferValue e p),
          mainBufferedShellBin rows e select Ds cost n p) := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  rw [shared_projector_shell_sum Ds hs cost,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  exact main_buffered_cost_partition rows e select
    (fun r=>∑D∈shell (sharedProjectors Ds) n,if D∈Ds r then cost r D else 0)

section Physical
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance mainBufferedSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- One actual selector for the complete ordinary physical row family,
before any residual projector or low/high cost is considered. `Label` keeps
the original nonzero-block restriction and its previously selected allocations. -/
theorem actual_main_buffered_row_selector
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (d : Label→SecondInputDatum α) (χ₀ : Label→RayCharacter) (Q : Ideal O)
    (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1<Z) (second : Bool)
    (hP : ∀l,(d l).R*(if second then (d l).D else (d l).C)≠0)
    (hPN : ∀l,(((d l).R*(if second then (d l).D else (d l).C)).absNorm:ℝ)≤Z^Bmask)
    (η₀ : Character) (hQM : Q≤M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let ordinary:=fun l=>ordinarySecondDatum (d l) (χ₀ l) Q m
    let rows:=secondLiveRows (fun l=>(ordinary l).block)
    let signed:=fun r : rows=>mainLowSignedRow second r.val.2.2.2.val
    let st:=fun r : rows=>retainedState Z Bmask hZ
      (if second then (d r.val.1).τ r.val.2.2.1⁻¹ else (d r.val.1).τ r.val.2.1) Q
      ((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C))
      (hP r.val.1) (hPN r.val.1)
      (d r.val.1).radius (d r.val.1).C (d r.val.1).D (d r.val.1).inactive
    ∃keep : ∀r : rows,(st r).radial.keep (signed r),
    ∃select : rows→BufferIndex e,∀r : rows,
      1≤((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re ∧
      GeometryZeroBin M H hH (st r) η₀ hQM hQη (signed r) (keep r) e T (select r) ∧
      (bufferValue e (select r)<((1+Cycle63.Arithmetic.q0)/2) →
        ActualLow M H hH (st r) η₀ hQM hQη (((1+Cycle63.Arithmetic.q0)/2)) e
          (3*((select r).1.val+1:ℕ)*T) (signed r)) := by
  intro ordinary rows signed st
  have ha (r : rows) := actual_main_ordinary_row_admission (d r.val.1)
    (χ₀ r.val.1) r.val.2.1 r.val.2.2.1 Q hQ m hm hml hm2
    Z Bmask hZ second (hP r.val.1) (hPN r.val.1)
    r.val.2.2.2.val r.val.2.2.2.property
  let keep : ∀r : rows,(st r).radial.keep (signed r) := fun r=>(ha r).1
  have hp (r : rows) := actual_geometry_zero_partition M H hH (st r) η₀ hQM hQη
    (signed r) (keep r) e T he hT hβlo hβhi
  let select : rows→BufferIndex e := fun r=>Classical.choose (hp r)
  refine ⟨keep,select,?_⟩
  intro r
  have hbin := Classical.choose_spec (hp r)
  refine ⟨(ha r).2,hbin,?_⟩
  intro hl
  apply actual_main_low_bin_admission M H hH (st r) η₀ hQM hQη (signed r)
    (keep r) e T (select r) hbin hl
  have hweight : 1≤((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re := (ha r).2
  simpa only [normValue_eq_embedding] using hweight

/-- Literal full main physical cost is exactly low plus high buffered costs.
`Label` can be the original-nonzero block subtype: it is never enlarged or
replaced, and its original first coefficient remains inside every term. -/
theorem actual_main_buffered_physical_partition
    (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : Label→SecondInputDatum α) (coefficient : Label→ℝ) (t u e : ℝ)
    (select : (secondLiveRows (fun l=>(d l).block))→BufferIndex e) :
    let rows:=secondLiveRows (fun l=>(d l).block)
    let cost:=fun r : rows=>∑D∈secondResidualIdeals (fun l=>(d l).block) r.val,
      mainNormalizedPhysicalCost N a ap second d coefficient t u r.val D
    (∑l,coefficient l*mainNormalizedBlockCost N a ap second (d l) t u)=
      (∑p∈Finset.univ.filter (fun p=>bufferValue e p<((1+Cycle63.Arithmetic.q0)/2)),
        mainBufferedCostBin rows e select cost p)+
      (∑p∈Finset.univ.filter (fun p=>((1+Cycle63.Arithmetic.q0)/2)≤bufferValue e p),
        mainBufferedCostBin rows e select cost p) := by
  intro rows cost
  rw [actual_main_block_cost_rows]
  rw [←Finset.sum_coe_sort rows]
  exact main_buffered_cost_partition rows e select cost

/-- The same literal identity with globally unioned residual-projector
shells. A selector never depends on the residual ideal being paid. -/
theorem actual_main_buffered_physical_shell_partition
    (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : Label→SecondInputDatum α) (coefficient : Label→ℝ) (t u e : ℝ)
    (select : (secondLiveRows (fun l=>(d l).block))→BufferIndex e) :
    let rows:=secondLiveRows (fun l=>(d l).block)
    let Ds:=fun r : rows=>secondResidualIdeals (fun l=>(d l).block) r.val
    let cost:=fun (r : rows) D=>mainNormalizedPhysicalCost N a ap second d coefficient t u r.val D
    (∑l,coefficient l*mainNormalizedBlockCost N a ap second (d l) t u)=
      (∑n∈selectedShells (sharedProjectors Ds),
        ∑p∈Finset.univ.filter (fun p=>bufferValue e p<((1+Cycle63.Arithmetic.q0)/2)),
          mainBufferedShellBin rows e select Ds cost n p)+
      (∑n∈selectedShells (sharedProjectors Ds),
        ∑p∈Finset.univ.filter (fun p=>((1+Cycle63.Arithmetic.q0)/2)≤bufferValue e p),
          mainBufferedShellBin rows e select Ds cost n p) := by
  intro rows Ds cost
  rw [actual_main_block_cost_rows]
  rw [←Finset.sum_coe_sort rows]
  apply main_buffered_projector_partition rows e select Ds _ cost
  intro r D hD
  change D∈secondResidualIdeals (fun l=>(d l).block) r.val at hD
  rw [actual_second_residual_ideals_label] at hD
  exact (Finset.mem_filter.mp hD).2
end Physical
end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.main_buffered_cost_partition
#print axioms OAI.SevenEighths.Cycle63InitialMass.main_buffered_projector_partition
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_buffered_physical_partition
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_buffered_physical_shell_partition
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_main_buffered_row_selector
