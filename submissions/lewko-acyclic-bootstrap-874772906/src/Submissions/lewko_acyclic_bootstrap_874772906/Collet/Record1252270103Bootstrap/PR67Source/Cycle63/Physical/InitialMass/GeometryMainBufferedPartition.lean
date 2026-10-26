import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainHighRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion LocalMoment
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open Cycle63FinalNatural CenteredMomentEnergyState Cycle63Moment.LowBranch
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentSectorLocalization

section Physical
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance mainBufferedSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

variable [Cycle63.AffineLedger] in
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
      (bufferValue e (select r)<((1+Cycle63.AffineLedger.q)/2) →
        ActualLow M H hH (st r) η₀ hQM hQη (((1+Cycle63.AffineLedger.q)/2)) e
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

end Physical
end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
