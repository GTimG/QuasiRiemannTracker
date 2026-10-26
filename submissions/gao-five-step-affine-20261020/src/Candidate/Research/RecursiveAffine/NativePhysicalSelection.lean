/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativePhysicalForest
import Candidate.Research.RecursiveAffine.WholeForestAttainer

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily Cycle63Moment Cycle63InitialMass Cycle153SourceReturn
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSectorLocalization CenteredMomentCommonAllocationSum
open CanonicalQuadraticSieve CenteredMomentSecondCanonicalScalar
open CenteredMomentCommonPairedSource CenteredMomentSourceLiveColumn
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open LocalMoment CenteredMomentSecondHeightFamily CenteredMomentSourceMass
open CenteredMomentEligibleEnergy CenteredMomentChildRows CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondInputCapacitySource
attribute [local irreducible] Finset.univ mainLowCompleteSelectedCost mainLowSourceRows
  mainLowPhysicalCompleteCost DepthReturnedFamily.value

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

variable [Cycle63.AffineLedger] in
/-- One actual buffered column-source sum in the native full physical
operator. No new set of arithmetic labels, source allocations, or residual
rays is substituted for the original datum. -/
def nativeBufferedColumnCost {Label : Type} [Fintype Label]
    (second : Bool) (datum : Label→SecondInputDatum alpha) (coefficient : Label→ℝ)
    (t u e : ℝ)
    (select : (r : Label)→(chi psi : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (datum r) (fun _=>True)→BufferIndex e)
    (chi psi : RayFourExpansion.RayCharacter) (p : BufferIndex e) : ℝ :=
  ∑r : Label,∑D∈(datum r).block.divisors.filter Squarefree,
    (coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive)*
    (∑z∈mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
      (select r chi psi) p,
      ‖normalizedColumn
        (withHeight (datum r).input (if second then (datum r).τ psi⁻¹ else (datum r).τ chi)
          ((datum r).input.t+2*Real.pi*(u-(if second then -t else t))))
        (if second then (datum r).D else (datum r).C)
        (mainLowPhysicalSupported second (datum r))
        (datum r).R (datum r).seed D z‖^2)

variable [Cycle63.AffineLedger] in
/-- Actual component source receipts construct ONE whole attaining forest
for the complete physical operator. Maximization is over complete forests,
so terminal depths and all physical residual/deletion metadata stay tied
together. Fixed ray and buffer cardinalities are paid as constants, and
are not added to the physical history key. -/
theorem actual_complete_low_choose_forest
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M ≤ H}
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {eta : Character} {Z Bnorm T : ℝ} {root : O}
    {Label : Type} [Fintype Label]
    (N : ℕ) (supply ap : ℝ) (second : Bool) (datum : Label→SecondInputDatum alpha)
    (coefficient : Label→ℝ) (t u e : ℝ)
    (select : (r : Label)→(chi psi : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (datum r) (fun _=>True)→BufferIndex e)
    (Trace : RayFourExpansion.RayCharacter→RayFourExpansion.RayCharacter→BufferIndex e→
      DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root→Prop)
    (oldBound sourceConstant : ℝ)
    (hZ : 0 ≤ Z) (hlower : 0<lowerFactor N supply ap)
    (hold : 0 ≤ oldBound) (hsourceConstant : 0 ≤ sourceConstant)
    (hpositive : ∀r chi psi p z,
      z∈mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
        (select r chi psi) p → 1 ≤ p.1.val)
    (hsource : ∀(chi psi : RayFourExpansion.RayCharacter)(p : BufferIndex e),1 ≤ p.1.val →
      ∃F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root,
        Trace chi psi p F ∧ nativeBufferedColumnCost second datum coefficient t u e select chi psi p ≤
          oldBound+sourceConstant*F.value) :
    ∃F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root,
      (F=emptyReturnedForest ∨ ∃chi psi p,1 ≤ p.1.val ∧ Trace chi psi p F) ∧
      mainLowPhysicalCompleteCost N supply ap second datum coefficient t u select ≤
        (1/lowerFactor N supply ap)*
          ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*
            (Fintype.card (BufferIndex e):ℝ)*(oldBound+2*sourceConstant*F.value)) := by
  classical
  let Good := RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter ×
    {p : BufferIndex e // 1 ≤ p.1.val}
  let Config := Option Good
  let chosenGood := fun c : Good => Classical.choose (hsource c.1 c.2.1 c.2.2.val c.2.2.property)
  let pick : Config→DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root :=
    fun c=>match c with | none=>emptyReturnedForest | some k=>chosenGood k
  have hbounded : BddAbove (Set.range (fun c : Config=>(pick c).value)) := by
    refine ⟨∑c : Config,(pick c).value,?_⟩
    rintro _ ⟨c,rfl⟩
    exact Finset.single_le_sum (fun k _=>(pick k).value_nonneg hZ) (Finset.mem_univ c)
  obtain ⟨chosen,hchosen⟩ := whole_source_forest_attainer pick hZ hbounded
  let F := pick chosen
  have htrace : F.value=0 ∨ ∃chi psi p,1 ≤ p.1.val ∧ Trace chi psi p F := by
    cases chosen with
    | none =>
      left
      exact emptyReturnedForest_value
    | some c =>
      right
      exact ⟨c.1,c.2.1,c.2.2.val,c.2.2.property,
        (Classical.choose_spec (hsource c.1 c.2.1 c.2.2.val c.2.2.property)).1⟩
  have hbound : mainLowPhysicalCompleteCost N supply ap second datum coefficient t u select ≤
      (1/lowerFactor N supply ap)*
        ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*
          (Fintype.card (BufferIndex e):ℝ)*(oldBound+2*sourceConstant*F.value)) := by
    apply actual_complete_low_source_return N supply ap second datum coefficient t u e select F
      oldBound (2*sourceConstant) hZ hlower hold (mul_nonneg (by norm_num) hsourceConstant) hpositive
    intro chi psi p hp
    let c : Good := ⟨chi,psi,⟨p,hp⟩⟩
    have hc := (Classical.choose_spec (hsource chi psi p hp)).2
    have hvalue := hchosen (some c)
    have hineq : nativeBufferedColumnCost second datum coefficient t u e select chi psi p ≤
        oldBound+(2*sourceConstant)*F.value := by
      apply hc.trans
      calc
        _ ≤ oldBound+sourceConstant*(2*F.value) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hvalue hsourceConstant)
        _ = _ := by ring
    exact hineq
  by_cases hzF : F.value=0
  · refine ⟨emptyReturnedForest,Or.inl rfl,?_⟩
    simpa only [hzF,emptyReturnedForest_value] using hbound
  · exact ⟨F,Or.inr (htrace.resolve_left hzF),hbound⟩

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_complete_low_choose_forest
