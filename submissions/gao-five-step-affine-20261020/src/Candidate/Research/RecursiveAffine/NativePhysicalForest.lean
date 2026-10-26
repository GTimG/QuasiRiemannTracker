/- Copyright (c) 2026 Hailey Collet; returned-source assembly (c) 2026 Zhongpai Gao.
Released under Apache 2.0. The native complete source reindex is unchanged. -/
import Candidate.Research.RecursiveAffine.NativeCommonForest
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPhysicalPayment

set_option autoImplicit false
set_option maxHeartbeats 450000
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
open LocalMoment
open CenteredMomentSecondHeightFamily CenteredMomentSourceMass
open CenteredMomentEligibleEnergy CenteredMomentChildRows CenteredMomentCommonHeightEnvelope
open CenteredMomentFirstSourceReduction CenteredMomentSecondInputCapacitySource

attribute [local irreducible] Finset.univ mainLowCompleteSelectedCost mainLowSourceRows
  mainLowPhysicalCompleteCost DepthReturnedFamily.value

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

variable [Cycle63.AffineLedger] in
/-- Transport the actual selected column-source return through the COMPLETE
native physical LOW operator. Both rays, ordinary rows, canonical buffered
bins, the child volume, the own-second normalizer, and the physical lower
factor remain literal. The SAME source-wide whole forest pays every
configuration. Only the fixed ray and buffered-bin cardinalities are
charged; no first-seed reciprocal is inserted into its value. -/
theorem actual_complete_low_source_return
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
    (F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm T root)
    (oldBound sourceConstant : ℝ)
    (hZ : 0 ≤ Z) (hlower : 0<lowerFactor N supply ap)
    (hold : 0 ≤ oldBound) (hsourceConstant : 0 ≤ sourceConstant)
    (hpositive : ∀r chi psi p z,
      z∈mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
        (select r chi psi) p → 1 ≤ p.1.val)
    (hcolumns : ∀(chi psi : RayFourExpansion.RayCharacter)(p : BufferIndex e),1 ≤ p.1.val →
      (∑r : Label,∑D∈(datum r).block.divisors.filter Squarefree,
        (coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive)*
        (∑z∈mainLowPaymentRows (mainLowSourceRows second (datum r) (fun _=>True))
          (select r chi psi) p,
          ‖normalizedColumn
            (withHeight (datum r).input (if second then (datum r).τ psi⁻¹ else (datum r).τ chi)
              ((datum r).input.t+2*Real.pi*(u-(if second then -t else t))))
            (if second then (datum r).D else (datum r).C)
            (mainLowPhysicalSupported second (datum r))
            (datum r).R (datum r).seed D z‖^2)) ≤ oldBound+sourceConstant*F.value) :
    mainLowPhysicalCompleteCost N supply ap second datum coefficient t u select ≤
      (1/lowerFactor N supply ap)*
        ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*
          (Fintype.card (BufferIndex e):ℝ)*(oldBound+sourceConstant*F.value)) := by
  have hbound : 0 ≤ oldBound+sourceConstant*F.value :=
    add_nonneg hold (mul_nonneg hsourceConstant (F.value_nonneg hZ))
  rw [actual_main_low_complete_physical_reindex]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg zero_le_one hlower.le)
  have hbin (chi psi : RayFourExpansion.RayCharacter) :
      mainLowCompleteSelectedCost
        (fun r=>mainLowSourceRows second (datum r) (fun _=>True)) (fun r=>select r chi psi)
        (fun r=>(datum r).block.divisors.filter Squarefree)
        (fun r _=>coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive)
        (fun r D z=>‖normalizedColumn
          (withHeight (datum r).input (if second then (datum r).τ psi⁻¹ else (datum r).τ chi)
            ((datum r).input.t+2*Real.pi*(u-(if second then -t else t))))
          (if second then (datum r).D else (datum r).C)
          (mainLowPhysicalSupported second (datum r))
          (datum r).R (datum r).seed D z‖^2) ≤
        (Fintype.card (BufferIndex e):ℝ)*(oldBound+sourceConstant*F.value) := by
    unfold mainLowCompleteSelectedCost
    exact main_low_payment_complete_cost_le
      (fun r=>mainLowSourceRows second (datum r) (fun _=>True)) (fun r=>select r chi psi)
      (fun r=>(datum r).block.divisors.filter Squarefree)
      (fun r _=>coefficient r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive)
      (fun r D z=>‖normalizedColumn
        (withHeight (datum r).input (if second then (datum r).τ psi⁻¹ else (datum r).τ chi)
          ((datum r).input.t+2*Real.pi*(u-(if second then -t else t))))
        (if second then (datum r).D else (datum r).C)
        (mainLowPhysicalSupported second (datum r)) (datum r).R (datum r).seed D z‖^2)
      (oldBound+sourceConstant*F.value) hbound
      (fun r p z hz=>hpositive r chi psi p z hz) (hcolumns chi psi)
  calc
    _ ≤ ∑_chi : RayFourExpansion.RayCharacter,∑_psi : RayFourExpansion.RayCharacter,
        (Fintype.card (BufferIndex e):ℝ)*(oldBound+sourceConstant*F.value) :=
      Finset.sum_le_sum (fun chi _=>Finset.sum_le_sum (fun psi _=>hbin chi psi))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_two];ring

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_complete_low_source_return
