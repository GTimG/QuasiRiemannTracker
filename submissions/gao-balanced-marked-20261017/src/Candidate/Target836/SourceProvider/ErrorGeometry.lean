import Candidate.Cycle63.Physical.FinalError.Geometry
import Candidate.Target836.SourceProvider.ErrorCapacity
import Candidate.Cycle63.Physical.FinalError.Chain

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Target874836.SourceProvider.ErrorPhysical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63FinalError
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open Cycle63FinalNatural Cycle63FinalCapacity Cycle63FinalErrorCapacity
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem error_source_capacity {s : Input α} {q : Chain s} {Z Mrow amp omega ξ b J : ℝ}
    (g : Geometry s q Z Mrow amp omega ξ b J (Fintype.card α)) (hb : 1 ≤ b)
    (hs : s.upper ≤ b) (hZ : 1 < Z) (hM : 0 < Mrow) (hP : ∀j,1 ≤ s.P j)
    (hz : (17/500)*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j)) ≤ (1/25)*Mrow)
    (haff : CenteredMomentEnergyBands.length Z s.X₁+CenteredMomentEnergyBands.length Z s.X₂+
      Named.lam*(∑j,Real.logb Z (s.P j)) ≤ Named.B*Mrow)
    (η : Character) (v : ℝ) (second : Bool) (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) (z : O)
    (hne : Cycle63.Physical.sourcePositiveRow (q.final η v).toSource second L a z≠0) :
    let cell := Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L a 0)+
      CenteredMomentEnergyBands.length Z (Cycle63Moment.LowBranch.finalPlain (q.final η v) second L a 1)+
        (9/2)*CenteredMomentAllocatedChildCapacity.remainingLogs L a Z (q.final η v).P-g.nominal  ≤ 
      Mrow*Named.errorGap cell+3*amp+(errorRemoval q.p Z q.k-errorMoving q.p Z q.k)+omega+
        supportPadding (Fintype.card α) b s.b₁ s.b₂ Z := by
  exact Target874836.SourceProvider.ErrorCapacity.actual_error_source_capacity (Fintype.card α) b hb s le_rfl hs q.C₁ q.R₁ q.B₁
    g.first_nonzero q.η₁ q.t₁ (Ideal.span {q.p}) (Ideal.span_singleton_eq_bot.not.mpr q.hp)
    q.k q.coprime q.Bp η v g.C g.D q.E₂ q.R₂ g.label q.B₂ g.second_nonzero
    g.D₁ g.hD₁.1 g.hC g.hD g.heq g.U L a Z Mrow amp omega (errorMoving q.p Z q.k)
    hZ hM hP (actual_prime_widths q.p q.hp Z hZ q.k q.hk).2.2 hz haff second z hne

#print axioms error_source_capacity
end
end Target874836.SourceProvider.ErrorPhysical
