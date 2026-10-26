import Candidate.Target830.High.BalancedMass
import Candidate.Target830.Source.LowPhysical.MainLowPhysicalCost

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.TargetHigh830
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

theorem balanced_first_high_mass_le (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (D Z ξ ε : ℝ) (hK : 0<Z^D) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK key)) (hZ : 1<Z) :
    balancedFirstHighMass reflected s R seed W D Z ξ ε hK key j ≤
      geometryFirstHighMass reflected s R seed W D Z ξ ε hK key j := by
  have hSigma := Target830.Source.actual_surplus_nonneg s R seed (Z^D) Z ξ hZ j.1.val
  have hp : Z^(-Target830.Source.surplus (geometryExponents s R seed (Z^D) Z ξ j.1.val))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hZ.le (by linarith)
  exact (mul_le_mul_of_nonneg_left hp
    (geometry_first_high_mass_nonneg reflected s R seed W D Z ξ ε hK key j)).trans_eq (mul_one _)

theorem main_low_complete_cost_mono (plane : SourcePlane) {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (ha : 0<a) (hap : 0<ap) (second : Bool)
    (d : Label→SecondInputDatum α) (c c' : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e)
    (hcc : ∀l,c l≤c' l) :
    Target830.Source.LowPhysical.mainLowPhysicalCompleteCost (P:=plane) N a ap second d c t u select ≤
      Target830.Source.LowPhysical.mainLowPhysicalCompleteCost (P:=plane) N a ap second d c' t u select := by
  unfold Target830.Source.LowPhysical.mainLowPhysicalCompleteCost
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
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.balanced_first_high_mass_le
#print axioms OAI.SevenEighths.TargetHigh830.main_low_complete_cost_mono
