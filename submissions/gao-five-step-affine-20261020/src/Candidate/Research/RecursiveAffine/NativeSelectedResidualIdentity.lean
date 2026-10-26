/- Canonical residual normalization of the same literal selected physical source.
Copyright (c) 2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalResidual

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
namespace OAI.SevenEighths.Cycle153CanonicalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve ConcreteTraceCRT LocalMoment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentFirstAmplificationChoice CenteredMomentFixedRowMask CenteredExceptionalProfile
open CenteredMomentCommonPairedSource
open CenteredMomentCommonLinearNormalization CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondHeightFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSourceLiveColumn
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentSectorLocalization CenteredMomentInductionEnergy
open Cycle63Moment Cycle63Moment.LowBranch Cycle63FinalLow Cycle63FinalNatural Cycle63InitialMass
open Cycle153LowPhysical
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSecondPhysicalBlock CenteredMomentSourceLiveColumn
open CenteredMomentSecondHeightFamily CenteredMomentSecondCanonicalScalar Cycle153LowPhysical
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

/-- The exact selected physical coefficient contains the original first
mass/child-volume ratio, the first radius and the second common normalizer.
It is not moved into a returned family or replaced by a cardinality. -/
def selectedPhysicalCoefficient {Label : Type}
    (datum : Label→SecondInputDatum alpha)(mass childVolume : Label→ℝ)(r : Label) : ℝ :=
  mass r/childVolume r*(datum r).K*normalizer (datum r).C (datum r).D (datum r).inactive

/-- The genuine ordinary canonical source is the same column energy
used by the selected-forest source theorem. This is a source identity,
with the physical coefficient unaltered on both sides. -/
theorem actual_selected_residual_shell_eq_columns {Label : Type} [Fintype Label]
    (s : Input alpha)(ch : Label→Chain s)
    {Z Mrow amp omega xi b : ℝ}{N : ℕ}
    (g : ∀r,LiveMainGeometry s (ch r) Z Mrow amp omega xi b N)
    (datum : Label→SecondInputDatum alpha)(second : Bool)
    (frame : ∀r,CanonicalSourceFrame s (ch r) (g r) (datum r) second)
    (hE : ∀r,Supported (ch r).E₂)
    (chi0 : Label→RayFourExpansion.RayCharacter)(Q : Ideal O)(m : O)
    (mass childVolume : Label→ℝ)(ray : Label→RayFourExpansion.RayCharacter)
    (height : Label→ℝ)(zs : Label→Finset O)(Ds : Finset (Ideal O)) :
    (∑r,∑D∈Ds,nativeResidualCost second (fun r=>ordinarySecondDatum (datum r) (chi0 r) Q m)
      (selectedPhysicalCoefficient datum mass childVolume) ray height zs (fun _ _=>1) r D)=
    ∑r,selectedPhysicalCoefficient datum mass childVolume r*
      (∑D∈Ds,∑z∈zs r,‖normalizedColumn (withHeight (ch r).first ((g r).datum.τ (ray r)) (height r))
        (ch r).E₂ (hE r) (ch r).R₂ (datum r).seed D z‖^2) := by
  rw [ordinary_residual_shell_eq_actual_chain s ch g datum second frame hE chi0 Q m
    (selectedPhysicalCoefficient datum mass childVolume) ray height zs Ds]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]

/-- Keep the actual AtState outer scale exactly once while passing from
the ordinary residual shell to its literal selected physical row sum. -/
theorem actual_selected_raw_residual_shell_eq_columns {Label : Type} [Fintype Label]
    (s : Input alpha)(ch : Label→Chain s)
    {Z Mrow amp omega xi b : ℝ}{N : ℕ}
    (g : ∀r,LiveMainGeometry s (ch r) Z Mrow amp omega xi b N)
    (datum : Label→SecondInputDatum alpha)(second : Bool)
    (frame : ∀r,CanonicalSourceFrame s (ch r) (g r) (datum r) second)
    (hE : ∀r,Supported (ch r).E₂)
    (chi0 : Label→RayFourExpansion.RayCharacter)(Q : Ideal O)(m : O)
    (mass childVolume : Label→ℝ)(ray : Label→RayFourExpansion.RayCharacter)
    (height : Label→ℝ)(zs : Label→Finset O)(Ds : Finset (Ideal O))(rawOuter : ℝ) :
    Z^rawOuter*(∑r,∑D∈Ds,nativeResidualCost second (fun r=>ordinarySecondDatum (datum r) (chi0 r) Q m)
      (selectedPhysicalCoefficient datum mass childVolume) ray height zs (fun _ _=>1) r D)=
    Z^rawOuter*(∑r,selectedPhysicalCoefficient datum mass childVolume r*
      (∑D∈Ds,∑z∈zs r,‖normalizedColumn (withHeight (ch r).first ((g r).datum.τ (ray r)) (height r))
        (ch r).E₂ (hE r) (ch r).R₂ (datum r).seed D z‖^2)) :=
  congrArg (fun x : ℝ=>Z^rawOuter*x)
    (actual_selected_residual_shell_eq_columns s ch g datum second frame hE chi0 Q m mass childVolume ray height zs Ds)

end
end OAI.SevenEighths.Cycle153CanonicalLow
#print axioms OAI.SevenEighths.Cycle153CanonicalLow.actual_selected_raw_residual_shell_eq_columns
