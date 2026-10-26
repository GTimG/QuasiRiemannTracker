import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalScalarCompensation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryUniformScalar
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.BalancedMass

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths Cycle61InitialMass Record12518109Natural
open scoped Classical BigOperators SchwartzMap
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O

variable {α : Type} [Fintype α] [DecidableEq α]

def balancedFirstHighMass (reflected : Bool)(s : Input α)(modifier : CenteredMomentAddedZeroUniform.Tuple α→ℂ)(R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ))(D Z ξ ε : ℝ)(hK : 0<Z^D)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin)) : ℝ :=
  ‖balancedColumnScalar reflected s modifier R seed (Z^D) Z ξ D (Real.logb Z (volume s.toData))
    hK bin (fun q=>normPhase (coordinateBlock s modifier R seed W (Z^D) Z ξ q)) j‖^2*
    ((geometryColumnIdeal reflected s modifier R seed (Z^D) Z ξ hK bin j).absNorm:ℝ)^(ε-1)

omit [DecidableEq α] in
lemma balanced_first_high_mass_nonneg (reflected : Bool)(s : Input α)(modifier : CenteredMomentAddedZeroUniform.Tuple α→ℂ)(R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ))(D Z ξ ε : ℝ)(hK : 0<Z^D)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin)) :
    0≤balancedFirstHighMass reflected s modifier R seed W D Z ξ ε hK bin j := by
  unfold balancedFirstHighMass
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The support constant is fixed before the source and first label move. -/
theorem actual_balanced_uniform_high_mass (reflected : Bool)(N : ℕ)(lo ap : ℝ)
    (hlo : 0<lo)(hap : 0<ap)(s : Input α)(modifier : CenteredMomentAddedZeroUniform.Tuple α→ℂ)(R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ))(D Z ξ B ε : ℝ)(hZ : 1<Z)(hK : 0<Z^D)
    (hε : 0≤ε)(hcard : Fintype.card α≤N)(hlower : lo≤s.lower)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B)
    (hs₁ : ∀x,s.W₁ x≠0→ap≤x)(hs₂ : ∀x,s.W₂ x≠0→ap≤x)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin)) :
    balancedFirstHighMass reflected s modifier R seed W D Z ξ ε hK bin j≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*ε)/
        Z^(balancedGeometrySide reflected (Real.logb Z (volume s.toData))
          (geometryExponents s modifier R seed (Z^D) Z ξ j.1.val)) := by
  have hC:=actual_geometry_support_constant s N lo ap ap hcard hlo hlower hap hap
  cases reflected
  · have hh:=actual_geometry_left_mass_compensation s modifier R seed W D Z ξ B ε hZ hε hs hz₁ hz₂
      hsource ap ap hap hap hs₁ hs₂ bin j
    apply hh.trans
    have hsq : (4/((∏i,s.lo i)*ap*ap))^2≤(geometrySupportConstant N lo ap ap)^2 := by
      nlinarith [hC.1,hC.2]
    change (2*(4/((∏i,s.lo i)*ap*ap))^2*geometryDCompensator bin)*Z^(B*ε)/_≤
      (2*(geometrySupportConstant N lo ap ap)^2*geometryDCompensator bin)*Z^(B*ε)/_
    apply div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
      (geometryDCompensator_pos bin).le
  · have hh:=actual_geometry_right_mass_compensation s modifier R seed (Z^D) Z ξ D
      (Real.logb Z (volume s.toData)) B ε hK hZ hε hs hz₁ hz₂ hsource bin
      (fun q=>normPhase (coordinateBlock s modifier R seed W (Z^D) Z ξ q)) j
    apply hh.trans_eq
    change (Z^(B*ε)/Z^(QRH.Record12518109Assembly.balancedRight
      (Real.logb Z (volume s.toData)) (geometryExponents s modifier R seed (Z^D) Z ξ j.1.val)))/
        geometryDCompensator bin =
      (geometryDCompensator bin)⁻¹*Z^(B*ε)/Z^(QRH.Record12518109Assembly.balancedRight
        (Real.logb Z (volume s.toData)) (geometryExponents s modifier R seed (Z^D) Z ξ j.1.val))
    ring


end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.balanced_first_high_mass_nonneg
#print axioms QRH.Record1252270103Source.High.CoupledFirst.actual_balanced_uniform_high_mass
