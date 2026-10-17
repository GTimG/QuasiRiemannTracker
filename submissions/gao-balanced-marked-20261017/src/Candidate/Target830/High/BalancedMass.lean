import Candidate.Target830.High.Allocation
import Candidate.Target830.Source.BalancedColumns
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry Cycle63InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSourceReduction Cycle63FinalCapacity
open CenteredMomentFirstPhysicalSource CenteredMomentExceptionalAmplitudePair CenteredMomentEnergyState
open CenteredMomentChildRows CenteredMomentCommonHeightEnvelope
open scoped Classical BigOperators SchwartzMap
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

def balancedFirstHighMass (reflected : Bool) (s : Input alpha) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (D Z xi e : ℝ) (hK : 0<Z^D) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z xi hK bin)) : ℝ :=
  geometryFirstHighMass reflected s R seed W D Z xi e hK bin j*
    Z^(-Target830.Source.surplus (geometryExponents s R seed (Z^D) Z xi j.1.val))

theorem balanced_first_high_mass_nonneg (reflected : Bool) (s : Input alpha) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (D Z xi e : ℝ) (hK : 0<Z^D) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z xi hK bin)) (hZ : 0 ≤ Z) :
    0 ≤ balancedFirstHighMass reflected s R seed W D Z xi e hK bin j := by
  exact mul_nonneg (geometry_first_high_mass_nonneg reflected s R seed W D Z xi e hK bin j)
    (Real.rpow_nonneg hZ _)

theorem balanced_first_high_mass_formula (reflected : Bool) (s : Input alpha) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (D Z xi e : ℝ) (hK : 0<Z^D) (hZ : 0<Z) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z xi hK bin)) :
    balancedFirstHighMass reflected s R seed W D Z xi e hK bin j=
    ‖Target830.Source.balancedColumnScalar reflected s R seed (Z^D) Z xi D
      (Real.logb Z (volume s.toData)) hK bin
      (fun q=>normPhase (coordinateBlock s R seed W (Z^D) Z xi q)) j‖^2*
      ((geometryColumnIdeal reflected s R seed (Z^D) Z xi hK bin j).absNorm:ℝ)^(e-1) := by
  rw [Target830.Source.balancedColumnScalar_norm_sq reflected s R seed (Z^D) Z xi D
    (Real.logb Z (volume s.toData)) hK bin
    (fun q=>normPhase (coordinateBlock s R seed W (Z^D) Z xi q)) j hZ]
  unfold balancedFirstHighMass geometryFirstHighMass
  ring

/-- The new denominator cancels the actual surplus label by label. The
external D-compensator and original support constant are unchanged. -/
theorem actual_balanced_uniform_high_mass (reflected : Bool) (N : ℕ) (lo ap : ℝ)
    (hlo : 0<lo) (hap : 0<ap) (s : Input alpha) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (D Z xi B e : ℝ) (hZ : 1<Z) (hK : 0<Z^D)
    (he : 0 ≤ e) (hcard : Fintype.card alpha ≤ N) (hlower : lo ≤ s.lower)
    (hs : Squarefree seed) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (hsource : sourceRadius s ≤ Z^B)
    (hs1 : ∀x,s.W₁ x≠0 → ap ≤ x) (hs2 : ∀x,s.W₂ x≠0 → ap ≤ x)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z xi hK bin)) :
    balancedFirstHighMass reflected s R seed W D Z xi e hK bin j ≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*e)/
        Z^(balancedGeometrySide reflected (Real.logb Z (volume s.toData))
          (geometryExponents s R seed (Z^D) Z xi j.1.val)) := by
  have hp : 0<Z := zero_lt_one.trans hZ
  have hm:=actual_geometry_uniform_high_mass reflected N lo ap hlo hap s R seed W D Z xi B e
    hZ hK he hcard hlower hs hz1 hz2 hsource hs1 hs2 bin j
  have hh:=mul_le_mul_of_nonneg_right hm
    (Real.rpow_nonneg hp.le (-Target830.Source.surplus (geometryExponents s R seed (Z^D) Z xi j.1.val)))
  unfold balancedFirstHighMass
  refine hh.trans_eq ?_
  have hid : balancedGeometrySide reflected (Real.logb Z (volume s.toData))
      (geometryExponents s R seed (Z^D) Z xi j.1.val)=
      geometryHighSide reflected (Real.logb Z (volume s.toData))
        (geometryExponents s R seed (Z^D) Z xi j.1.val)+
      Target830.Source.surplus (geometryExponents s R seed (Z^D) Z xi j.1.val) := by
    cases reflected
    · exact Target830.Source.left_eq_old _ _
    · exact Target830.Source.right_eq_old _ _
  rw [hid,Real.rpow_add hp]
  simp only [div_eq_mul_inv,mul_inv,Real.rpow_neg hp.le]
  ring


theorem balanced_geometry_side_box (reflected : Bool) (A B : ℝ) (v : Fin 5→ℝ)
    (hB : 0 ≤ B) (hA : |A| ≤ B) (hv : ∀j,0 ≤ v j ∧ v j ≤ B) :
    |balancedGeometrySide reflected A v| ≤ 5*B := by
  have ha:=abs_le.mp hA
  have hm (i j : Fin 5) : 0 ≤ max (3*v i-5*v j-v 3) 0 ∧
      max (3*v i-5*v j-v 3) 0 ≤ 3*B := by
    exact ⟨le_max_right _ _,max_le (by linarith [(hv i).2,(hv j).1,(hv 3).1]) (by linarith)⟩
  apply abs_le.mpr
  cases reflected <;>
    dsimp only [balancedGeometrySide,Target830.Source.balancedLeft,
      Target830.Source.balancedRight,QRH830.BalancedGeometry.left,
      QRH830.BalancedGeometry.right,QRH830.BalancedGeometry.side,ite_true,ite_false,
      Bool.false_eq_true]
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true]
  all_goals constructor <;> linarith [(hv 0).1,(hv 0).2,(hv 1).1,(hv 1).2,
    (hv 3).1,(hv 3).2,(hv 4).1,(hv 4).2,(hm 0 1).1,(hm 0 1).2,(hm 1 0).1,(hm 1 0).2]

end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.balanced_first_high_mass_formula
#print axioms OAI.SevenEighths.TargetHigh830.actual_balanced_uniform_high_mass
