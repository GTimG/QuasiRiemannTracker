import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorAdmission
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorNormalizedAssembly
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
universe u v
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open Filter Set HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondEnergySplit
open CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondHeightFamily CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondRetainedRows
open CenteredMomentSecondActivePhysicalDictionary CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondLiveBlock
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentEligibleEnergy CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAmplificationErrorEnergy CenteredMomentRestrictedEnergy
open CenteredMomentAllocatedRayDictionary CenteredMomentSlotRatios
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open Cycle63FinalNatural Cycle63Moment Cycle63FinalError Cycle63FinalErrorCapacity
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonAllocationSum
open CenteredMomentPrimeElements CenteredMomentRankinRadical
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentFirstAnnularInput CenteredMomentSecondRadicalBudget
local instance errorNormalizedClosureSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {α : Type*} [Fintype α] [DecidableEq α]
section Selected
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
variable (p : O) (i : Fin 3)
variable (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
variable (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
variable (n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v)
variable (hne : (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block.value ballProfile≠0)
variable (second : Bool)

/-- The allocation is fixed by the original nonzero physical block, before
its residual projector, either ray, or any external Mellin height. -/
noncomputable def geometryErrorSelectedAllocation :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    actualAllocations d.input.pools (if second then d.D else d.C) :=
  let nz : geometryErrorNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ :=
    (geometryErrorNonzeroBlock reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne)
  Classical.choose (actual_geometry_error_live_common_allocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ nz second)

theorem geometryErrorSelectedAllocation_nonzero :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    frozenCoefficient (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second).val
      (if second then d.D else d.C) d.R d.input.ν d.input.W d.input.P≠0 :=
  Classical.choose_spec (actual_geometry_error_live_common_allocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂
    (geometryErrorNonzeroBlock reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne) second)

variable (hp : p≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→
      IsCoprime (Ideal.span {p}) I)
    (ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
      fixedBadMask p (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)

/-- Actual admission uses the live allocation supplied by the original
block; the inducing and full stored-pool coprimality gates stay explicit. -/
noncomputable def geometryErrorSelectedGeometry :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    Geometry s (geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
      (if second then d.D else d.C) d.R (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second))
      Z Mrow amp (frequencyLoss Z 32 ξ+reserve) ξ b (fixedFactor:ℝ) N :=
  geometryErrorActualGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
    hp hcop hw₁ hw₂ (geometryErrorNonzeroBlock reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne) second
    (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second) ψ hυ hf₁
    (geometryErrorSelectedAllocation_nonzero reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second)

/-- Admission preserves the literal extracted frequency radius in both
first orientations; it does not replace the common source radius. -/
theorem geometryErrorSelectedGeometry_radius :
    (geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁).radius=
      (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).radius := by
  change errorRadius
    (geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
      (if second then (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).D
       else (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).C)
      (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).R
      (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second))
    (geometryErrorOtherIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
    (geometryErrorInactive reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
    Z Mrow amp (frequencyLoss Z 32 ξ) reserve ξ b N=
      frequencyRadius (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i) Z ξ
  exact actual_geometry_error_radius reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hp hcop _ _ _

/-- Both full physical zero-mode sums equal the columns of the admitted
geometry. The right ray stays inverse and its height shift stays negative. -/
theorem geometryErrorSelectedGeometry_complete_columns
    (Q : Ideal O)(hQ : Q≤Ideal.span {(72:O)})
    (χ₀ χ ψ₂ : RayCharacter)(L : Ideal O)(tₑ u : ℝ) :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    let chain := geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
      (if second then d.D else d.C) d.R (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second)
    let g := geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁
    let hE : Supported chain.E₂ := by
      cases second with
      | false => exact d.hC
      | true => exact d.hD
    (∑z∈partRows false d.input.η χ₀ Q fixedBadMask d.C d.D d.inactive d.radius,
      if second then
        ‖normalizedColumn (withHeight d.input (d.τ ψ₂⁻¹) (d.input.t+2*Real.pi*(u-(-tₑ))))
          d.D d.hD d.R d.seed L (-z)‖^2
      else
        ‖normalizedColumn (withHeight d.input (d.τ χ) (d.input.t+2*Real.pi*(u-tₑ)))
          d.C d.hC d.R d.seed L z‖^2)=
    ∑z∈partRows false chain.υ (if second then ψ₂⁻¹ else χ) Q fixedBadMask
      g.C g.D g.U g.radius,
      ‖normalizedColumn (withHeight chain.extracted (g.τ (if second then ψ₂⁻¹ else χ))
        (chain.extracted.t+2*Real.pi*(u-(if second then -tₑ else tₑ))))
        chain.E₂ hE chain.R₂ d.seed L z‖^2 := by
  intro d chain g hE
  apply (actual_error_complete_column_rows d.input d.τ d.C d.D d.hC d.hD d.inactive
    d.R d.seed L Q d.radius hQ χ₀ χ ψ₂ second tₑ u).trans
  have hr := geometryErrorSelectedGeometry_radius reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁
  change _=∑z∈partRows false chain.υ (if second then ψ₂⁻¹ else χ) Q fixedBadMask
    g.C g.D g.U g.radius,_
  rw [show g.radius=d.radius from hr]
  cases second <;> rfl

end Selected

end
end OAI.SevenEighths.Cycle63InitialMass


end Record1252270103Bootstrap.PR67
