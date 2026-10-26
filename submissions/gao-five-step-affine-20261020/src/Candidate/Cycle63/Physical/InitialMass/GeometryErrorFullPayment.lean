/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorAdmission
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorNormalizedClosure
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorNormalizedPayment

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
universe u v
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open CenteredMomentFirstSectors CenteredMomentFirstDiscardedEnergy
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
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentFirstAnnularInput CenteredMomentSecondRadicalBudget CenteredMomentLogDyadic
local instance errorFullPaymentSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

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

/-- The supported arithmetic label is obtained from the original physical
block, before choosing a common second allocation. -/
noncomputable def geometryErrorSupportedSecondLabel : FirstSourceLabel :=
  let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
  ⟨(d.C,d.D),⟨d.inactive,by
    exact second_block_nonzero_inactive d.block ballProfile hne⟩⟩

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

variable [Cycle63.AffineLedger] in
/-- The post-column coefficient of one second block, with its nominal width and branch
reserve measured in the ledger unit `unit`. -/
noncomputable def geometryErrorColumnScalar
    (unit : ℝ)(P : Finset (Ideal O))(weight lf error εcommon : ℝ) : ℝ :=
  let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
  let chain := geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
    (if second then d.D else d.C) d.R
    (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second)
  let g := geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁
  let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i
  ((56/(P.card:ℝ))*weight*(K/lf)*normalizer d.C d.D d.inactive*16*((chain.k+1):ℝ)/volume chain.extracted)*
    Z^(errorRemoval chain.p Z chain.k-errorMoving chain.p Z chain.k)*
    (chain.E₂.absNorm:ℝ)^(εcommon-1)*Z^(g.nominal unit+error-unit*branchReserve chain.k)

variable [Cycle63.AffineLedger] in
/-- The literal post-column coefficient retains the prime denominator,
removal gain and selected source volume in the arithmetic label payment.
The nominal width in the ledger unit exceeds the one at the radial scale by
`unit - Mrow`. -/
theorem actual_geometry_error_column_scalar_identity
    (unit : ℝ)(P : Finset (Ideal O))(weight lf error εcommon : ℝ) :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    let chain := geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
      (if second then d.D else d.C) d.R
      (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second)
    let g := geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁
    let firstLabel := geometryFirstLabel s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
    let secondLabel := geometryErrorSupportedSecondLabel reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne
    let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i
    ((56/(P.card:ℝ))*weight*(K/lf)*normalizer d.C d.D d.inactive*16*((chain.k+1):ℝ)/volume chain.extracted)*
      Z^(errorRemoval chain.p Z chain.k-errorMoving chain.p Z chain.k)*
      (chain.E₂.absNorm:ℝ)^(εcommon-1)*Z^(g.nominal unit+error-unit*branchReserve chain.k)=
      Z^(unit-Mrow)*(((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf)*
        extractedErrorLabelScalar reflected second firstLabel secondLabel Z unit Mrow amp
          (frequencyLoss Z 32 ξ) reserve error εcommon (volume s) (volume chain.extracted) p (errorIndex i+1)) := by
  intro d chain g firstLabel secondLabel K
  have hr : K=firstErrorTailRadius reflected firstLabel Z Mrow (volume s) amp
      (frequencyLoss Z 32 ξ) reserve p (errorIndex i+1) := rfl
  have hn : g.nominal Mrow=errorNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
      (errorRemoval p Z (errorIndex i+1)) (errorMoving p Z (errorIndex i+1))
      (if reflected then firstLabel.1.2 else firstLabel.1.1)
      (if reflected then firstLabel.1.1 else firstLabel.1.2)
      secondLabel.1.1 secondLabel.1.2 secondLabel.2.val := by
    cases reflected <;> rfl
  have hshift : g.nominal unit+error-unit*branchReserve chain.k=
      (unit-Mrow)+(g.nominal Mrow+error-unit*branchReserve chain.k) := by
    unfold Geometry.nominal errorNominal
    ring
  have hcount : (chain.k:ℝ)+1=(errorIndex i+2:ℝ) := by
    change (↑(errorIndex i+1):ℝ)+1=(errorIndex i+2:ℝ)
    push_cast
    ring
  rw [hshift,Real.rpow_add (zero_lt_one.trans hZ)]
  calc
    _=Z^(unit-Mrow)*(((56/(P.card:ℝ))*weight*(K/lf)*normalizer d.C d.D d.inactive*16*((chain.k+1):ℝ)/
        volume chain.extracted)*Z^(errorRemoval chain.p Z chain.k-errorMoving chain.p Z chain.k)*
        (chain.E₂.absNorm:ℝ)^(εcommon-1)*Z^(g.nominal Mrow+error-unit*branchReserve chain.k)) := by ring
    _=_ := by
      congr 1
      rw [hr,hn,hcount]
      exact actual_error_normalized_scalar_identity reflected second firstLabel secondLabel Z unit Mrow amp
        (frequencyLoss Z 32 ξ) reserve error εcommon (volume s) (volume chain.extracted) lf weight
        P p i (zero_lt_one.trans hZ)

end Selected

section ScalarFamily
variable {Label : Type*}[Fintype Label]
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

variable (index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v)
variable (hne : ∀n : Label,(geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ (index n)).block.value ballProfile≠0)

variable [Cycle63.AffineLedger] in
/-- All second labels share the extracted source and prime denominator;
the common allocation remains fixed before both ray and residual sums. -/
theorem actual_geometry_error_column_scalar_sum
    (second : Bool)(unit : ℝ)(P : Finset (Ideal O))(weight lf error εcommon : ℝ) :
    (∑n : Label,geometryErrorColumnScalar reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
      hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁ unit P weight lf error εcommon)=
    Z^(unit-Mrow)*(((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf)*
      ∑n : Label,extractedErrorLabelScalar reflected second
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
        (geometryErrorSupportedSecondLabel reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ (index n) (hne n))
        Z unit Mrow amp (frequencyLoss Z 32 ξ) reserve error εcommon
        (volume s) (volume (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)) p (errorIndex i+1)) := by
  rw [Finset.mul_sum,Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact actual_geometry_error_column_scalar_identity reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
    hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁ unit P weight lf error εcommon

end ScalarFamily

section ScalarDisintegration
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

set_option linter.defProp false in
variable [Cycle63.AffineLedger] in
/-- Genuine second-label enlargement pays one full four-dyad box, after
the literal normalized coefficient has been restored. -/
def actual_geometry_error_scalar_disintegration
    (rows : Finset (GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v))
    (hne : ∀n∈rows,(geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block.value ballProfile≠0)
    (box : Finset (Fin 4→ℤ))
    (hbox : ∀n∈rows,actualSecondDyad
      (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)
      ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1))
      q.1.val.2.1.val (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)
      (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i)
      Z ξ n∈box)
    (second : Bool)(unit : ℝ)(P : Finset (Ideal O))(weight lf error εcommon : ℝ)
    (hweight : 0≤weight)(hlf : 0<lf) :=
  let source := geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v
  let R₂ := (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1)
  let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i
  let Tsec := geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i
  let firstLabel := geometryFirstLabel s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
  let hU : ∀n∈rows,ActualSecondBlockIndex.IsInactive n :=
    fun n hn=>second_block_nonzero_inactive
      (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block
      ballProfile (hne n hn)
  let cost := fun l=>extractedErrorLabelScalar reflected second firstLabel l Z unit Mrow amp
    (frequencyLoss Z 32 ξ) reserve error εcommon (volume s) (volume source) p (errorIndex i+1)
  let hseed := actual_first_live_squarefree
    (geometryFirstSource s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (fun _=>logAnnulus) q.1.val q.1.property
  let hz₁ : source.W₁ 0=0 := hw₁
  let hz₂ : source.W₂ 0=0 := hw₂
  let hcost : ∀l∈actualSecondLabels source R₂ q.1.val.2.1.val,∀n∈box,0≤ cost l := by
    intro l hl _ _
    have hg := actual_second_labels_gates source R₂ q.1.val.2.1.val hseed hz₁ hz₂ l hl
    have hn := (normalizer_pos l.1.1 l.1.2 hg.1 l.2.val).le
    have hV := (volume_pos source).le
    have hrad : 0≤firstErrorTailRadius reflected firstLabel Z Mrow (volume s) amp
        (frequencyLoss Z 32 ξ) reserve p (errorIndex i+1) := by
      unfold firstErrorTailRadius errorCommonRadius
      exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _
    dsimp only [cost]
    unfold extractedErrorLabelScalar
    positivity
  let hpaid := actual_second_positive_disintegration source R₂ q.1.val.2.1.val K Tsec Z ξ
    rows hU box hbox (fun l _=>cost l) hcost
  let hpaid' :
      (∑n : rows,cost (geometryErrorSupportedSecondLabel reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val (hne n.val n.property)))≤
      (box.card:ℝ)*∑l∈actualSecondLabels source R₂ q.1.val.2.1.val,cost l := by
    have hlabel (n : rows) :
        actualSecondSupportedLabel source R₂ q.1.val.2.1.val K Tsec Z ξ n.val (hU n.val n.property)=
        geometryErrorSupportedSecondLabel reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val (hne n.val n.property) := rfl
    simpa only [hlabel,Finset.sum_const,nsmul_eq_mul] using hpaid
  let hsum := actual_geometry_error_column_scalar_sum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
    hw₁ hw₂ hp hcop ψ hυ hf₁ (fun n : rows=>n.val) (fun n=>hne n.val n.property) second unit P weight lf error εcommon
  let hfactor : 0≤((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf) := by positivity
  hsum.le.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpaid' hfactor)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))

end ScalarDisintegration

end
end OAI.SevenEighths.Cycle63InitialMass
