import Candidate.Target836.SourceProvider.ErrorMain
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Target836.Error836.GeometryErrorNormalizedFullFamily
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorTail
import Candidate.Cycle63.Physical.InitialMass.SecondProjectorShell
import Candidate.Target836.Error836.GeometryAmplifiedRemainder
import Candidate.Cycle63.Physical.InitialMass.SecondLabelDisintegration
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorAbsoluteBox

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
universe u v
namespace OAI.SevenEighths.Target836ErrorPayment
open OAI.SevenEighths.Cycle63InitialMass
open Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
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
local notation "O" => HeckeFamily.O
local instance errorFullPaymentSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _


variable {α : Type*} [Fintype α] [DecidableEq α]
section Selected
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1 < Z) (bin : ℤ×(Fin 5→ℤ))
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
    (hυ : υ.modulus.absNorm ≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
      fixedBadMask p (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)

noncomputable def geometryErrorColumnScalar
    (P : Finset (Ideal O))(weight lf error εcommon : ℝ) : ℝ :=
  let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
  let chain := geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
    (if second then d.D else d.C) d.R
    (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second)
  let g := geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁
  let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i
  ((56/(P.card:ℝ))*weight*(K/lf)*normalizer d.C d.D d.inactive*16*((chain.k+1):ℝ)/volume chain.extracted)*
    Z^(errorRemoval chain.p Z chain.k-errorMoving chain.p Z chain.k)*
    (chain.E₂.absNorm:ℝ)^(εcommon-1)*Z^(g.nominal+error-Mrow*Target874836.SourceProvider.ErrorPhysical.branchReserve chain.k)

/-- The literal post-column coefficient retains the prime denominator,
removal gain and selected source volume in the arithmetic label payment. -/
theorem actual_geometry_error_column_scalar_identity
    (P : Finset (Ideal O))(weight lf error εcommon : ℝ) :
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
      (chain.E₂.absNorm:ℝ)^(εcommon-1)*Z^(g.nominal+error-Mrow*Target874836.SourceProvider.ErrorPhysical.branchReserve chain.k)=
      ((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf)*
        extractedErrorLabelScalar reflected second firstLabel secondLabel Z Mrow amp
          (frequencyLoss Z 32 ξ) reserve error εcommon (volume s) (volume chain.extracted) p (errorIndex i+1) := by
  intro d chain g firstLabel secondLabel K
  have hr : K=firstErrorTailRadius reflected firstLabel Z Mrow (volume s) amp
      (frequencyLoss Z 32 ξ) reserve p (errorIndex i+1) := rfl
  have hn : g.nominal=errorNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
      (errorRemoval p Z (errorIndex i+1)) (errorMoving p Z (errorIndex i+1))
      (if reflected then firstLabel.1.2 else firstLabel.1.1)
      (if reflected then firstLabel.1.1 else firstLabel.1.2)
      secondLabel.1.1 secondLabel.1.2 secondLabel.2.val := by
    cases reflected <;> rfl
  rw [hr,hn]
  have hcount : (chain.k:ℝ)+1=(errorIndex i+2:ℝ) := by
    change (↑(errorIndex i+1):ℝ)+1=(errorIndex i+2:ℝ)
    push_cast
    ring
  rw [hcount]
  exact actual_error_normalized_scalar_identity reflected second firstLabel secondLabel Z Mrow amp
    (frequencyLoss Z 32 ξ) reserve error εcommon (volume s) (volume chain.extracted) lf weight
    P p i (zero_lt_one.trans hZ)

end Selected

section ScalarFamily
variable {Label : Type*}[Fintype Label]
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1 < Z) (bin : ℤ×(Fin 5→ℤ))
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
    (hυ : υ.modulus.absNorm ≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
      fixedBadMask p (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)

variable (index : Label→GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v)
variable (hne : ∀n : Label,(geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ (index n)).block.value ballProfile≠0)

/-- All second labels share the extracted source and prime denominator;
the common allocation remains fixed before both ray and residual sums. -/
theorem actual_geometry_error_column_scalar_sum
    (second : Bool)(P : Finset (Ideal O))(weight lf error εcommon : ℝ) :
    (∑n : Label,geometryErrorColumnScalar reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
      hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁ P weight lf error εcommon)=
    ((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf)*
      ∑n : Label,extractedErrorLabelScalar reflected second
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
        (geometryErrorSupportedSecondLabel reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ (index n) (hne n))
        Z Mrow amp (frequencyLoss Z 32 ξ) reserve error εcommon
        (volume s) (volume (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)) p (errorIndex i+1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact actual_geometry_error_column_scalar_identity reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
    hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁ P weight lf error εcommon

end ScalarFamily

section ScalarDisintegration
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1 < Z) (bin : ℤ×(Fin 5→ℤ))
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
    (hυ : υ.modulus.absNorm ≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
      fixedBadMask p (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)

set_option linter.defProp false in
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
    (second : Bool)(P : Finset (Ideal O))(weight lf error εcommon : ℝ)
    (hweight : 0 ≤ weight)(hlf : 0 < lf) :=
  let source := geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v
  let R₂ := (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1)
  let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i
  let Tsec := geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i
  let firstLabel := geometryFirstLabel s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
  let hU : ∀n∈rows,n.2.1∈inactiveSubsets n.1.val.val.1 n.1.val.val.2 :=
    fun n hn=>second_block_nonzero_inactive
      (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block
      ballProfile (hne n hn)
  let cost := fun l=>extractedErrorLabelScalar reflected second firstLabel l Z Mrow amp
    (frequencyLoss Z 32 ξ) reserve error εcommon (volume s) (volume source) p (errorIndex i+1)
  let hseed := actual_first_live_squarefree
    (geometryFirstSource s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (fun _=>logAnnulus) q.1.val q.1.property
  let hz₁ : source.W₁ 0=0 := hw₁
  let hz₂ : source.W₂ 0=0 := hw₂
  let hcost : ∀l∈actualSecondLabels source R₂ q.1.val.2.1.val,∀n∈box,0 ≤ cost l := by
    intro l hl _ _
    have hg := actual_second_labels_gates source R₂ q.1.val.2.1.val hseed hz₁ hz₂ l hl
    have hn := (normalizer_pos l.1.1 l.1.2 hg.1 l.2.val).le
    have hV := (volume_pos source).le
    have hrad : 0 ≤ firstErrorTailRadius reflected firstLabel Z Mrow (volume s) amp
        (frequencyLoss Z 32 ξ) reserve p (errorIndex i+1) := by
      unfold firstErrorTailRadius errorCommonRadius
      exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _
    dsimp only [cost]
    unfold extractedErrorLabelScalar
    positivity
  let hpaid := actual_second_positive_disintegration source R₂ q.1.val.2.1.val K Tsec Z ξ
    rows hU box hbox (fun l _=>cost l) hcost
  let hpaid' :
      (∑n : rows,cost (geometryErrorSupportedSecondLabel reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val (hne n.val n.property))) ≤ 
      (box.card:ℝ)*∑l∈actualSecondLabels source R₂ q.1.val.2.1.val,cost l := by
    have hlabel (n : rows) :
        actualSecondSupportedLabel source R₂ q.1.val.2.1.val K Tsec Z ξ n.val (hU n.val n.property)=
        geometryErrorSupportedSecondLabel reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val (hne n.val n.property) := rfl
    simpa only [hlabel,Finset.sum_const,nsmul_eq_mul] using hpaid
  let hsum := actual_geometry_error_column_scalar_sum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
    hw₁ hw₂ hp hcop ψ hυ hf₁ (fun n : rows=>n.val) (fun n=>hne n.val n.property) second P weight lf error εcommon
  let hfactor : 0 ≤ ((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf) := by positivity
  hsum.le.trans (mul_le_mul_of_nonneg_left hpaid' hfactor)

end ScalarDisintegration


private theorem error_box_factor_payment (factor card cap total : ℝ)
    (hf : 0 ≤ factor)(ht : 0 ≤ total)(hc : card ≤ cap) :
    factor*(card*total) ≤ cap*(factor*total) := by
  have h:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc ht) hf
  exact h.trans_eq (mul_left_comm _ _ _)

def geometryErrorScalarSubpowerConstant
    (Ncap : ℕ)(B loss b bs ξ ε : ℝ)
    (hB : 0 ≤ B)(hloss : 0 < loss)(hb : 1 ≤ b)(hbs : 1 ≤ bs)
    (hξ : ξ ≤ loss)(hε : 0 < ε) : ℝ :=
  Classical.choose (eventual_actual_geometry_error_absolute_box Ncap B loss b bs ξ ε
    hB hloss hb hbs hξ hε)

set_option linter.defProp false in
/-- Fixed source caps pay the complete second-label disintegration before
the first column, extraction menu or either height is chosen. -/
def eventual_actual_geometry_error_scalar_subpower
    (Ncap : ℕ)(B loss b bs ξ ε : ℝ)
    (hB : 0 ≤ B)(hloss : 0 < loss)(hb : 1 ≤ b)(hbs : 1 ≤ bs)
    (hξ : ξ ≤ loss)(hε : 0 < ε) :=
  let data:=eventual_actual_geometry_error_absolute_box Ncap B loss b bs ξ ε
    hB hloss hb hbs hξ hε
  let hdata:=Classical.choose_spec data
  And.intro hdata.1 (hdata.2.mono fun Z hz=>And.intro hz.1 (
    fun {α : Type} [Fintype α] [DecidableEq α] (reflected : Bool)(s : Input α)(R seed : Ideal O)
      (M amp reserve t : ℝ)(hZ : 1 < Z)
      (hN : Fintype.card α ≤ Ncap)(hend : Endpoints b bs bs s)(hseed : Squarefree seed)
      (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
      (hsource : sourceRadius s ≤ Z^B)(hA : |Real.logb Z (volume s)| ≤ B)
      (hM : |M| ≤ B)(ha : |amp| ≤ B)(hω : |frequencyLoss Z 32 ξ+reserve| ≤ B)
      (bin : ℤ×(Fin 5→ℤ))
      (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
      (hf₁ : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)
      (p : O)(hp : p≠0)(i : Fin 3)
      (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→
        IsCoprime (Ideal.span {p}) I)=>
    let firstChild:=geometryLowFirstChild reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q
    fun (Bp : actualAllocations (activeInput firstChild).pools ((Ideal.span {p})^(errorIndex i+1)))
      (υ : Character)(v : ℝ)(ψ : RayCharacter)
      (hυ : υ.modulus.absNorm ≤ radicalBound
        (childCharacter (geometryColumnCharacter reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
        fixedBadMask p (errorMovingExponent (errorIndex i)))
      (rows : Finset (GeometryErrorSecondIndex reflected s R seed Z M amp ξ reserve b t
        (Fintype.card α) hZ bin q p i Bp υ v))
      (hne : ∀n∈rows,(geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t
        (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ n).block.value ballProfile≠0)
      (second : Bool)(P : Finset (Ideal O))(weight lf error εcommon : ℝ)
      (hweight : 0 ≤ weight)(hlf : 0 < lf)=>
    let source:=geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v
    let R₂:=(R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1)
    let first:=geometryFirstLabel s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
    let hc:=hz.2.2 reflected s R seed M amp reserve t hZ hN hend hseed hw₁ hw₂
      hsource hA hM ha hω bin q hf₁ p hp i hcop Bp υ v
    let hbox : ∀n∈rows,actualSecondDyad source R₂ q.1.val.2.1.val
        (geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ bin q p i)
        (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b (Fintype.card α) hZ bin q p i)
        Z ξ n∈geometryErrorAbsoluteBox Z Ncap B loss b := fun n _=>hc.2.2.2.2 n
    let hpaid:=actual_geometry_error_scalar_disintegration reflected s R seed Z M amp ξ reserve b t
      (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ hp hcop ψ hυ hf₁ rows hne
      (geometryErrorAbsoluteBox Z Ncap B loss b) hbox second P weight lf error εcommon hweight hlf
    let hseed₁:=actual_first_live_squarefree
      (geometryFirstSource s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
      (fun _=>logAnnulus) q.1.val q.1.property
    let hsum : 0 ≤ ∑l∈actualSecondLabels source R₂ q.1.val.2.1.val,
        extractedErrorLabelScalar reflected second first l Z M amp (frequencyLoss Z 32 ξ)
          reserve error εcommon (volume s) (volume source) p (errorIndex i+1) := by
      apply Finset.sum_nonneg
      intro l hl
      have hg:=actual_second_labels_gates source R₂ q.1.val.2.1.val hseed₁ hw₁ hw₂ l hl
      have hn:=(normalizer_pos l.1.1 l.1.2 hg.1 l.2.val).le
      have hV:=(volume_pos source).le
      have hrad : 0 ≤ firstErrorTailRadius reflected first Z M (volume s) amp
          (frequencyLoss Z 32 ξ) reserve p (errorIndex i+1) := by
        unfold firstErrorTailRadius errorCommonRadius
        exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _
      unfold extractedErrorLabelScalar
      exact mul_nonneg
        (mul_nonneg (div_nonneg hrad hV)
          (mul_nonneg hn (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    let hf : 0 ≤ ((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf) :=
      div_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) hweight)
            (by norm_num))
          (add_nonneg (Nat.cast_nonneg _) (by norm_num))) hlf.le
    hpaid.trans (error_box_factor_payment
      ((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf)
      ((geometryErrorAbsoluteBox Z Ncap B loss b).card:ℝ) _ _ hf hsum hz.2.1)
  ))


end
end OAI.SevenEighths.Target836ErrorPayment
#print axioms OAI.SevenEighths.Target836ErrorPayment.actual_geometry_error_column_scalar_identity
#print axioms OAI.SevenEighths.Target836ErrorPayment.actual_geometry_error_column_scalar_sum
#print axioms OAI.SevenEighths.Target836ErrorPayment.actual_geometry_error_scalar_disintegration
#print axioms OAI.SevenEighths.Target836ErrorPayment.eventual_actual_geometry_error_scalar_subpower

#print axioms OAI.SevenEighths.Target836ErrorPayment.geometryErrorScalarSubpowerConstant
