import Candidate.Uneven.AuxiliaryHighParameters
import Candidate.Uneven.AuxiliaryAffineLowPayment
import Candidate.Target830.High.BalancedMass
import Candidate.Uneven.AuxiliaryCellGeometry
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighFinalPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineFinalSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryMainCompletePartition
import Candidate.Cycle63.Physical.InitialMass.GeometryCoarseSupport
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighNormalizedPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineHighSelectedTransport
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineHighSelectedFiber
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainLowPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Candidate.Uneven.AuxiliaryAffineMainLowPayment
import Candidate.Uneven.AuxiliaryHighFinalPayment

/- Original module: Candidate.Uneven.AuxiliaryHighAffineBase. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Actual HIGH transport adapted from Hailey Collet and accepted PR60; Apache-2.0.
Private .874836 proof components. No completed endpoint is asserted. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.AuxiliaryHigh
open TargetHigh830 SaturatedPlain
open OAI.SevenEighths.Target830
open OAI.SevenEighths.AuxiliaryPhysical
open Marked830Plain
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass

open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
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
local instance geometryAffineHighPaymentSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := geometryMainCoarseFamilySumDecidable

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

open CenteredMomentCommonPairedSource CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow FourierBridge

open CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
open CenteredMomentSecondInputCapacitySource


open Cycle63FinalNatural CenteredMomentSourceRow CenteredMomentSecondEnergySplit
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)



/-- The shared rate uses the ambient budget; Fourier data retain the actual count. -/
def geometryAffineHighDictionaryRate (μ : ℝ) (Nbudget : ℕ) : ℝ :=
  geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((Nbudget:ℝ)+2)) Nbudget

def geometryAffineHighTarget (μ δ : ℝ) : ℝ :=
  -(auxiliaryHighReserve:ℝ)+4*μ-3*δ

def geometryAffineHighCoarseExponent (μ δ : ℝ) (N : ℕ) : ℝ :=
  130+(39*(130+μ/8)+(130+μ/8)*δ+(130+μ/8)*δ+μ/8)+
    8*(130+μ/8)+3*(μ/8)+((N:ℝ)+2)*1+2*δ+3*(((N:ℝ)+2)*3)*δ+130



open Cycle63InitialSource CenteredMomentCommonRawScale QuadraticInitialBound CenteredMomentEnergyBands
variable {α : Type} [Fintype α] [DecidableEq α]

set_option linter.unusedVariables false in
set_option linter.defProp false in
def GeometryAffineHighSelectedCostSpec 
    (W : ℝ→ℂ)(hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (P : HighSourceParameters)(μ δ target : ℝ)(range : ℝ→ℝ→ℝ→ℝ→ℝ→Prop)(ηseed : Character)(Cs : ℝ)
    (Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)
    (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})(Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(s : Input α)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs Z)
    (θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W 2 Z)(hsη : s.η=ηseed)
    (height mesh : ℝ)(hw : ∀j,0≤ w j)
    (hwL : ∀j,w j≤ Cycle25.Energy.commonMesh 2 28 1 (μ/8))
    (hwr : ∀j,w j/31≤1)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
    (hwmarked : ∀j,w j≤ fineRawMesh*fineRawCore)
    (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0≤ height)(hfreq : ∀j,|freq j|≤ height)(hT : 2< Z^P.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hzslot : (1/50:ℝ)≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤7/250)
    (haff : length Z s.X₁+length Z s.X₂+Sil.Uneven.AuxiliarySource.lambda*(∑j,Real.logb Z (s.P j))≤
      Sil.Uneven.AuxiliarySource.B)
    (hvolumeCell : Real.logb Z (volume s)≤ Sil.Uneven.AuxiliarySource.total
      (Sil.Uneven.AuxiliarySource.widthCellUpper (∑j,Real.logb Z (s.P j))))
    {Label : Type}[Fintype Label]
    (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
    let first:=fun l=> geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let amp:=(1:ℝ)*Sil.Uneven.AuxiliarySource.amp (Sil.Uneven.AuxiliarySource.widthCellUpper ((∑j,Real.logb Z (s.P j))/(1:ℝ)))
    let omega:=frequencyLoss Z 32 (μ/64)+μ/8
    ∀(hamp0 : 0≤ amp)(hamp : |amp|≤4)(homega : |omega|≤4)
      (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
        1 s.ν s.W s.P≠0)
      (hinj : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val))),
    let rows:=mainLowSelectedNonzeroRows reflected s 1 1 Z 1 amp (μ/64) (μ/8)
      (9/4) t (Fintype.card α) hZ bin caps.zero₁ caps.zero₂ firstIndex
    let datum : rows→SecondInputDatum α:=fun r=> geometryLowSecondDatum reflected s 1 1 Z 1 amp
      (μ/64) (μ/8) (9/4) t (Fintype.card α) hZ bin (firstIndex r.val.1)
      caps.zero₁ caps.zero₂ r.val.2
    ∀(χ₀ : RayFourExpansion.RayCharacter)(m : O)(hm₀ : m≠0)
      (hml : goodLambda∣m)(hm₂ : (2:O)∣m)(Ψ : 𝓢(ℝ,ℂ))(t₀ u : ℝ),
    range Z t height t₀ u →
    ∀hP : ∀r,(datum r).R*(if second then (datum r).D else (datum r).C)≠0,
    ∀hPN : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤ Z^(28:ℝ),
    let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
      AuxiliaryPhysical.mainLowCanonicalSelector M H hH (datum r) χ₀ χ ψ (internalQ Q η₀) hQ72
        m hm₀ hml hm₂ Z 28 hZ second (hP r) (hPN r) η₀
        (inf_le_left.trans hQM) inf_le_right P.e (Z^P.τ) P.he hT hbeta hβhi
    let firstMass:=fun l=> balancedFirstHighMass reflected s 1 1 Ψ 1 Z (μ/64) δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let childSrc:=fun l=> geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
    let ordinary:=fun r=> ordinarySecondDatum (datum r) χ₀ (internalQ Q η₀) m
    let coefficient:=fun r=> firstMass r.val.1/volume (childSrc r.val.1)
    let select:=mainPhysicalFamilySelector second ordinary canonical
    (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(ordinary l).block)=>
        (1+Sil.Uneven.AuxiliarySource.q)/2≤ bufferValue P.e (select r)),
      (coefficient r.val.1*((ordinary r.val.1).K/lowerFactor (Fintype.card α) 1 (1/4))*
        normalizer (ordinary r.val.1).C (ordinary r.val.1).D (ordinary r.val.1).inactive)*
      highNormalizedRowCost second ordinary r
        ((ordinary r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((ordinary r.val.1).block.divisors.filter Squarefree))≤
      Kall*(p.control Sp)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
        Z^(amp+target)*
        (1+|t|+height)^degreeAll*(1+|t₀|)^degreeAll*(1+|u|)^degreeAll



/-- Field identities for the literal affine schedule; bΦ remains a supplied
radial cap, enlarged only enough to include the retained profile. -/
structure GeometryAffineHighScheduleGates (W : ℝ→ℂ) (μ δ : ℝ)
    (P : HighSourceParameters) : Prop where
  slot : P.Wslot=W
  slotCap : P.B₀=2
  degree : P.d=31
  plain : P.Rplain=1
  width : P.Rwidth=1
  retainedWidth : P.Mcap=2
  mask : P.Bmask=28
  radial : 2≤ P.bΦ
  slotRate : P.εslot=δ
  plainRate : P.εplain=geometryFinalPlainRate μ 31
  sigmaLo : P.σmin=33/50
  sigmaHi : P.σmax=33/50





/-- The exact selected ordinary fiber receipt, exposed until its independent
transport module completes whole-file checking. Fourier data use card α. -/
def GeometryAffineHighSelectedFiberReceipt
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    {α : Type} [Fintype α] [DecidableEq α]
    (b bs ε Amax Mmax ξ : ℝ) : Prop :=
    ∃Cfiber : ℝ,0< Cfiber ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(D amp reserve t : ℝ),
      Squarefree seed → Endpoints b bs bs s →
      volume s≤ Z^Amax → Z^D≤ Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ amp → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^D) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin),
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^D) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin (firstIndex l).1.val)
        R s.ν s.W s.P≠0) →
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^D) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin (firstIndex l).1.val,
        (firstIndex l).1.val.2.1.val)) →
      let Selected:=mainLowSelectedNonzeroRows reflected s R seed Z D amp ξ reserve b t
        (Fintype.card α) hZ bin hs₁ hs₂ firstIndex
      let datum:=mainLowSelectedDatum reflected s R seed Z D amp ξ reserve b t
        (Fintype.card α) hZ bin hs₁ hs₂ firstIndex
      let first:=fun q : Selected=> geometryFirstLabel s R seed (Z^D) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin (firstIndex q.val.1).1.val
      let left:=!reflected
      let unit:=fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      ∀(χ₀ : RayCharacter)(Q : Ideal O)(m : O),
      let ordinary:=fun q=> ordinarySecondDatum (datum q) χ₀ Q m
      ∀(labels : Finset (secondLiveRows (fun q=>(ordinary q).block)))(second : Bool)
        (hf : ∀r : secondLiveRows (fun q=>(ordinary q).block),
          jointFirstFrequency left u₀ unit (secondEncodedRow (fun q=>(ordinary q).block) first r)≠0),
      ∀target : NonzeroJointSourceLabel left u₀ unit,
      ((Finset.univ.filter (fun r : labels=>
        (if second then reflectedNonzeroJointLabel
          (secondEncodedNonzeroRow (fun q=>(ordinary q).block) first r.val left u₀ unit (hf r.val))
        else secondEncodedNonzeroRow (fun q=>(ordinary q).block) first r.val left u₀ unit (hf r.val))=target)).card:ℝ)≤
          Cfiber*Z^(2*ε)

/-- Replace only the puncture-bound proof; all physical fields are literal. -/
def reboundAffineHighState {Z Bmask Bmask' bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (hbound : (st.puncture.absNorm:ℝ)≤ Z^Bmask') : NaturalState Z Bmask' bΦ :=
  {st with puncture_bound:=hbound}

end
end OAI.SevenEighths.AuxiliaryHigh
end

/- Original module: Candidate.Uneven.AuxiliaryHighAffinePayment. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Actual HIGH transport adapted from Hailey Collet and accepted PR60; Apache-2.0.
Private .874836 proof components. No completed endpoint is asserted. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.AuxiliaryHigh
open TargetHigh830 SaturatedPlain
open OAI.SevenEighths.Target830
open OAI.SevenEighths.AuxiliaryPhysical
open Marked830Plain
noncomputable section
open OAI.SevenEighths.Cycle63InitialMass

open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
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
local instance geometryAffineHighConsumerSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := geometryMainCoarseFamilySumDecidable

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

open CenteredMomentCommonPairedSource CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow FourierBridge

open CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
open CenteredMomentSecondInputCapacitySource


open Cycle63FinalNatural CenteredMomentSourceRow CenteredMomentSecondEnergySplit
open CenteredMomentSecondHeightFamily Cycle63Moment.LowBranch

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)




open Cycle63InitialSource CenteredMomentCommonRawScale QuadraticInitialBound CenteredMomentEnergyBands
variable {α : Type} [Fintype α] [DecidableEq α]

set_option maxHeartbeats 1200000 in


attribute [local irreducible] SecondInputDatum.block
set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
set_option linter.defProp false in
/-- The literal affine-input high receipt has no source-cap, Matches,
volume-cell, or amplifier premise. The selected cost and selector are exact. -/
def GeometryAffineMainHighSpec 
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)(P : HighSourceParameters)(μ δ target : ℝ)
    (ηseed : Character)(Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)
    (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})(Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(tplain X₁ X₂ : ℝ)(hX₁ : 0< X₁)(hX₂ : 0< X₂)
    (height mesh : ℝ)(hw : ∀i,0≤ w i)(hmesh : 0≤ mesh)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (μ/8))(hwm : ∀i,w i≤ mesh)
    (hwmarked : ∀i,w i≤ fineRawMesh*fineRawCore)
    (hheight : 0≤ height)(hfreq : ∀i,|freq i|≤ height)(hT : 2< Z^P.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hlo₁ : (81/200:ℝ)≤ length Z X₁)(hlo₂ : (81/200:ℝ)≤ length Z X₂)
    (hhi₁ : length Z X₁≤(45/100:ℝ))(hhi₂ : length Z X₂≤(45/100:ℝ))
    (hslots : (1/50:ℝ)≤∑i,w i ∧ (∑i,w i)≤7/250)
    (hcone : length Z X₁+length Z X₂+Sil.Uneven.AuxiliarySource.lambda*(∑i,w i)≤ Sil.Uneven.AuxiliarySource.B),
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=AuxiliaryPhysical.affine_main_low_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=AuxiliaryPhysical.affine_main_low_profile_zero p 1
    ∀{Label : Type}[Fintype Label]
    (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
    let first:=fun l=> geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let amp:=(1:ℝ)*Sil.Uneven.AuxiliarySource.amp (Sil.Uneven.AuxiliarySource.widthCellUpper ((∑j,Real.logb Z (s.P j))/(1:ℝ)))
    let omega:=frequencyLoss Z 32 (μ/64)+μ/8
    ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
        1 s.ν s.W s.P≠0)
      (hinj : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val))),
    let rows:=mainLowSelectedNonzeroRows reflected s 1 1 Z 1 amp (μ/64) (μ/8)
      (9/4) t (Fintype.card α) hZ bin hz₁ hz₂ firstIndex
    let datum : rows→SecondInputDatum α:=fun r=> geometryLowSecondDatum reflected s 1 1 Z 1 amp
      (μ/64) (μ/8) (9/4) t (Fintype.card α) hZ bin (firstIndex r.val.1)
      hz₁ hz₂ r.val.2
    ∀(χ₀ : RayFourExpansion.RayCharacter)(m : O)(hm₀ : m≠0)
      (hml : goodLambda∣m)(hm₂ : (2:O)∣m)(Ψ : 𝓢(ℝ,ℂ))(t₀ u : ℝ),
    ∀hP : ∀r,(datum r).R*(if second then (datum r).D else (datum r).C)≠0,
    ∀hPN : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤ Z^(28:ℝ),
    let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
      AuxiliaryPhysical.mainLowCanonicalSelector M H hH (datum r) χ₀ χ ψ (internalQ Q η₀) hQ72
        m hm₀ hml hm₂ Z 28 hZ second (hP r) (hPN r) η₀
        (inf_le_left.trans hQM) inf_le_right P.e (Z^P.τ) P.he hT hbeta hβhi
    let firstMass:=fun l=> balancedFirstHighMass reflected s 1 1 Ψ 1 Z (μ/64) δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let childSrc:=fun l=> geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
    let ordinary:=fun r=> ordinarySecondDatum (datum r) χ₀ (internalQ Q η₀) m
    let coefficient:=fun r=> firstMass r.val.1/volume (childSrc r.val.1)
    let select:=mainPhysicalFamilySelector second ordinary canonical
    (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(ordinary l).block)=>
        (1+Sil.Uneven.AuxiliarySource.q)/2≤ bufferValue P.e (select r)),
      (coefficient r.val.1*((ordinary r.val.1).K/lowerFactor (Fintype.card α) 1 (1/4))*
        normalizer (ordinary r.val.1).C (ordinary r.val.1).D (ordinary r.val.1).inactive)*
      highNormalizedRowCost second ordinary r
        ((ordinary r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((ordinary r.val.1).block.divisors.filter Squarefree))≤
      Kall*(p.control Sp)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
        Z^(amp+target)*
        (1+|t|+height)^degreeAll*(1+|t₀|)^degreeAll*(1+|u|)^degreeAll






end
end OAI.SevenEighths.AuxiliaryHigh
end
