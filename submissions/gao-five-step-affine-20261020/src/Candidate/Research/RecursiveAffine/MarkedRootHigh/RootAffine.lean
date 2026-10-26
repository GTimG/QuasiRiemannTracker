/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.MarkedRootHigh.MainFinal
import Candidate.Research.RecursiveAffine.MarkedRootHigh.BindingLemmas
import Candidate.Research.RecursiveAffine.MarkedRootHigh.RootSourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineFinalSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryMainCompletePartition
import Candidate.Cycle63.Physical.InitialMass.GeometryCoarseSupport
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighNormalizedPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineHighSelectedTransport
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineHighSelectedFiber
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainLowPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Candidate.Cycle63.Arithmetic.Constants
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RootHigh
open Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
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
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable [L : Cycle63.AffineLedger] [Cycle153.MarkedRootPrice.RootLedgerBinding L]

/-- The shared rate uses the ambient budget; Fourier data retain the actual count. -/
def geometryAffineHighDictionaryRate (μ : ℝ) (Nbudget : ℕ) : ℝ :=
  geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((Nbudget:ℝ)+2)) Nbudget

def geometryAffineHighTarget (μ δ : ℝ) : ℝ :=
  -(Cycle153.MarkedRootPrice.lowReserve:ℝ)+4*μ-3*δ

def geometryAffineHighCoarseExponent (μ δ : ℝ) (N : ℕ) : ℝ :=
  130+(39*(130+μ/8)+(130+μ/8)*δ+(130+μ/8)*δ+μ/8)+
    8*(130+μ/8)+3*(μ/8)+((N:ℝ)+2)*1+2*δ+3*(((N:ℝ)+2)*3)*δ+130

/-- The actual slot count pays the same ambient raw-error budget. -/
theorem geometry_affine_high_actual_raw_budget (μ : ℝ) (N Nbudget : ℕ)
    (hμ : 0<μ) (hN : N≤Nbudget) :
    let δ:=geometryAffineHighDictionaryRate μ Nbudget
    δ+2*geometryFinalPlainRate μ 31*31+2*δ*31*(N:ℝ)≤μ/4 := by
  intro δ
  have hb:=geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((Nbudget:ℝ)+2)) Nbudget
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hactual : (N:ℝ)≤Nbudget := by exact_mod_cast hN
  have hslots:=mul_le_mul_of_nonneg_left hactual (show 0≤2*δ*31 by
    have hd : 0<δ:=hb.1
    positivity)
  have hδ : δ≤μ/128:=hb.2.2.1
  have hplain:=hb.2.2.2.2.2.2.2.1
  have hraw:=hb.2.2.2.2.2.2.2.2
  change μ/16+2*31*geometryFinalPlainRate μ 31+2*31*(Nbudget:ℝ)*δ≤μ/4 at hraw
  nlinarith only [hslots,hδ,hraw,hμ]

open Cycle63InitialSource CenteredMomentCommonRawScale QuadraticInitialBound CenteredMomentEnergyBands
variable {α : Type} [Fintype α] [DecidableEq α]

set_option linter.unusedVariables false in
set_option linter.defProp false in
def GeometryAffineHighSelectedCostSpec
    (W : ℝ→ℂ)(hbeta : 51/100≤HeckeZeroSupremum.beta)
    (P : HighSourceParameters)(μ δ target : ℝ)(range : ℝ→ℝ→ℝ→ℝ→ℝ→Prop)(ηseed : Character)(Cs : ℝ)
    (Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})(Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input α)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs Z)
    (θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hm : Matches M H hH s η₀ θ w σ freq W 2 Z)(hsη : s.η=ηseed)
    (height mesh : ℝ)(hw : ∀j,0≤w j)
    (hwL : ∀j,w j≤Cycle25.Energy.commonMesh 2 28 1 (μ/8))
    (hwr : ∀j,w j/31≤1)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
    (hwmarked : ∀j,w j≤ markedRawMesh*markedCoreMin)
    (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)(hT : 2<Z^P.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hzslot : Cycle63.Optimization.slotFloor≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤Cycle153.MarkedRootPrice.top)
    (haff : length Z s.X₁+length Z s.X₂+Cycle153.MarkedRootPrice.lambda*(∑j,Real.logb Z (s.P j))≤
      Cycle153.MarkedRootPrice.B)
    (hvolumeCell : Real.logb Z (volume s)≤Cycle153.MarkedRootPrice.totalA
      (Cycle153.MarkedRootPrice.cellUpper (Cycle153.MarkedRootPrice.originalCell (∑j,Real.logb Z (s.P j)))))
    {Label : Type}[Fintype Label]
    (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
    let first:=fun l=>geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let amp:=(1:ℝ)*Cycle153.MarkedRootPrice.amp (Cycle153.MarkedRootPrice.cellUpper
      (Cycle153.MarkedRootPrice.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    let omega:=frequencyLoss Z 32 (μ/64)+μ/8
    ∀(hamp0 : 0≤amp)(hamp : |amp|≤4)(homega : |omega|≤4)
      (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
        1 s.ν s.W s.P≠0)
      (hinj : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val))),
    let rows:=mainLowSelectedNonzeroRows reflected s 1 1 Z 1 amp (μ/64) (μ/8)
      (9/4) t (Fintype.card α) hZ bin caps.zero₁ caps.zero₂ firstIndex
    let datum : rows→SecondInputDatum α:=fun r=>geometryLowSecondDatum reflected s 1 1 Z 1 amp
      (μ/64) (μ/8) (9/4) t (Fintype.card α) hZ bin (firstIndex r.val.1)
      caps.zero₁ caps.zero₂ r.val.2
    ∀(χ₀ : RayFourExpansion.RayCharacter)(m : O)(hm₀ : m≠0)
      (hml : goodLambda∣m)(hm₂ : (2:O)∣m)(Ψ : 𝓢(ℝ,ℂ))(t₀ u : ℝ),
    range Z t height t₀ u →
    ∀hP : ∀r,(datum r).R*(if second then (datum r).D else (datum r).C)≠0,
    ∀hPN : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤Z^(28:ℝ),
    let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
      mainLowCanonicalSelector M H hH (datum r) χ₀ χ ψ (internalQ Q η₀) hQ72
        m hm₀ hml hm₂ Z 28 hZ second (hP r) (hPN r) η₀
        (inf_le_left.trans hQM) inf_le_right P.e (Z^P.τ) P.he hT hbeta hβhi
    let firstMass:=fun l=>geometryFirstHighMass reflected s 1 1 Ψ 1 Z (μ/64) δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let childSrc:=fun l=>geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
    let ordinary:=fun r=>ordinarySecondDatum (datum r) χ₀ (internalQ Q η₀) m
    let coefficient:=fun r=>firstMass r.val.1/volume (childSrc r.val.1)
    let select:=mainPhysicalFamilySelector second ordinary canonical
    (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(ordinary l).block)=>
        ((1+Cycle153.MarkedRootPrice.q)/2)≤bufferValue P.e (select r)),
      (coefficient r.val.1*((ordinary r.val.1).K/lowerFactor (Fintype.card α) 1 (1/4))*
        normalizer (ordinary r.val.1).C (ordinary r.val.1).D (ordinary r.val.1).inactive)*
      highNormalizedRowCost second ordinary r
        ((ordinary r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((ordinary r.val.1).block.divisors.filter Squarefree))≤
      Kall*(p.control Sp)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
        Z^(amp+target)*
        (1+|t|+height)^degreeAll*(1+|t₀|)^degreeAll*(1+|u|)^degreeAll

/-- Undo the exact physical amplifier after a bound on the amplified cost. -/
theorem geometry_affine_high_unamplify (Z amp exponent cost K : ℝ)
    (hZ : 0<Z) (h : Z^(-amp)*cost≤K*Z^exponent) :
    cost≤K*Z^(amp+exponent) := by
  calc
    cost=Z^amp*(Z^(-amp)*cost) := by
      rw [←mul_assoc,←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero,one_mul]
    _≤Z^amp*(K*Z^exponent) := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hZ.le _)
    _=K*Z^(amp+exponent) := by rw [Real.rpow_add hZ]; ring

/-- The physical coarse estimate on the literal selected high carrier. Its
exponent is coarse and contains no high saving. -/
theorem actual_affine_high_selected_coarse
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hbeta : 51/100≤HeckeZeroSupremum.beta)
    (P : HighSourceParameters)(μ δ Cs : ℝ)(ηseed : Character)
    (hμ : 0<μ)(_hμcap : μ≤1/128)(hδ : 0<δ)(hCs : 1≤Cs) :
    ∃K : ℝ,0<K ∧ ∀(Q : Ideal O)(hQM : Q≤M)
      (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}),∀ᶠZ : ℝ in atTop,
      2≤Z ∧ GeometryAffineHighSelectedCostSpec (α:=α) M H hH W hbeta P μ δ
        (geometryAffineHighCoarseExponent μ δ (Fintype.card α)) (fun _ _ _ _ _=>True) ηseed Cs {(0,0)} 0 K
        η₀ Q hQM hQ72 Z := by
  have hc:=actual_main_high_final_all_height_coarse (α:=α)
    η₀ u₀ F₀ R₀ hu₀ (Fintype.card α) rfl (bp:=9/4)
    130 (μ/8) δ δ Cs (9/4) (9/4) (Real.log 2) 1 1 (1/4) (μ/8) δ (μ/64) 3
    (by norm_num) (by positivity) hδ hδ hCs (by norm_num) (by norm_num)
    (Real.log_nonneg (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) hδ.le (by positivity) (by linarith) (by norm_num)
  obtain ⟨K,hK,hc⟩:=hc
  refine ⟨K,hK,?_⟩
  intro Q hQM hQ72
  filter_upwards [hc,eventually_ge_atTop (2:ℝ)] with Z hc hZ2
  refine ⟨hZ2,?_⟩
  unfold GeometryAffineHighSelectedCostSpec
  intro hZ s p caps θ w σ freq hm hsη height mesh hw hwL hwr hmesh hwm hwmarked hσ hheight hfreq hT hβhi
    hzslot haff hvolumeCell Label _ reflected second bin t firstIndex first amp omega hamp0 hamp homega hf₁ hinj
    rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u hRange hP hPN canonical firstMass childSrc ordinary coefficient select
  let hKfirst:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let highRows:=Finset.univ.filter (fun r : secondLiveRows (fun l=>(ordinary l).block)=>
    ((1+Cycle153.MarkedRootPrice.q)/2)≤bufferValue P.e (select r))
  have hb:=hc hZ (Label:=Label) reflected s 1 1 1 amp (μ/8) t hKfirst squarefree_one caps.endpoints
    (by rw [caps.lower])
    (caps.sourceCap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))
    (caps.volumeLog.trans (by norm_num)) (by norm_num) (hamp.trans (by norm_num))
    (homega.trans (by norm_num)) caps.controls caps.windows caps.plainScales caps.primeScales
    caps.poolCap caps.support₁ caps.support₂ caps.zero₁ caps.zero₂ hamp0 (by positivity)
    bin firstIndex hinj hf₁ (fun _=>χ₀) (fun _=>internalQ Q η₀) (fun _=>m)
    highRows second Ψ t₀ u p {(0,0)} (by simp) caps.profile₁ caps.profile₂
  change Z^(-amp)*(∑r∈highRows,∑L∈secondResidualIdeals (fun q=>(ordinary q).block) r.val,
    mainNormalizedPhysicalCost (Fintype.card α) 1 (1/4) second ordinary coefficient t₀ u r.val L)≤
    K*(p.control {(0,0)})^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
      Z^(geometryAffineHighCoarseExponent μ δ (Fintype.card α)) at hb
  rw [geometry_main_high_physical_row_sum (Fintype.card α) 1 (1/4) second ordinary coefficient t₀ u highRows] at hb
  have hh:=geometry_affine_high_unamplify Z amp (geometryAffineHighCoarseExponent μ δ (Fintype.card α))
    _ (K*(p.control {(0,0)})^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin) (zero_lt_one.trans hZ) hb
  simpa only [pow_zero,mul_one] using hh

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
  radial : 2≤P.bΦ
  slotRate : P.εslot=δ
  plainRate : P.εplain=geometryFinalPlainRate μ 31
  sigmaLo : P.σmin=33/50
  sigmaHi : P.σmax=33/50

theorem geometry_affine_high_schedule_gates
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (μ bΦ τ : ℝ)(Nbudget : ℕ)(bound : ℕ→ℝ)
    (hμ : 0<μ)(hbΦ : 2≤bΦ)(hτ : 0<τ)(hbound : ∀k,0≤bound k) :
    GeometryAffineHighScheduleGates W μ (geometryAffineHighDictionaryRate μ Nbudget)
      (geometryAffineFinalHighSchedule W hWs hW μ 130 (3*((Nbudget:ℝ)+2)) bΦ τ Nbudget bound
        hμ (by norm_num) (by positivity) (by linarith) hτ hbound) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,hbΦ,rfl,rfl,rfl,rfl⟩

/-- A larger physical profile-control set pays the same exact carrier. -/
theorem geometry_affine_high_selected_cost_mono
    (W : ℝ→ℂ)(hbeta : 51/100≤HeckeZeroSupremum.beta)
    (P : HighSourceParameters)(μ δ target : ℝ)(range : ℝ→ℝ→ℝ→ℝ→ℝ→Prop)
    (ηseed : Character)(Cs : ℝ)(S S₁ : Finset (ℕ×ℕ))(degree : ℕ)(K : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (Z : ℝ)(hK : 0≤K)(hS : S⊆S₁)
    (hspec : GeometryAffineHighSelectedCostSpec (α:=α) M H hH W hbeta P μ δ target range ηseed Cs
      S degree K η₀ Q hQM hQ72 Z) :
    GeometryAffineHighSelectedCostSpec (α:=α) M H hH W hbeta P μ δ target range ηseed Cs
      S₁ degree K η₀ Q hQM hQ72 Z := by
  unfold GeometryAffineHighSelectedCostSpec at hspec ⊢
  intro hZ s p caps θ w σ freq hm hsη height mesh hw hwL hwr hmesh hwm hwmarked hσ hheight hfreq hT hβhi
    hzslot haff hvolumeCell Label _ reflected second bin t firstIndex first amp omega hamp0 hamp homega hf₁ hinj
    rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u hRange hP hPN canonical firstMass childSrc ordinary coefficient select
  have hb:=hspec hZ s p caps θ w σ freq hm hsη height mesh hw hwL hwr hmesh hwm hwmarked hσ hheight hfreq hT hβhi
    hzslot haff hvolumeCell reflected second bin t firstIndex hamp0 hamp homega hf₁ hinj χ₀ m hm₀ hml hm₂
    Ψ t₀ u hRange hP hPN
  have hc:=CenteredMomentEnergyBandMonotonicity.profile_control_mono p hS
  have hp:=pow_le_pow_left₀ (Profiles.control_nonneg _ _) hc 2
  have hside : 0≤geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin :=
    (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos (Fintype.card α) 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  have hscalar : 0≤K*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
      Z^(amp+target)*(1+|t|+height)^degree*(1+|t₀|)^degree*(1+|u|)^degree := by positivity
  apply hb.trans
  calc
    _=(K*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
      Z^(amp+target)*(1+|t|+height)^degree*(1+|t₀|)^degree*(1+|u|)^degree)*(p.control S)^2 := by ring
    _≤(K*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
      Z^(amp+target)*(1+|t|+height)^degree*(1+|t₀|)^degree*(1+|u|)^degree)*(p.control S₁)^2 :=
      mul_le_mul_of_nonneg_left hp hscalar
    _=_ := by ring

/-- The same amplifier is applied to both height branches. -/
theorem geometry_affine_high_amplify (Z amp exponent cost K : ℝ)
    (hZ : 0<Z) (h : cost≤K*Z^(amp+exponent)) :
    Z^(-amp)*cost≤K*Z^exponent := by
  calc
    _≤Z^(-amp)*(K*Z^(amp+exponent)) := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hZ.le _)
    _=K*Z^exponent := by
      rw [Real.rpow_add hZ]
      calc
        _=K*(Z^(-amp)*Z^amp)*Z^exponent := by ring
        _=_ := by rw [←Real.rpow_add hZ,neg_add_cancel,Real.rpow_zero,mul_one]

/-- Splice the two checked selected-cost contracts at the actual combined
Mellin height, and keep the separate polynomial weights for both integrals. -/
theorem geometry_affine_high_selected_height_splice
    (W : ℝ→ℂ)(hbeta : 51/100≤HeckeZeroSupremum.beta)
    (P : HighSourceParameters)(μ δ target coarse : ℝ)(ηseed : Character)(Cs : ℝ)
    (Sp : Finset (ℕ×ℕ)) :
    ∃degree : ℕ,∀(Ks Kc : ℝ)(_hKs : 0≤Ks)(_hKc : 0≤Kc)
      (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
      (Z : ℝ),
      GeometryAffineHighSelectedCostSpec (α:=α) M H hH W hbeta P μ δ target
        (fun Z t height t₀ u=>|t|+height+2*Real.pi*(|u|+|t₀|)≤Z^P.τ) ηseed Cs Sp 0 Ks η₀ Q hQM hQ72 Z →
      GeometryAffineHighSelectedCostSpec (α:=α) M H hH W hbeta P μ δ coarse
        (fun _ _ _ _ _=>True) ηseed Cs Sp 0 Kc η₀ Q hQM hQ72 Z →
      GeometryAffineHighSelectedCostSpec (α:=α) M H hH W hbeta P μ δ target
        (fun _ _ _ _ _=>True) ηseed Cs Sp degree ((2+4*Real.pi)^degree*(Ks+Kc)) η₀ Q hQM hQ72 Z := by
  have hext:=geometry_extend_shifted_height_bound coarse target P.τ P.hτ 0
  obtain ⟨degree,hext⟩:=hext
  refine ⟨degree,?_⟩
  intro Ks Kc hKs hKc η₀ Q hQM hQ72 Z hs hc
  unfold GeometryAffineHighSelectedCostSpec at hs hc ⊢
  intro hZ s p caps θ w σ freq hm hsη height mesh hw hwL hwr hmesh hwm hwmarked hσ hheight hfreq hT hβhi
    hzslot haff hvolumeCell Label _ reflected second bin t firstIndex first amp omega hamp0 hamp homega hf₁ hinj
    rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u hRange hP hPN canonical firstMass childSrc ordinary coefficient select
  let cost:=∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(ordinary l).block)=>((1+Cycle153.MarkedRootPrice.q)/2)≤bufferValue P.e (select r)),
    (coefficient r.val.1*((ordinary r.val.1).K/lowerFactor (Fintype.card α) 1 (1/4))*
      normalizer (ordinary r.val.1).C (ordinary r.val.1).D (ordinary r.val.1).inactive)*
    highNormalizedRowCost second ordinary r
      ((ordinary r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
      ((ordinary r.val.1).block.divisors.filter Squarefree)
  let side:=geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin
  have hside : 0≤ side:=(geometry_high_factor_pos reflected _ bin
    (geometrySupportConstant_pos (Fintype.card α) 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  have hcoarse:=hc hZ s p caps θ w σ freq hm hsη height mesh hw hwL hwr hmesh hwm hwmarked hσ hheight hfreq hT hβhi
    hzslot haff hvolumeCell reflected second bin t firstIndex hamp0 hamp homega hf₁ hinj χ₀ m hm₀ hml hm₂
    Ψ t₀ u True.intro hP hPN
  change cost≤_ at hcoarse
  simp only [pow_zero,mul_one] at hcoarse
  have hcoarseAmp:=geometry_affine_high_amplify Z amp coarse cost (Kc*(p.control Sp)^2*side)
    (zero_lt_one.trans hZ) hcoarse
  have hsmall : 2*(1+|t|+height+2*Real.pi*(|t₀|+|u|))≤Z^P.τ →
      Z^(-amp)*cost≤Ks*((p.control Sp)^2*side)*Z^target*
        (2*(1+|t|+height+2*Real.pi*(|t₀|+|u|)))^0 := by
    intro hh
    have hcombined : |t|+height+2*Real.pi*(|u|+|t₀|)≤Z^P.τ := by
      have hsh : 0≤2*Real.pi*(|t₀|+|u|):=by positivity
      nlinarith [abs_nonneg t]
    have hb:=hs hZ s p caps θ w σ freq hm hsη height mesh hw hwL hwr hmesh hwm hwmarked hσ hheight hfreq hT hβhi
      hzslot haff hvolumeCell reflected second bin t firstIndex hamp0 hamp homega hf₁ hinj χ₀ m hm₀ hml hm₂
      Ψ t₀ u hcombined hP hPN
    change cost≤_ at hb
    simp only [pow_zero,mul_one] at hb
    have ha:=geometry_affine_high_amplify Z amp target cost (Ks*(p.control Sp)^2*side)
      (zero_lt_one.trans hZ) hb
    simpa only [pow_zero,mul_one,mul_assoc] using ha
  have ha:=hext Z t height t₀ u (Z^(-amp)*cost) Ks Kc ((p.control Sp)^2*side) hZ.le hheight hKs hKc
    (mul_nonneg (sq_nonneg _) hside) hsmall (by simpa only [mul_assoc] using hcoarseAmp)
  have hb:=geometry_affine_high_unamplify Z amp target cost
    ((2+4*Real.pi)^degree*(Ks+Kc)*((p.control Sp)^2*side)*
      (1+|t|+height)^degree*(1+|t₀|)^degree*(1+|u|)^degree)
    (zero_lt_one.trans hZ) (by convert ha using 1; ring)
  change cost≤_
  convert hb using 1; ring
/-- The exact selected ordinary fiber receipt, exposed until its independent
transport module completes whole-file checking. Fourier data use card α. -/
def GeometryAffineHighSelectedFiberReceipt
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    {α : Type} [Fintype α] [DecidableEq α]
    (b bs ε Amax Mmax ξ : ℝ) : Prop :=
    ∃Cfiber : ℝ,0<Cfiber ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(D amp reserve t : ℝ),
      Squarefree seed → Endpoints b bs bs s →
      volume s≤Z^Amax → Z^D≤Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤amp → 0≤ reserve →
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
      let first:=fun q : Selected=>geometryFirstLabel s R seed (Z^D) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) D) bin (firstIndex q.val.1).1.val
      let left:=!reflected
      let unit:=fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      ∀(χ₀ : RayCharacter)(Q : Ideal O)(m : O),
      let ordinary:=fun q=>ordinarySecondDatum (datum q) χ₀ Q m
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
    (hbound : (st.puncture.absNorm:ℝ)≤Z^Bmask') : NaturalState Z Bmask' bΦ :=
  {st with puncture_bound:=hbound}

/-- The second datum of a nonzero second-stage block of a parent at the first height `t`. -/
def affineHighBlockDatum (reflected : Bool) (s : Input α) (R seed : Ideal O) (Z Mrow amp μ t : ℝ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t (Fintype.card α) hZ bin hz₁ hz₂) :
    SecondInputDatum α :=
  geometryLowSecondDatum reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t (Fintype.card α) hZ bin j.val.1 hz₁ hz₂
    j.val.2

/-- The transport form of the HIGH rows of all nonzero second-stage blocks of a parent at the first height `t` on the
canonical selector: over the buffer bins `q`, the binned count of the keys of the HIGH rows in `q` at their compensated
coordinates, with the weight `Z^(U₀ + (2 bufferValue q - 1) U₃ + extra)` at the upper edges `U` of an exponent bin. -/
def affineHighUniversalTransport (η₀ : Character) (u₀ : O) (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) (hu₀ : u₀≠0)
    (reflected second : Bool) (s : Input α) (R seed : Ideal O) (Z Mrow amp μ t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (χ₀ : RayCharacter) (Q : Ideal O) (hQ72 : Q≤Ideal.span {(72:O)}) (m : O)
    (hm₀ : m≠0) (hml : goodLambda∣m) (hm₂ : (2:O)∣m) (hQM : Q≤M) (hQη : Q≤η₀.modulus) (e T : ℝ) (he : 0<e)
    (hT : 2<T) (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hP : ∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0)
    (hPN : ∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤Z^(28:ℝ))
    (qh extra : ℝ) : ℝ :=
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  let full:=affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂
  let ordinary:=fun j=>ordinarySecondDatum (full j) χ₀ Q m
  let first:=fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t (Fintype.card α) hZ
      bin hz₁ hz₂=>
    geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hK bin j.val.1.1.val
  let canonical:=fun j (χ ψ : RayCharacter)=>mainLowCanonicalSelector M H hH (full j) χ₀ χ ψ Q hQ72 m hm₀ hml hm₂
    Z 28 hZ second (hP j) (hPN j) η₀ hQM hQη e T he hT hβlo hβhi
  let select:=mainPhysicalFamilySelector second ordinary canonical
  let left:=!reflected
  let unit:=fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
  let hf:=fun r : secondLiveRows (fun j=>(ordinary j).block)=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀
    hu₀ s R seed (Z^Mrow) Z (μ/64) hK bin r.val.1.val.1.1.val ordinary first r rfl
  let rawKey:=fun r=>secondEncodedNonzeroRow (fun j=>(ordinary j).block) first r left u₀ unit (hf r)
  let key:=fun r=>if second then reflectedNonzeroJointLabel (rawKey r) else rawKey r
  let A:=Real.logb Z (volume s.toData)
  let x:=fun r : secondLiveRows (fun j=>(ordinary j).block)=>compensatedHighCoordinates
    (childHighCoordinates (actualHighCoordinates reflected left second (first r.val.1) (ordinary r.val.1).C
      (ordinary r.val.1).D (ordinary r.val.1).inactive Z Mrow A amp (μ/64) (μ/8) (μ/8)) (μ/8))
    (geometryHighSide reflected A (geometryExponents s R seed (Z^Mrow) Z (μ/64) r.val.1.val.1.1.val.1.val))
  let high:=Finset.univ.filter (fun r : secondLiveRows (fun j=>(ordinary j).block)=>
    ((1+qh)/2)≤bufferValue e (select r))
  ∑q : BufferIndex e,keyBinnedCount (high.filter (fun r=>select r=q)) key x (μ/32)
    (fun k=>Z^(exponentBinUpper (μ/32) k 0+(2*bufferValue e q-1)*exponentBinUpper (μ/32) k 3+extra))

/-- The transport form of the nonzero blocks is nonnegative. -/
theorem affineHighUniversalTransport_nonneg (η₀ : Character) (u₀ : O) (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O)
    (hu₀ : u₀≠0) (reflected second : Bool) (s : Input α) (R seed : Ideal O) (Z Mrow amp μ t : ℝ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (χ₀ : RayCharacter) (Q : Ideal O)
    (hQ72 : Q≤Ideal.span {(72:O)}) (m : O) (hm₀ : m≠0) (hml : goodLambda∣m) (hm₂ : (2:O)∣m) (hQM : Q≤M)
    (hQη : Q≤η₀.modulus) (e T : ℝ) (he : 0<e) (hT : 2<T) (hβlo : 51/100≤HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hP : ∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)≠0)
    (hPN : ∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).R*
      (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).D
        else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ j).C)).absNorm:ℝ))≤Z^(28:ℝ))
    (qh extra : ℝ) :
    0≤affineHighUniversalTransport M H hH η₀ u₀ F₀ R₀ hu₀ reflected second s R seed Z Mrow amp μ t hZ bin hz₁ hz₂ χ₀
      Q hQ72 m hm₀ hml hm₂ hQM hQη e T he hT hβlo hβhi hP hPN qh extra := by
  unfold affineHighUniversalTransport
  exact Finset.sum_nonneg fun q _ => keyBinnedCount_nonneg _ _ _ _ _
    (fun _ => Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

/-- Undo the physical amplifier of a bound on the amplified cost. -/
theorem geometry_affine_high_unamplify_bound (Z amp cost Y : ℝ) (hZ : 0<Z) (h : Z^(-amp)*cost≤Y) :
    cost≤Z^amp*Y := by
  calc cost=Z^amp*(Z^(-amp)*cost) := by
        rw [←mul_assoc,←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero,one_mul]
    _≤Z^amp*Y := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hZ.le _)

/-- The constants and the powers of `Z` of the transport form of the canonical HIGH shell, gathered in front of the
binned count of the keys with the powers of `Z` moved into the weights. -/
theorem affine_high_transport_constants {κ K : Type*} (S : Finset κ) (key : κ→K) (x : κ→Fin 4→ℝ) (width Z : ℝ)
    (hZ : 0<Z) (f : (Fin 4→ℤ)→ℝ) (lf Cf fl Km εp Lp ε Cs B εm side Cm Kc : ℝ) (n : ℕ) :
    (1/lf)*((Cf*Z^fl)*(Km*Z^εp*(2*Z^Lp)^ε*Cs^n*Z^(B*ε)*(side*Z^(B*εm)*
      keyBinnedCount S key x width (fun k=>Cm*Kc*(2*Z^Lp)^(2*ε)*Z^(f k))))) =
    ((1/lf)*Cf*Km*Cs^n*Cm*(2:ℝ)^ε*(2:ℝ)^(2*ε))*Kc*side*
      keyBinnedCount S key x width (fun k=>Z^(f k+(fl+εp+Lp*ε+B*ε+B*εm+Lp*(2*ε)))) := by
  rw [keyBinnedCount_const_mul, keyBinnedCount_rpow_shift S key x width Z _ hZ f]
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hZ.le Lp),
    Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hZ.le Lp), ←Real.rpow_mul hZ.le, ←Real.rpow_mul hZ.le]
  simp only [Real.rpow_add hZ]
  ring

set_option maxHeartbeats 200000 in
set_option linter.unusedVariables false in
/-- The canonical HIGH rows at small height of a parent with first-stage puncture `R`, seed `seed` and radial scale
`Z^Mrow`. Without payment data their selected cost is at most `Z^amp` times the transport form of the HIGH rows of all
nonzero blocks of the parent at the first height, which does not depend on the family of first columns or on the
Mellin heights; with the cell payment data it is the paid exponent. The density dictionary and degree precede the
moving source, detector and common cutoff. -/
theorem actual_affine_high_selected_small_height_shell
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (μ Cs ρ : ℝ)(Nbudget : ℕ)(hμ : 0<μ)(hμcap : μ≤Cycle63.Optimization.geometryLossCap)(hCs : 1≤Cs)
    (hρ : ρ≤20)(qh : ℝ)(hqh : Cycle153.MarkedRootPrice.q≤qh)(hN : Fintype.card α≤Nbudget)
    (fiberReceipt : GeometryAffineHighSelectedFiberReceipt (α:=α) η₀ u₀ F₀ R₀ (9/4) (9/4)
      (μ/8) 3 1 (μ/64)) (δ : ℝ) (hδdef : δ=geometryAffineHighDictionaryRate μ Nbudget) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      GeometryAffineHighScheduleGates W μ δ P →
      MarkedSchedule P (Fintype.card α) W (33/50) (33/50) →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain → 2*P.τ*(J+1)≤μ/8 →
      ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃K Kt : ℝ,0<K ∧ 0<Kt ∧
      ∀(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}),
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀(hZ : 1<Z)(s : Input α)(p : Profiles (1/4) (9/4))
        (caps : GeometryAffineLowSourceGates s p Cs Z)
        (θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
        (hm : Matches M H hH s η₀ θ w σ freq W 2 Z)
        (R seed : Ideal O)(Mrow : ℝ)(hR : R≠0)(hseed : Squarefree seed)(hRcap : (R.absNorm:ℝ)≤Z^ρ)
        (hMrow : 0≤Mrow)(hMrow1 : Mrow≤1)
        (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+μ/16)
        (height mesh : ℝ)(hw : ∀j,0≤w j)
        (hwL : ∀j,w j≤Cycle25.Energy.commonMesh 2 28 1 (μ/8))
        (hwr : ∀j,w j/31≤1)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
        (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
        (hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)(hT : 2<Z^P.τ)
        (hβhi : HeckeZeroSupremum.beta≤7/8)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t amp : ℝ)
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
      let first:=fun l=>geometryFirstLabel s R seed (Z^Mrow) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
      let omega:=frequencyLoss Z 32 (μ/64)+μ/8
      ∀(hamp0 : 0≤amp)(hamp : |amp|≤4)(homega : |omega|≤4)
        (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
          (geometryColumnIdeal reflected s R seed (Z^Mrow) Z (μ/64)
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
          R s.ν s.W s.P≠0)
        (hinj : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val))),
      let rows:=mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp (μ/64) (μ/8)
        (9/4) t (Fintype.card α) hZ bin caps.zero₁ caps.zero₂ firstIndex
      let datum : rows→SecondInputDatum α:=fun r=>geometryLowSecondDatum reflected s R seed Z Mrow amp
        (μ/64) (μ/8) (9/4) t (Fintype.card α) hZ bin (firstIndex r.val.1)
        caps.zero₁ caps.zero₂ r.val.2
      ∀(χ₀ : RayFourExpansion.RayCharacter)(m : O)(hm₀ : m≠0)
        (hml : goodLambda∣m)(hm₂ : (2:O)∣m)(Ψ : 𝓢(ℝ,ℂ))(t₀ u : ℝ),
      |t|+height+2*Real.pi*(|u|+|t₀|)≤Z^P.τ →
      ∀hP : ∀r,(datum r).R*(if second then (datum r).D else (datum r).C)≠0,
      ∀hPN : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤Z^(28:ℝ),
      let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
        mainLowCanonicalSelector M H hH (datum r) χ₀ χ ψ (internalQ Q η₀) hQ72
          m hm₀ hml hm₂ Z 28 hZ second (hP r) (hPN r) η₀
          (inf_le_left.trans hQM) inf_le_right P.e (Z^P.τ) P.he hT hbeta hβhi
      let firstMass:=fun l=>geometryFirstHighMass reflected s R seed Ψ Mrow Z (μ/64) δ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
      let childSrc:=fun l=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z (μ/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
      let ordinary:=fun r=>ordinarySecondDatum (datum r) χ₀ (internalQ Q η₀) m
      let coefficient:=fun r=>firstMass r.val.1/volume (childSrc r.val.1)
      let select:=mainPhysicalFamilySelector second ordinary canonical
      let side:=geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin
      ∃(hPU : ∀j,(affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ j).R*
          (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ j).D
            else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ j).C)≠0)
        (hPNU : ∀j,((((affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ j).R*
          (if second then (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ j).D
            else (affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ j).C)).absNorm:ℝ))
          ≤Z^(28:ℝ)),
      ∀pay : Option (FinalHighCellPayment η₀ u₀ F₀ R₀ Z s Mrow (μ/64) amp (μ/8) (μ/8) 130 w (μ/8) (μ/32)
        (μ/8) (μ/4) (μ/4) δ (μ/8) δ (3*((Nbudget:ℝ)+2)) δ (2*(μ/8)) μ (3*δ)),
      (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(ordinary l).block)=>
          ((1+qh)/2)≤bufferValue P.e (select r)),
        (coefficient r.val.1*((ordinary r.val.1).K/lowerFactor (Fintype.card α) 1 (1/4))*
          normalizer (ordinary r.val.1).C (ordinary r.val.1).D (ordinary r.val.1).inactive)*
        highNormalizedRowCost second ordinary r
          ((ordinary r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
          ((ordinary r.val.1).block.divisors.filter Squarefree))≤
        Z^amp*pay.elim
          (Kt*(p.control Sp)^2*side*affineHighUniversalTransport M H hH η₀ u₀ F₀ R₀ hu₀ reflected second s R seed
            Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ χ₀ (internalQ Q η₀) hQ72 m hm₀ hml hm₂
            (inf_le_left.trans hQM) inf_le_right P.e (Z^P.τ) P.he hT hbeta hβhi hPU hPNU qh
            (μ/4+μ/4+(2*(μ/8)+δ+3*((Nbudget:ℝ)+2)*δ+130*δ+130*δ+3*((Nbudget:ℝ)+2)*(2*δ))))
          (fun _=>K*(p.control Sp)^2*side*Z^(-Mrow*Cycle153.MarkedRootPrice.lowReserve+4*μ-3*δ)) := by
  have hμ1 : μ ≤ 1/1000 := hμcap.trans (by
    norm_num [Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight,
      Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice,
      Cycle63.Optimization.betaBound])
  have rates:=geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((Nbudget:ℝ)+2)) Nbudget
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hδ : 0<δ:=hδdef ▸ rates.1
  have hδsmall : δ≤μ/128:=hδdef ▸ rates.2.2.1
  have hraw : δ+2*geometryFinalPlainRate μ 31*31+2*δ*31*(Fintype.card α:ℝ)≤μ/4 :=
    hδdef ▸ geometry_affine_high_actual_raw_budget μ (Fintype.card α) Nbudget hμ hN
  have hL : 0≤3*((Nbudget:ℝ)+2):=by positivity
  have hUL : ((Fintype.card α:ℝ)+2)*3≤3*((Nbudget:ℝ)+2) := by
    have hn : (Fintype.card α:ℝ)≤Nbudget:=by exact_mod_cast hN
    linarith
  have hshell:=actual_main_high_small_height_shell (α:=α) (ap:=1/4) (bp:=9/4) M H hH
    η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper 130 130 (μ/8) δ μ (3*δ) (μ/32) (2*(μ/8))
    (by positivity) (by norm_num) (by norm_num) le_rfl (by norm_num) (by positivity) hδ (by norm_num)
    (Fintype.card α) 1 δ (μ/8) (μ/8) (by norm_num) hδ.le (by positivity) (by positivity)
    (3*((Nbudget:ℝ)+2)) δ 3 hL hδ (by norm_num) hUL
    Cs (9/4) (9/4) (Real.log 2) δ hCs (by norm_num) (by norm_num)
    (Real.log_nonneg (by norm_num)) hδ
  obtain ⟨bound,hbound,J,hsmall⟩:=hshell
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hsched hmarked hslot hplain hdensity
  have hsmallP:=hsmall (μ/8) P hboundeq hmarked hslot hplain (hdensity.trans (by linarith)) hdensity
  obtain ⟨F,G,Ks,Kmove,Cmove,hF,hKs,hKmove,hCmove,he⟩:=hsmallP
  let Sp:=G∪{(0,0)}
  let amplitude : ℝ := (2*(9/4)*Cs^(Fintype.card α))^2
  have hampPositive : 0<amplitude:=by dsimp only [amplitude]; positivity
  -- The selected fiber constant is independent of the moving detector.
  obtain ⟨Cf,hCf,hfiber⟩:=fiberReceipt
  have hlower : 0<lowerFactor (Fintype.card α) 1 (1/4):=lowerFactor_pos (Fintype.card α) 1 (1/4) one_pos
    (by norm_num)
  let Kt:=((1/lowerFactor (Fintype.card α) 1 (1/4))*Cf*Kmove*Cs^(2*Fintype.card α)*Cmove*(2:ℝ)^δ*
    (2:ℝ)^(2*δ))*amplitude
  have hKt : 0<Kt:=by dsimp only [Kt]; positivity
  refine ⟨Sp,by simp [Sp],Ks*Cf*amplitude,Kt,by positivity,hKt,?_⟩
  intro Q hQM hQ72
  filter_upwards [he,
    eventually_actual_main_high_canonical_admission (α:=α) M H hH
      (9/4) (9/4) (μ/8) (μ/64) (1/4) P.τ P.e 28 P.bΦ ρ
      (by norm_num) (by norm_num) (by positivity) (by linarith) (by positivity) (by norm_num)
      P.hτ P.he (by linarith) hsched.radial η₀,
    eventually_actual_main_high_literal_admission (α:=α) M H hH
      (9/4) (9/4) (μ/8) (μ/64) (1/4) P.τ P.e 28 P.bΦ ρ
      (by norm_num) (by norm_num) (by positivity) (by linarith) (by positivity) (by norm_num)
      P.hτ P.he (by linarith) hsched.radial η₀,
    eventual_geometry_joint_support η₀ u₀ F₀ R₀ hu₀ (9/4) (μ/8) (Fintype.card α)
      (by norm_num) (by positivity),hfiber,
    eventually_geometry_zero_heights P.e P.τ P.hτ,
    eventual_actual_geometry_main_high_source_caps (Fintype.card α) (9/4) (9/4) (μ/8)
      (by norm_num) (by norm_num) (by positivity) (by linarith)]
    with Z he had hlit hjoint hfib hzero hsource
  refine ⟨he.1,?_⟩
  intro hZ s p caps θ w σ freq hm R seed Mrow hR hseed hRcap hMrow hMrow1 hfit height mesh hw hwL hwr hmesh hwm
    hσ hheight hfreq hT hβhi Label _ reflected second bin t amp firstIndex first omega hamp0 hamp homega hf₁ hinj
    rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u hSmall hP hPN canonical firstMass childSrc ordinary coefficient select side
  let hKfirst:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  have hvol3 : volume s≤Z^(3:ℝ):=caps.volume.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  let Original:=geometryMainNonzeroBlocks reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t
    (Fintype.card α) hZ bin caps.zero₁ caps.zero₂
  let embed : rows→Original:=mainLowSelectedOriginal reflected s R seed Z Mrow amp (μ/64) (μ/8) (9/4) t
    (Fintype.card α) hZ bin caps.zero₁ caps.zero₂ firstIndex
  let full : Original→SecondInputDatum α:=fun q=>geometryLowSecondDatum reflected s R seed Z Mrow amp
    (μ/64) (μ/8) (9/4) t (Fintype.card α) hZ bin q.val.1 caps.zero₁ caps.zero₂ q.val.2
  let originalDatum : Original→SecondInputDatum α:=fun q=>ordinarySecondDatum (full q) χ₀ (internalQ Q η₀) m
  let firstOriginal:=fun q : Original=>geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hKfirst bin q.val.1.1.val
  let Live:=secondLiveRows (fun q=>(ordinary q).block)
  let row : Live→secondLiveRows (fun q=>(originalDatum q).block):=
    highSelectedLiveRowEmbedding originalDatum embed
  let highRows : Finset Live:=Finset.univ.filter (fun r=>((1+qh)/2)≤bufferValue P.e (select r))
  have hA4 : |Real.logb Z (volume s)|≤4:=caps.volumeLog.trans (by norm_num)
  have hMrow4 : |Mrow|≤4 := by rw [abs_of_nonneg hMrow]; linarith
  have literal (q : Original):=hlit.2 hZ reflected second s R seed Mrow amp (μ/8) t caps.endpoints
    hseed hR hRcap caps.zero₁ caps.zero₂ caps.sourceCap hvol3 hamp0 (by positivity) hMrow4
    hA4 hamp homega
    bin χ₀ (internalQ Q η₀) hQ72 m hm₀ hml hm₂ (inf_le_left.trans hQM) inf_le_right hbeta hβhi q
  have hadmit:=had.2 hZ reflected second s R seed Mrow amp (μ/8) t caps.endpoints
    hseed hR hRcap caps.zero₁ caps.zero₂ caps.sourceCap hvol3 hamp0 (by positivity) hMrow4
    hA4 hamp homega
    bin (fun _=>χ₀) (fun _=>internalQ Q η₀) (fun _=>hQ72) (fun _=>m) (fun _=>hm₀)
    (fun _=>hml) (fun _=>hm₂) (fun _=>inf_le_left.trans hQM) (fun _=>inf_le_right) hbeta hβhi
  obtain ⟨hPo,hPNo,keepo,selecto,hadmitted⟩:=hadmit
  refine ⟨hPo,hPNo,?_⟩
  intro pay
  have hfamily:=actual_main_high_canonical_family_admission M H hH datum (fun _=>χ₀)
    (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z 28 P.bΦ hZ hsched.radial second hP hPN η₀
    (inf_le_left.trans hQM) inf_le_right P.e (Z^P.τ) P.he hT hbeta hβhi
  obtain ⟨keep,hcanonical⟩:=hfamily
  let ψ : Live→RayCharacter:=fun r=>if second then r.val.2.2.1⁻¹ else r.val.2.1
  let signed : Live→O:=fun r=>if second then -r.val.2.2.2.val else r.val.2.2.2.val
  let st : Live→NaturalState Z 28 P.bΦ:=fun r=>widenHighState
    (retainedState Z 28 hZ ((datum r.val.1).τ (ψ r)) (internalQ Q η₀)
      ((datum r.val.1).R*(if second then (datum r.val.1).D else (datum r.val.1).C))
      (hP r.val.1) (hPN r.val.1) (datum r.val.1).radius (datum r.val.1).C (datum r.val.1).D
      (datum r.val.1).inactive) P.bΦ hsched.radial
  have hwidth (r : Live) : (st r).width≤2 := by
    have hadmission : (st r).width≤Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)+1/4+μ/64/2 := by
      cases second <;> exact (hadmitted (row r)).1
    linarith
  have hkeep (r : Live) : (st r).radial.keep (signed r) := by
    cases second <;> exact keep r
  have hcanon (r : Live) : GeometryZeroBin M H hH (st r) η₀ (inf_le_left.trans hQM) inf_le_right
      (signed r) (hkeep r) P.e (Z^P.τ) (select r) := by
    cases second <;> exact (hcanonical r).2.2.2
  have hradial (r : Live) : (st r).radial.profile (‖eisEmbedding (signed r)‖^2/(st r).radial.scale)≠0 := by
    rw [←normValue_eq_embedding]
    cases second <;> exact (hcanonical r).2.1
  let left:=!reflected
  let unit:=fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
  let column:=fun r : Live=>(row r).val.1.val.1.1.val
  let hfirst : ∀r,firstOriginal (row r).val.1=geometryFirstLabel s R seed (Z^Mrow) Z
      (μ/64) hKfirst bin (column r):=fun _=>rfl
  let hf:=fun r=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^Mrow) Z
    (μ/64) hKfirst bin (column r) originalDatum firstOriginal (row r) (hfirst r)
  let rawKey:=fun r=>secondEncodedNonzeroRow (fun q=>(originalDatum q).block) firstOriginal (row r)
    left u₀ unit (hf r)
  let key:=fun r=>if second then reflectedNonzeroJointLabel (rawKey r) else rawKey r
  have hsupport (r : Live) : ((Ideal.span {jointSourceRow left u₀ unit (key r).val}*
      firstSourceMissing left (key r).val.1).absNorm:ℝ)≤Z^(130:ℝ) := by
    have hj:=hjoint hZ (ι:=α) (α:=α) (Label:=↥Original) reflected s R seed (Z^Mrow)
      (μ/64) amp (μ/8) Mrow 3 hKfirst hseed caps.zero₁ caps.zero₂ caps.sourceCap le_rfl
      (by positivity) (by linarith) hamp0 (by positivity) bin (column r) originalDatum firstOriginal
      (row r) (hfirst r) rfl
    have hb : ((Ideal.span {jointSourceRow left u₀ unit (rawKey r).val}*
        firstSourceMissing left (rawKey r).val.1).absNorm:ℝ)≤Z^(130:ℝ) :=
      hj.2.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
    cases second
    · exact hb
    · change ((Ideal.span {jointSourceRow left u₀ unit (reflectedJointLabel (rawKey r).val)}*
        firstSourceMissing left (rawKey r).val.1).absNorm:ℝ)≤Z^(130:ℝ)
      rw [reflected_joint_row,Ideal.span_singleton_neg]
      exact hb
  have hcoordinate (r : Live) :
      childHighCoordinates (actualHighCoordinates reflected left second (firstOriginal (row r).val.1)
        (originalDatum (row r).val.1).C (originalDatum (row r).val.1).D
        (originalDatum (row r).val.1).inactive Z Mrow (Real.logb Z (volume s)) amp (μ/64) (μ/8) (μ/8))
        (μ/8) 2+μ/32≤130 :=
    ((literal (row r).val.1).2.2.2.2 (μ/8) (μ/8) (μ/32)
      (by rw [abs_of_nonneg (by positivity : 0≤μ/8)]; linarith)
      (by linarith)).1
  have hnorm (r : Live) : ((originalDatum (row r).val.1).C.absNorm:ℝ)≤Z^(130:ℝ) ∧
      ((originalDatum (row r).val.1).D.absNorm:ℝ)≤Z^(130:ℝ) :=
    ⟨(literal (row r).val.1).2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)),
      (literal (row r).val.1).2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))⟩
  have hprofile : (p.control G)^2*amplitude≤(p.control Sp)^2*amplitude := by
    have hc:=CenteredMomentEnergyBandMonotonicity.profile_control_mono p (Finset.subset_union_left : G⊆Sp)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Profiles.control_nonneg _ _) hc _) hampPositive.le
  let selectedFirst:=fun q : rows=>first q.val.1
  let hSelected : ∀r : Live,jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun q=>(ordinary q).block) selectedFirst r)≠0:=fun r=>
    actual_joint_first_frequency_ne_zero left u₀ unit
      (secondEncodedRow (fun q=>(ordinary q).block) selectedFirst r) hu₀ (Units.ne_zero _)
      (geometryFirstSource s R seed (Z^Mrow) Z (μ/64) hKfirst bin (firstIndex r.val.1.val.1).1.val.1).hC
  have hkeys (r : Live) : key r=
      (if second then reflectedNonzeroJointLabel
        (secondEncodedNonzeroRow (fun q=>(ordinary q).block) selectedFirst r left u₀ unit (hSelected r))
      else secondEncodedNonzeroRow (fun q=>(ordinary q).block) selectedFirst r left u₀ unit (hSelected r)) :=
    affine_high_selected_live_reflected_key originalDatum embed firstOriginal r left second u₀ unit (hf r) (hSelected r)
  have hFibers : ∀target,((Finset.univ.filter (fun r : highRows=>key r.val=target)).card:ℝ)≤Cf*Z^(2*(μ/8)) := by
    intro target
    have hh:=hfib hZ (Label:=Label) reflected s R seed Mrow amp (μ/8) t hseed caps.endpoints hvol3
      (Real.rpow_le_rpow_of_exponent_le hZ.le hMrow1)
      caps.zero₁ caps.zero₂ hamp0 (by positivity) bin firstIndex hf₁ hinj χ₀ (internalQ Q η₀) m
      highRows second hSelected target
    change ((Finset.univ.filter (fun r : highRows=>
      (if second then reflectedNonzeroJointLabel
        (secondEncodedNonzeroRow (fun q=>(ordinary q).block) selectedFirst r.val left u₀ unit (hSelected r.val))
      else secondEncodedNonzeroRow (fun q=>(ordinary q).block) selectedFirst r.val left u₀ unit
        (hSelected r.val))=target)).card:ℝ)≤Cf*Z^(2*(μ/8)) at hh
    simpa only [hkeys] using hh
  have hcostEq : (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(ordinary l).block)=>
          ((1+qh)/2)≤bufferValue P.e (select r)),
        (coefficient r.val.1*((ordinary r.val.1).K/lowerFactor (Fintype.card α) 1 (1/4))*
          normalizer (ordinary r.val.1).C (ordinary r.val.1).D (ordinary r.val.1).inactive)*
        highNormalizedRowCost second ordinary r
          ((ordinary r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
          ((ordinary r.val.1).block.divisors.filter Squarefree))=
      ∑r∈highRows,∑L∈secondResidualIdeals (fun q=>(ordinary q).block) r.val,
        mainNormalizedPhysicalCost (Fintype.card α) 1 (1/4) second ordinary coefficient t₀ u r.val L :=
    (geometry_main_high_physical_row_sum (Fintype.card α) 1 (1/4) second ordinary coefficient t₀ u highRows).symm
  refine hcostEq.trans_le ?_
  -- The HIGH rows of the family are among those of all nonzero blocks, with the same keys, coordinates and selector.
  let fullU:=affineHighBlockDatum reflected s R seed Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂
  let ordinaryU:=fun j=>ordinarySecondDatum (fullU j) χ₀ (internalQ Q η₀) m
  let firstU:=fun j : Original=>geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hKfirst bin j.val.1.1.val
  let canonicalU:=fun j (χ ψ : RayCharacter)=>mainLowCanonicalSelector M H hH (fullU j) χ₀ χ ψ (internalQ Q η₀)
    hQ72 m hm₀ hml hm₂ Z 28 hZ second (hPo j) (hPNo j) η₀ (inf_le_left.trans hQM) inf_le_right P.e
    (Z^P.τ) P.he hT hbeta hβhi
  let selectU:=mainPhysicalFamilySelector second ordinaryU canonicalU
  let hfU:=fun r : secondLiveRows (fun j=>(ordinaryU j).block)=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀
    R₀ hu₀ s R seed (Z^Mrow) Z (μ/64) hKfirst bin r.val.1.val.1.1.val ordinaryU firstU r rfl
  let rawKeyU:=fun r=>secondEncodedNonzeroRow (fun j=>(ordinaryU j).block) firstU r left u₀ unit (hfU r)
  let keyU:=fun r=>if second then reflectedNonzeroJointLabel (rawKeyU r) else rawKeyU r
  let AU:=Real.logb Z (volume s.toData)
  let xU:=fun r : secondLiveRows (fun j=>(ordinaryU j).block)=>compensatedHighCoordinates
    (childHighCoordinates (actualHighCoordinates reflected left second (firstU r.val.1) (ordinaryU r.val.1).C
      (ordinaryU r.val.1).D (ordinaryU r.val.1).inactive Z Mrow AU amp (μ/64) (μ/8) (μ/8)) (μ/8))
    (geometryHighSide reflected AU (geometryExponents s R seed (Z^Mrow) Z (μ/64) r.val.1.val.1.1.val.1.val))
  let highU:=Finset.univ.filter (fun r : secondLiveRows (fun j=>(ordinaryU j).block)=>
    ((1+qh)/2)≤bufferValue P.e (selectU r))
  let extra:=μ/4+μ/4+(2*(μ/8)+δ+3*((Nbudget:ℝ)+2)*δ+130*δ+130*δ+3*((Nbudget:ℝ)+2)*(2*δ))
  have hUT : affineHighUniversalTransport M H hH η₀ u₀ F₀ R₀ hu₀ reflected second s R seed
      Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ χ₀ (internalQ Q η₀) hQ72 m hm₀ hml hm₂
      (inf_le_left.trans hQM) inf_le_right P.e (Z^P.τ) P.he hT hbeta hβhi hPo hPNo qh
      extra=∑q : BufferIndex P.e,keyBinnedCount (highU.filter (fun r=>selectU r=q)) keyU xU (μ/32)
        (fun k=>Z^(exponentBinUpper (μ/32) k 0+(2*bufferValue P.e q-1)*exponentBinUpper (μ/32) k 3+extra)):=rfl
  let A:=Real.logb Z (volume s.toData)
  let xc:=fun r : Live=>compensatedHighCoordinates (childHighCoordinates (actualHighCoordinates reflected left second
      (geometryFirstLabel s R seed (Z^Mrow) Z (μ/64) hKfirst bin (column r)) (originalDatum (row r).val.1).C
      (originalDatum (row r).val.1).D (originalDatum (row r).val.1).inactive Z Mrow A amp (μ/64) (μ/8) (μ/8))
      (μ/8))
    (geometryHighSide reflected A (geometryExponents s R seed (Z^Mrow) Z (μ/64) (column r).1.val))
  let rowU : Live→secondLiveRows (fun j=>(ordinaryU j).block):=row
  have hcmp (q : BufferIndex P.e) (wt : (Fin 4→ℤ)→ℝ) (hwt : ∀b,0≤wt b) :
      keyBinnedCount (highRows.filter (fun l=>select l=q)) key xc (μ/32) wt≤
        keyBinnedCount (highU.filter (fun r=>selectU r=q)) keyU xU (μ/32) wt := by
    have h1 : keyBinnedCount (highRows.filter (fun l=>select l=q)) key xc (μ/32) wt=
        keyBinnedCount (highRows.filter (fun l=>select l=q)) (fun l=>keyU (rowU l)) (fun l=>xU (rowU l))
          (μ/32) wt:=rfl
    refine h1.trans_le (keyBinnedCount_le_of_map _ _ rowU (fun l hl=>?_) keyU xU (μ/32) wt hwt)
    have hsel : select l=selectU (rowU l):=rfl
    simp only [highRows,Finset.mem_filter,Finset.mem_univ,true_and] at hl
    rw [hsel] at hl
    simp only [highU,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hl
  have hside : 0 ≤ side:=(geometry_high_factor_pos reflected _ bin
    (geometrySupportConstant_pos (Fintype.card α) 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  have hsummand (q : BufferIndex P.e) :
      (1/lowerFactor (Fintype.card α) 1 (1/4))*((Cf*Z^(2*(μ/8)))*(Kmove*Z^δ*(2*Z^(3*((Nbudget:ℝ)+2)))^δ*
        Cs^(2*Fintype.card α)*Z^(130*δ)*(side*Z^(130*δ)*keyBinnedCount (highRows.filter (fun l=>select l=q)) key xc
          (μ/32) (fun k=>Cmove*((p.control Sp)^2*amplitude)*(2*Z^(3*((Nbudget:ℝ)+2)))^(2*δ)*
            Z^(exponentBinUpper (μ/32) k 0+(2*bufferValue P.e q-1)*exponentBinUpper (μ/32) k 3+μ/4+μ/4)))))≤
      Kt*(p.control Sp)^2*side*keyBinnedCount (highU.filter (fun r=>selectU r=q)) keyU xU (μ/32)
        (fun k=>Z^(exponentBinUpper (μ/32) k 0+(2*bufferValue P.e q-1)*exponentBinUpper (μ/32) k 3+extra)) := by
    rw [affine_high_transport_constants (highRows.filter (fun l=>select l=q)) key xc (μ/32) Z (zero_lt_one.trans hZ)
      (fun k=>exponentBinUpper (μ/32) k 0+(2*bufferValue P.e q-1)*exponentBinUpper (μ/32) k 3+μ/4+μ/4)
      (lowerFactor (Fintype.card α) 1 (1/4)) Cf (2*(μ/8)) Kmove δ (3*((Nbudget:ℝ)+2)) δ Cs 130 δ side Cmove
      ((p.control Sp)^2*amplitude) (2*Fintype.card α)]
    have hKt' : (1/lowerFactor (Fintype.card α) 1 (1/4))*Cf*Kmove*Cs^(2*Fintype.card α)*Cmove*(2:ℝ)^δ*
        (2:ℝ)^(2*δ)*((p.control Sp)^2*amplitude)*side=Kt*(p.control Sp)^2*side := by
      dsimp only [Kt]
      ring
    rw [hKt']
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg hKt.le (sq_nonneg _)) hside)
    have hw : (fun k : Fin 4→ℤ=>Z^(exponentBinUpper (μ/32) k 0+(2*bufferValue P.e q-1)*exponentBinUpper (μ/32) k 3+
        μ/4+μ/4+(2*(μ/8)+δ+3*((Nbudget:ℝ)+2)*δ+130*δ+130*δ+3*((Nbudget:ℝ)+2)*(2*δ))))=
        (fun k=>Z^(exponentBinUpper (μ/32) k 0+(2*bufferValue P.e q-1)*exponentBinUpper (μ/32) k 3+extra)) := by
      funext k
      congr 1
      dsimp only [extra]
      ring
    rw [hw]
    exact hcmp q _ fun _=>Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  by_cases hnonempty : Nonempty Live
  · let : Nonempty Live:=hnonempty
    have hbefore:=he.2 (κ:=↥Live) reflected second s R seed Ψ Mrow (μ/64) amp (μ/8) t hKfirst hR hZ bin
      caps.zero₁ caps.zero₂ (fun _=>χ₀) (fun _=>internalQ Q η₀) (fun _=>m) row ψ (μ/4) (μ/4)
      ((p.control Sp)^2*amplitude) Cf (div_nonneg hμ.le (by norm_num))
      (div_nonneg hμ.le (by norm_num)) (mul_nonneg (sq_nonneg _) hampPositive.le) hCf.le
      highRows hFibers select (fun r _=>hcoordinate r) hseed
      (caps.sourceCap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))
      (by rw [caps.lower]) (by linarith only [hμ.le]) (fun r _=>hnorm r)
    let stP : Live→NaturalState Z P.Bmask P.bΦ:=fun r=>reboundAffineHighState (st r)
      (by simpa only [hsched.mask] using (st r).puncture_bound)
    have hb:=hbefore
      stP (fun _=>inf_le_left.trans hQM) (fun _=>inf_le_right) signed hkeep (fun _=>rfl) (fun _=>rfl)
      (fun _=>rfl) (fun r _=>hcanon r) (fun r hr=>le_trans (by linarith only [hqh]) (Finset.mem_filter.mp hr).2)
      (fun r _=>hsupport r) (fun r _=>hzero.2.2 (select r)) rfl caps.controls
      (by rw [caps.b₁]) (by rw [caps.b₂]) caps.endpoints.1 caps.windows
      t₀ u height w σ freq θ p 1 hheight hfreq hSmall
      (by rw [hsched.degree,hsched.plain]; norm_num)
      (by simpa only [hsched.slot,hsched.slotCap] using hm) caps.plainScales
      (by linarith only [hδsmall,hμ]) (fun r _=>by rw [hsched.retainedWidth]; exact hwidth r)
      (fun r _=>hradial r) hw
      (fun j=>by simpa only [hsched.degree,hsched.width] using hwr j)
      (fun j=>by rw [hsched.sigmaLo]; exact (hσ j).1)
      (fun j=>by rw [hsched.sigmaHi]; exact (hσ j).2) caps.profile₁ caps.profile₂ caps.b₁ caps.b₂ caps.poolCap
      hprofile (by simpa only [hsched.plainRate,hsched.slotRate,hsched.degree] using hraw)
      (fun _ _=>rfl) pay
    change Z^(-amp)*(∑r∈highRows,∑L∈secondResidualIdeals (fun q=>(ordinary q).block) r.val,
      mainNormalizedPhysicalCost (Fintype.card α) 1 (1/4) second ordinary coefficient t₀ u r.val L)≤_ at hb
    refine (geometry_affine_high_unamplify_bound Z amp _ _ (zero_lt_one.trans hZ) hb).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    cases pay with
    | some c =>
      dsimp only [Option.elim]
      apply le_of_eq
      ring
    | none =>
      dsimp only [Option.elim]
      refine (Finset.sum_le_sum fun q _ => hsummand q).trans_eq ?_
      refine (Finset.mul_sum _ _ _).symm.trans ?_
      exact congrArg (fun x=>Kt*(p.control Sp)^2*side*x) hUT.symm
  · let : IsEmpty Live:=not_nonempty_iff.mp hnonempty
    refine (Finset.sum_eq_zero fun r _=>isEmptyElim r).trans_le ?_
    have hT₀ := affineHighUniversalTransport_nonneg M H hH η₀ u₀ F₀ R₀ hu₀ reflected second s R seed
      Z Mrow amp μ t hZ bin caps.zero₁ caps.zero₂ χ₀ (internalQ Q η₀) hQ72 m hm₀ hml hm₂
      (inf_le_left.trans hQM) inf_le_right P.e (Z^P.τ) P.he hT hbeta hβhi hPo
      hPNo qh (μ/4+μ/4+(2*(μ/8)+δ+3*((Nbudget:ℝ)+2)*δ+130*δ+130*δ+3*((Nbudget:ℝ)+2)*(2*δ)))
    have hs : 0 < side :=
      geometry_high_factor_pos reflected _ bin
        (geometrySupportConstant_pos (Fintype.card α) 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))
    have hZ0 : 0<Z:=zero_lt_one.trans hZ
    refine mul_nonneg (Real.rpow_nonneg hZ0.le _) ?_
    cases pay with
    | some c =>
      dsimp only [Option.elim]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hKs.le hCf.le) hampPositive.le)
        (sq_nonneg _)) hs.le) (Real.rpow_nonneg hZ0.le _)
    | none =>
      dsimp only [Option.elim]
      exact mul_nonneg (mul_nonneg (mul_nonneg hKt.le (sq_nonneg _)) hs.le) hT₀

/-- The density dictionary and degree precede the moving source, detector,
and common cutoff. The actual Fourier count is kept distinct from its budget. -/
theorem actual_affine_high_selected_small_height_of_fibers
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (μ Cs : ℝ)(Nbudget : ℕ)(hμ : 0<μ)(hμcap : μ≤Cycle63.Optimization.geometryLossCap)(hCs : 1≤Cs)
    (hN : Fintype.card α≤Nbudget)
    (fiberReceipt : GeometryAffineHighSelectedFiberReceipt (α:=α) η₀ u₀ F₀ R₀ (9/4) (9/4)
      (μ/8) 3 1 (μ/64)) :
    let δ:=geometryAffineHighDictionaryRate μ Nbudget
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      GeometryAffineHighScheduleGates W μ δ P →
      MarkedSchedule P (Fintype.card α) W (33/50) (33/50) →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain → 2*P.τ*(J+1)≤μ/8 →
      ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃K : ℝ,0<K ∧
      ∀(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}),
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
        GeometryAffineHighSelectedCostSpec (α:=α) M H hH W hbeta P μ δ
          (geometryAffineHighTarget μ δ)
          (fun Z t height t₀ u=>|t|+height+2*Real.pi*(|u|+|t₀|)≤Z^P.τ)
          (excluded F₀.character R₀) Cs Sp 0 K η₀ Q hQM hQ72 Z := by
  intro δ
  have hμ1 : μ ≤ 1/1000 := hμcap.trans (by
    norm_num [Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight,
      Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice,
      Cycle63.Optimization.betaBound])
  have rates:=geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((Nbudget:ℝ)+2)) Nbudget
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hgen0:=actual_affine_high_selected_small_height_shell (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper μ Cs 0 Nbudget hμ hμcap hCs (by norm_num) Cycle153.MarkedRootPrice.q le_rfl
    hN fiberReceipt δ rfl
  obtain ⟨bound,hbound,J,hgen⟩:=hgen0
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hsched hmarked hslot hplain hdensity
  have hgenP:=hgen P hboundeq hsched hmarked hslot hplain hdensity
  obtain ⟨Sp,hSp,K,Kt,hK,_,hgen⟩:=hgenP
  refine ⟨Sp,hSp,K,hK,?_⟩
  intro Q hQM hQ72
  filter_upwards [hgen Q hQM hQ72,eventual_geometry_small_frequency μ hμ,
    Cycle63Moment.fixed_anchor_width_uniform (fun _:Unit=>excluded F₀.character R₀) 1 (μ/16)
      one_pos (by positivity)]
    with Z hg hω hanchor
  refine ⟨hg.1,?_⟩
  unfold GeometryAffineHighSelectedCostSpec
  intro hZ s p caps θ w σ freq hm hsη height mesh hw hwL hwr hmesh hwm hwmarked hσ hheight hfreq hT hβhi
    hzslot haff hvolumeCell Label _ reflected second bin t firstIndex first amp omega hamp0 hamp homega hf₁ hinj
    rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u hSmall hP hPN canonical firstMass childSrc ordinary coefficient select
  have hfit : (1:ℝ)+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+μ/16 := by
    have hc:=hanchor.2 () 1 le_rfl
    rw [hsη]
    linarith
  have hgZ:=hg.2 hZ s p caps θ w σ freq hm 1 1 1 one_ne_zero squarefree_one (by simp) zero_le_one
    le_rfl hfit height mesh hw hwL hwr hmesh hwm hσ hheight hfreq hT hβhi reflected second bin t amp firstIndex
    hamp0 hamp homega hf₁ hinj χ₀ m hm₀ hml hm₂ Ψ t₀ u hSmall hP hPN
  obtain ⟨hPU,hPNU,hb⟩:=hgZ
  have hsupplyUpper : (∑j,w j)≤Cycle153.MarkedRootPrice.top := by
    simpa only [hm.scale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hzslot.2
  have hcell:=Cycle153.MarkedRootPrice.originalCell_mem hzslot
  let bAmpl:=Cycle153.MarkedRootPrice.cellUpper (Cycle153.MarkedRootPrice.originalCell (∑j,Real.logb Z (s.P j)))
  have hbAmpl : Cycle63.Optimization.firstCellTop≤bAmpl ∧ bAmpl≤Cycle153.MarkedRootPrice.top:=
    Cycle153.MarkedRootPrice.cellUpper_bounds hcell.1 hcell.2.1
  -- The slot sum lies in the cell of upper edge `bAmpl`.
  have hsupply : (bAmpl-Cycle63.Optimization.cellMesh)*1≤∑j,w j := by
    have hsum : (∑j,Real.logb Z (s.P j))=∑j,w j := by
      simp only [hm.scale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
    have hlow := hcell.2.2.1
    rw [← hsum]
    unfold Cycle63.Optimization.cellMesh
    rw [mul_one]
    exact hlow
  have htotalA : Real.logb Z (volume s)≤1*Cycle153.MarkedRootPrice.totalA bAmpl := by
    simpa only [one_mul] using hvolumeCell
  have hampCell : amp≤1*Cycle153.MarkedRootPrice.amp bAmpl := by
    dsimp only [amp,bAmpl]
    rw [div_one]
  have hfinal : omega+μ/8+μ/8+4*(μ/32)+μ/8+μ/4+μ/4+130*δ+μ/8+
      130*δ+3*(3*((Nbudget:ℝ)+2))*δ+δ+2*(μ/8)≤4*μ-3*δ := by
    have hl:=geometry_final_main_high_consumer_ledger μ 31 3 4 3 130 (3*((Nbudget:ℝ)+2))
      omega (μ/4) (μ/4) Nbudget hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by positivity) hω.2.2 le_rfl le_rfl
    dsimp only at hl
    rw [geometry_affine_final_dictionary_mass_rate_eq μ 130 (3*((Nbudget:ℝ)+2)) Nbudget hμ (by norm_num)
      (by norm_num)] at hl
    change omega+μ/8+μ/8+4*(μ/32)+μ/8+μ/4+μ/4+130*δ+μ/8+
      130*δ+3*(3*((Nbudget:ℝ)+2))*δ+δ+2*(μ/8)+3*δ≤4*μ at hl
    linarith only [hl]
  have hpaid:=hb (some ⟨⟨bAmpl,hbAmpl.1,hbAmpl.2,rfl,(by norm_num),(by norm_num),
    (caps.volumeLog.trans (by norm_num)),(hamp.trans (by norm_num)),(homega.trans (by norm_num)),
    (by unfold Cycle63.Optimization.frequencyLossCap; linarith [hω.2.2, hμcap]),(by linarith only [hμ1]),
    htotalA,hampCell,hsupply,hsupplyUpper,hwmarked,hsη⟩,hfinal⟩)
  have htarget : -(1:ℝ)*(Cycle153.MarkedRootPrice.lowReserve)+4*μ-3*δ=geometryAffineHighTarget μ δ := by
    unfold geometryAffineHighTarget
    ring
  refine hpaid.trans (le_of_eq ?_)
  dsimp only [Option.elim]
  simp only [htarget,Real.rpow_add (zero_lt_one.trans hZ),pow_zero,mul_one]
  ring

/-- Genuine all-height payment on the same inclusive canonical high rows.
The density dictionary precedes the cutoff and the moving detector. -/
theorem actual_affine_high_selected_all_height_of_fibers
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (μ Cs : ℝ)(Nbudget : ℕ)(hμ : 0<μ)(hμcap : μ≤Cycle63.Optimization.geometryLossCap)(hCs : 1≤Cs)
    (hN : Fintype.card α≤Nbudget)
    (fiberReceipt : GeometryAffineHighSelectedFiberReceipt (α:=α) η₀ u₀ F₀ R₀ (9/4) (9/4)
      (μ/8) 3 1 (μ/64)) :
    let δ:=geometryAffineHighDictionaryRate μ Nbudget
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      GeometryAffineHighScheduleGates W μ δ P →
      MarkedSchedule P (Fintype.card α) W (33/50) (33/50) →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain → 2*P.τ*(J+1)≤μ/8 →
      ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃degree : ℕ,∃K : ℝ,0<K ∧
      ∀(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}),
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
        GeometryAffineHighSelectedCostSpec (α:=α) M H hH W hbeta P μ δ
          (geometryAffineHighTarget μ δ) (fun _ _ _ _ _=>True)
          (excluded F₀.character R₀) Cs Sp degree K η₀ Q hQM hQ72 Z := by
  intro δ
  obtain ⟨bound,hbound,J,hsmall⟩:=actual_affine_high_selected_small_height_of_fibers (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper μ Cs Nbudget hμ hμcap hCs hN fiberReceipt
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hsched hmarked hslot hplain hdensity
  obtain ⟨Sp,hSp,Ks,hKs,hsmall⟩:=hsmall P hboundeq hsched hmarked hslot hplain hdensity
  have hδ : 0<δ:=(geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((Nbudget:ℝ)+2)) Nbudget hμ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)).1
  obtain ⟨Kc,hKc,hcoarse⟩:=actual_affine_high_selected_coarse (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ W hbeta P μ δ Cs (excluded F₀.character R₀) hμ (hμcap.trans (by norm_num [Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.planeQuadratic, Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound])) hδ hCs
  obtain ⟨degree,hsplice⟩:=geometry_affine_high_selected_height_splice (α:=α) M H hH W hbeta P μ δ
    (geometryAffineHighTarget μ δ) (geometryAffineHighCoarseExponent μ δ (Fintype.card α))
    (excluded F₀.character R₀) Cs Sp
  refine ⟨Sp,hSp,degree,(2+4*Real.pi)^degree*(Ks+Kc),by positivity,?_⟩
  intro Q hQM hQ72
  filter_upwards [hsmall Q hQM hQ72,hcoarse Q hQM hQ72] with Z hs hc
  refine ⟨hs.1,?_⟩
  have hlarge:=geometry_affine_high_selected_cost_mono (α:=α) M H hH W hbeta P μ δ
    (geometryAffineHighCoarseExponent μ δ (Fintype.card α)) (fun _ _ _ _ _=>True)
    (excluded F₀.character R₀) Cs {(0,0)} Sp 0 Kc η₀ Q hQM hQ72 Z hKc.le
    (by simpa only [Finset.singleton_subset_iff] using hSp) hc.2
  exact hsplice Ks Kc hKs.le hKc.le η₀ Q hQM hQ72 Z hs.2 hlarge

attribute [local irreducible] SecondInputDatum.block
set_option maxHeartbeats 160000 in
set_option linter.unusedVariables false in
set_option linter.defProp false in
/-- The literal affine-input high receipt has no source-cap, Matches,
volume-cell, or amplifier premise. The selected cost and selector are exact. -/
def GeometryAffineMainHighSpec
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(P : HighSourceParameters)(μ δ target : ℝ)
    (ηseed : Character)(Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})(Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(tplain X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)
    (height mesh : ℝ)(hw : ∀i,0≤w i)(hmesh : 0≤ mesh)
    (hmeshcap : mesh≤Cycle25.Energy.commonMesh 2 28 1 (μ/8))(hwm : ∀i,w i≤ mesh)
    (hwmarked : ∀i,w i≤ markedRawMesh*markedCoreMin)
    (hheight : 0≤height)(hfreq : ∀i,|freq i|≤height)(hT : 2<Z^P.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hwin : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i)),
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_profile_zero p 1
    ∀{Label : Type}[Fintype Label]
    (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
    let first:=fun l=>geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let amp:=(1:ℝ)*Cycle153.MarkedRootPrice.amp (Cycle153.MarkedRootPrice.cellUpper
      (Cycle153.MarkedRootPrice.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    let omega:=frequencyLoss Z 32 (μ/64)+μ/8
    ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
        1 s.ν s.W s.P≠0)
      (hinj : Function.Injective (fun l=>(first l,(firstIndex l).1.val.2.1.val))),
    let rows:=mainLowSelectedNonzeroRows reflected s 1 1 Z 1 amp (μ/64) (μ/8)
      (9/4) t (Fintype.card α) hZ bin hz₁ hz₂ firstIndex
    let datum : rows→SecondInputDatum α:=fun r=>geometryLowSecondDatum reflected s 1 1 Z 1 amp
      (μ/64) (μ/8) (9/4) t (Fintype.card α) hZ bin (firstIndex r.val.1)
      hz₁ hz₂ r.val.2
    ∀(χ₀ : RayFourExpansion.RayCharacter)(m : O)(hm₀ : m≠0)
      (hml : goodLambda∣m)(hm₂ : (2:O)∣m)(Ψ : 𝓢(ℝ,ℂ))(t₀ u : ℝ),
    ∀hP : ∀r,(datum r).R*(if second then (datum r).D else (datum r).C)≠0,
    ∀hPN : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤Z^(28:ℝ),
    let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
      mainLowCanonicalSelector M H hH (datum r) χ₀ χ ψ (internalQ Q η₀) hQ72
        m hm₀ hml hm₂ Z 28 hZ second (hP r) (hPN r) η₀
        (inf_le_left.trans hQM) inf_le_right P.e (Z^P.τ) P.he hT hbeta hβhi
    let firstMass:=fun l=>geometryFirstHighMass reflected s 1 1 Ψ 1 Z (μ/64) δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let childSrc:=fun l=>geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
    let ordinary:=fun r=>ordinarySecondDatum (datum r) χ₀ (internalQ Q η₀) m
    let coefficient:=fun r=>firstMass r.val.1/volume (childSrc r.val.1)
    let select:=mainPhysicalFamilySelector second ordinary canonical
    (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(ordinary l).block)=>
        ((1+Cycle153.MarkedRootPrice.q)/2)≤bufferValue P.e (select r)),
      (coefficient r.val.1*((ordinary r.val.1).K/lowerFactor (Fintype.card α) 1 (1/4))*
        normalizer (ordinary r.val.1).C (ordinary r.val.1).D (ordinary r.val.1).inactive)*
      highNormalizedRowCost second ordinary r
        ((ordinary r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((ordinary r.val.1).block.divisors.filter Squarefree))≤
      Kall*(p.control Sp)^2*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
        Z^(amp+target)*
        (1+|t|+height)^degreeAll*(1+|t₀|)^degreeAll*(1+|u|)^degreeAll

/-- The actual affine constructor supplies all remaining source gates,
including the exact cell-volume ledger omitted from generic source caps. -/
theorem affine_main_high_spec_of_receipts
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(P : HighSourceParameters)(μ δ target : ℝ)
    (ηseed : Character)(Cs : ℝ)(Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})(Z : ℝ)
    (_hμ : 0<μ)(hμcap : μ≤1/128)
    (hω : 0≤frequencyLoss Z 32 (μ/64)+μ/8 ∧ frequencyLoss Z 32 (μ/64)+μ/8≤33*μ/128)
    (hcaps : GeometryAffineMainLowSourceSpec (α:=α) M H hH W hW hWs Cs Z)
    (hspec : GeometryAffineHighSelectedCostSpec (α:=α) M H hH W hbeta P μ δ target
      (fun _ _ _ _ _=>True) ηseed Cs Sp degreeAll Kall η₀ Q hQM hQ72 Z) :
    GeometryAffineMainHighSpec (α:=α) M H hH W hW hWs hbeta P μ δ target
      ηseed Sp degreeAll Kall η₀ Q hQM hQ72 Z := by
  unfold GeometryAffineMainHighSpec
  intro hZ θ w σ freq hσ bΦ state hη p tplain X₁ X₂ hX₁ hX₂ height mesh hw hmesh hmeshcap hwm hwmarked
    hheight hfreq hT hβhi hwin s hz₁ hz₂
    Label _ reflected second bin t firstIndex first amp omega hf₁ hinj
    rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u hP hPN canonical firstMass childSrc ordinary coefficient select
  have cap₀:=hcaps θ η₀ w σ freq hσ bΦ state p tplain X₁ X₂ hX₁ hX₂ hw hwin
  obtain ⟨caps,hm⟩:=actual_affine_low_source_gates M H hH η₀ θ W hW hWs w σ freq hσ state p
    tplain X₁ X₂ hX₁ hX₂ Cs hZ hw hwin cap₀
  have hlogs : ∀j,Real.logb Z (s.P j)=w j := by
    intro j
    change Real.logb Z (Z^(w j))=w j
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hsum : (∑j,Real.logb Z (s.P j))=∑j,w j := Finset.sum_congr rfl (fun j _=>hlogs j)
  have hηs : s.η=ηseed:=hη
  have hw₁ (j : α) : w j≤1 :=
    (Finset.single_le_sum (fun i _=>hw i) (Finset.mem_univ j)).trans ((show (∑i,w i)≤Cycle153.MarkedRootPrice.top by simpa only [Cycle153.MarkedRootPrice.RootLedgerBinding.top_eq] using hwin.slots_le).trans (by norm_num [Cycle153.MarkedRootPrice.top]))
  have hwr (j : α) : w j/31≤1 := by linarith only [hw₁ j]
  have hcell:=Cycle153.MarkedRootPrice.originalCell_mem (by simpa only [Cycle153.MarkedRootPrice.RootLedgerBinding.floor_eq,Cycle153.MarkedRootPrice.RootLedgerBinding.top_eq] using And.intro hwin.slots_ge hwin.slots_le)
  have hbetaCell:=Cycle153.MarkedRootPrice.cellUpper_bounds hcell.1 hcell.2.1
  have hamp0 : 0≤amp := by
    simpa only [amp,hsum,div_one,one_mul] using (Cycle153.MarkedRootPrice.amp_pos hbetaCell).le
  have hamp : |amp|≤4 := by
    rw [abs_of_nonneg hamp0]
    have hbL : Cycle63.AffineLedger.firstCellTop≤Cycle153.MarkedRootPrice.cellUpper
        (Cycle153.MarkedRootPrice.originalCell (∑i,w i)) ∧
        Cycle153.MarkedRootPrice.cellUpper (Cycle153.MarkedRootPrice.originalCell (∑i,w i))≤L.slotTop := by
      simpa only [Cycle63.AffineLedger.firstCellTop,Cycle153.MarkedRootPrice.RootLedgerBinding.floor_eq,
        Cycle153.MarkedRootPrice.RootLedgerBinding.mesh_eq,Cycle153.MarkedRootPrice.RootLedgerBinding.top_eq,
        Cycle63.Optimization.firstCellTop] using hbetaCell
    have h:=((Cycle63.AffineLedger.amp_bounds hbL).2.trans Cycle63.AffineLedger.amplifierCap_le_one).trans
      (by norm_num : (1:ℝ)≤4)
    simpa only [Cycle153.MarkedRootPrice.affine_amp_eq,amp,hsum,div_one,one_mul] using h
  have homega : |omega|≤4 := by
    rw [abs_of_nonneg hω.1]
    exact hω.2.trans (by linarith only [hμcap])
  have hvolume:=actual_affine_exceptional_volume_cell M H hH η₀ θ W hW hWs w σ freq hσ
    state p tplain X₁ X₂ hX₁ hX₂ hZ hwin
  simp only [Cycle153.MarkedRootPrice.affine_totalA_eq,Cycle153.MarkedRootPrice.affine_cellUpper_eq,
    Cycle153.MarkedRootPrice.affine_originalCell_eq] at hvolume
  unfold GeometryAffineHighSelectedCostSpec at hspec
  have hb:=hspec hZ s p caps θ w σ freq hm hηs height mesh hw
    (fun j=>(hwm j).trans hmeshcap) hwr hmesh hwm hwmarked hσ hheight hfreq hT hβhi
    (by rw [hsum]; simpa only [Cycle153.MarkedRootPrice.RootLedgerBinding.floor_eq,Cycle153.MarkedRootPrice.RootLedgerBinding.top_eq] using And.intro hwin.slots_ge hwin.slots_le) (by
      change length Z X₁+length Z X₂+Cycle153.MarkedRootPrice.lambda*(∑j,Real.logb Z (s.P j))≤Cycle153.MarkedRootPrice.B
      rw [hsum]; simpa only [Cycle153.MarkedRootPrice.RootLedgerBinding.lam_eq,Cycle153.MarkedRootPrice.RootLedgerBinding.B_eq] using hwin.plane)
    (by rw [hsum]; exact hvolume)
    reflected second bin t firstIndex hamp0 hamp homega hf₁ hinj χ₀ m hm₀ hml hm₂ Ψ t₀ u True.intro hP hPN
  exact hb

/-- The independently checked supported-allocation fiber theorem supplies
exactly the selected receipt used by the actual high consumer. -/
theorem geometry_affine_high_selected_fiber_receipt
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (μ : ℝ)(hμ : 0<μ) :
    GeometryAffineHighSelectedFiberReceipt (α:=α) η₀ u₀ F₀ R₀ (9/4) (9/4)
      (μ/8) 3 1 (μ/64) := by
  exact eventually_affine_high_selected_ordinary_fibers η₀ u₀ F₀ R₀ hu₀ (α:=α)
    (9/4) (9/4) (μ/8) 3 1 (μ/64) (by norm_num) (by norm_num)
    (by positivity) (by norm_num) (by norm_num) (by positivity) (by linarith only [hμ])

end
end OAI.SevenEighths.Cycle153RootHigh

#print axioms OAI.SevenEighths.Cycle153RootHigh.actual_affine_high_selected_all_height_of_fibers
#print axioms OAI.SevenEighths.Cycle153RootHigh.affine_main_high_spec_of_receipts
