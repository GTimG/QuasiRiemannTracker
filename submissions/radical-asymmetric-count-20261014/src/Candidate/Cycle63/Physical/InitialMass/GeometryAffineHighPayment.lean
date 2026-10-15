/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighFinalPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineFinalSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryMainCompletePartition
import Candidate.Cycle63.Physical.InitialMass.GeometryCoarseSupport
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighNormalizedPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineHighSelectedTransport
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineHighSelectedFiber
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainLowPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
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
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)



/-- The shared rate uses the ambient budget; Fourier data retain the actual count. -/
def geometryAffineHighDictionaryRate (μ : ℝ) (Nbudget : ℕ) : ℝ :=
  geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((Nbudget:ℝ)+2)) Nbudget

def geometryAffineHighTarget (μ δ : ℝ) : ℝ :=
  -(720486667/30493190000000:ℝ)+4*μ-3*δ

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

/-- The coordinate ceiling B=130 preserves the literal shared first mass. -/
theorem geometry_affine_high_mass_rate (μ : ℝ) (Nbudget : ℕ) (hμ : 0<μ) :
    geometryFinalMassRate μ (geometryAffineHighDictionaryRate μ Nbudget) 130=
      geometryAffineHighDictionaryRate μ Nbudget :=
  geometry_affine_final_dictionary_mass_rate_eq μ 130 (3*((Nbudget:ℝ)+2)) Nbudget
    hμ (by norm_num) (by norm_num)

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
    (hzslot : (17/500:ℝ)≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤1/25)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
      Cycle63.Arithmetic.B)
    (hvolumeCell : Real.logb Z (volume s)≤Cycle63.Arithmetic.totalA
      (Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑j,Real.logb Z (s.P j)))))
    {Label : Type}[Fintype Label]
    (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
    let first:=fun l=>geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let amp:=(1:ℝ)*Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
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
        21/25≤bufferValue P.e (select r)),
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
  obtain ⟨K,hK,hc⟩:=actual_main_high_final_all_height_coarse (α:=α)
    η₀ u₀ F₀ R₀ hu₀ (Fintype.card α) rfl (bp:=9/4)
    130 (μ/8) δ δ Cs (9/4) (9/4) (Real.log 2) 1 1 (1/4) (μ/8) δ (μ/64) 3
    (by norm_num) (by positivity) hδ hδ hCs (by norm_num) (by norm_num)
    (Real.log_nonneg (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) hδ.le (by positivity) (by linarith) (by norm_num)
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
    21/25≤bufferValue P.e (select r))
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
  obtain ⟨degree,hext⟩:=geometry_extend_shifted_height_bound coarse target P.τ P.hτ 0
  refine ⟨degree,?_⟩
  intro Ks Kc hKs hKc η₀ Q hQM hQ72 Z hs hc
  unfold GeometryAffineHighSelectedCostSpec at hs hc ⊢
  intro hZ s p caps θ w σ freq hm hsη height mesh hw hwL hwr hmesh hwm hwmarked hσ hheight hfreq hT hβhi
    hzslot haff hvolumeCell Label _ reflected second bin t firstIndex first amp omega hamp0 hamp homega hf₁ hinj
    rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u hRange hP hPN canonical firstMass childSrc ordinary coefficient select
  let cost:=∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(ordinary l).block)=>21/25≤bufferValue P.e (select r)),
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
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤amp → 0≤reserve →
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

set_option maxHeartbeats 120000 in
/-- The density dictionary and degree precede the moving source, detector,
and common cutoff. The actual Fourier count is kept distinct from its budget. -/
theorem actual_affine_high_selected_small_height_of_fibers
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤94/125)
    (μ Cs : ℝ)(Nbudget : ℕ)(hμ : 0<μ)(hμcap : μ≤1/100000000)(hCs : 1≤Cs)
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
  have rates:=geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((Nbudget:ℝ)+2)) Nbudget
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hδ : 0<δ:=rates.1
  have hδsmall : δ≤μ/128:=rates.2.2.1
  have hL : 0≤3*((Nbudget:ℝ)+2):=by positivity
  have hUL : ((Fintype.card α:ℝ)+2)*3≤3*((Nbudget:ℝ)+2) := by
    have hn : (Fintype.card α:ℝ)≤Nbudget:=by exact_mod_cast hN
    linarith
  obtain ⟨bound,hbound,J,hsmall⟩:=actual_main_high_final_small_height (α:=α) (ap:=1/4) (bp:=9/4) M H hH
    η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta hMarkedUpper 130 130 (μ/8) δ μ (3*δ) (μ/32) (2*(μ/8))
    (by positivity) (by norm_num) (by norm_num) le_rfl (by norm_num) (by positivity) hδ (by norm_num)
    (Fintype.card α) 1 δ (μ/8) (μ/8) (by norm_num) hδ.le (by positivity) (by positivity)
    (3*((Nbudget:ℝ)+2)) δ 3 hL hδ (by norm_num) hUL
    Cs (9/4) (9/4) (Real.log 2) δ hCs (by norm_num) (by norm_num)
    (Real.log_nonneg (by norm_num)) hδ
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hsched hmarked hslot hplain hdensity
  obtain ⟨F,G,Ks,hF,hKs,he⟩:=hsmall (μ/8) P hboundeq hmarked hslot hplain
    (hdensity.trans (by linarith)) hdensity
  let Sp:=G∪{(0,0)}
  let amplitude : ℝ := (2*(9/4)*Cs^(Fintype.card α))^2
  have hampPositive : 0<amplitude:=by dsimp only [amplitude]; positivity
  -- The selected fiber constant is independent of the moving detector.
  obtain ⟨Cf,hCf,hfiber⟩:=fiberReceipt
  refine ⟨Sp,by simp [Sp],Ks*Cf*amplitude,by positivity,?_⟩
  intro Q hQM hQ72
  filter_upwards [he,
    eventually_actual_main_high_canonical_admission (α:=α) M H hH (excluded F₀.character R₀)
      (9/4) (9/4) (μ/8) (μ/64) P.τ P.e 28 P.bΦ
      (by norm_num) (by norm_num) (by positivity) (by linarith) (by positivity) (by linarith)
      P.hτ P.he (by norm_num) hsched.radial η₀,
    eventually_actual_main_high_literal_admission (α:=α) M H hH (excluded F₀.character R₀)
      (9/4) (9/4) (μ/8) (μ/64) P.τ P.e 28 P.bΦ
      (by norm_num) (by norm_num) (by positivity) (by linarith) (by positivity) (by linarith)
      P.hτ P.he (by norm_num) hsched.radial η₀,
    eventual_geometry_joint_support η₀ u₀ F₀ R₀ hu₀ (9/4) (μ/8) (Fintype.card α)
      (by norm_num) (by positivity),hfiber,
    eventual_geometry_small_frequency μ hμ,eventually_geometry_zero_heights P.e P.τ P.hτ]
    with Z he had hlit hjoint hfib hω hzero
  refine ⟨he.1,?_⟩
  unfold GeometryAffineHighSelectedCostSpec
  intro hZ s p caps θ w σ freq hm hsη height mesh hw hwL hwr hmesh hwm hwmarked hσ hheight hfreq hT hβhi
    hzslot haff hvolumeCell Label _ reflected second bin t firstIndex first amp omega hamp0 hamp homega hf₁ hinj
    rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u hSmall hP hPN canonical firstMass childSrc ordinary coefficient select
  let hKfirst:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let Original:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) t
    (Fintype.card α) hZ bin caps.zero₁ caps.zero₂
  let embed : rows→Original:=mainLowSelectedOriginal reflected s 1 1 Z 1 amp (μ/64) (μ/8) (9/4) t
    (Fintype.card α) hZ bin caps.zero₁ caps.zero₂ firstIndex
  let full : Original→SecondInputDatum α:=fun q=>geometryLowSecondDatum reflected s 1 1 Z 1 amp
    (μ/64) (μ/8) (9/4) t (Fintype.card α) hZ bin q.val.1 caps.zero₁ caps.zero₂ q.val.2
  let originalDatum : Original→SecondInputDatum α:=fun q=>ordinarySecondDatum (full q) χ₀ (internalQ Q η₀) m
  let firstOriginal:=fun q : Original=>geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (μ/64) hKfirst bin q.val.1.1.val
  let Live:=secondLiveRows (fun q=>(ordinary q).block)
  let row : Live→secondLiveRows (fun q=>(originalDatum q).block):=
    highSelectedLiveRowEmbedding originalDatum embed
  let highRows : Finset Live:=Finset.univ.filter (fun r=>21/25≤bufferValue P.e (select r))
  have hvol3 : volume s≤Z^(3:ℝ):=caps.volume.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  have hA4 : |Real.logb Z (volume s)|≤4:=caps.volumeLog.trans (by norm_num)
  have literal (q : Original):=hlit.2 hZ reflected second s hsη 1 amp (μ/8) t caps.endpoints
    squarefree_one caps.zero₁ caps.zero₂ caps.sourceCap hvol3 hamp0 (by positivity) hA4 hamp homega
    bin χ₀ (internalQ Q η₀) hQ72 m hm₀ hml hm₂ (inf_le_left.trans hQM) inf_le_right hbeta hβhi q
  obtain ⟨hPo,hPNo,keepo,selecto,hadmitted⟩:=had.2 hZ reflected second s hsη 1 amp (μ/8) t caps.endpoints
    squarefree_one caps.zero₁ caps.zero₂ caps.sourceCap hvol3 hamp0 (by positivity) hA4 hamp homega
    bin (fun _=>χ₀) (fun _=>internalQ Q η₀) (fun _=>hQ72) (fun _=>m) (fun _=>hm₀)
    (fun _=>hml) (fun _=>hm₂) (fun _=>inf_le_left.trans hQM) (fun _=>inf_le_right) hbeta hβhi
  obtain ⟨keep,hcanonical⟩:=actual_main_high_canonical_family_admission M H hH datum (fun _=>χ₀)
    (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z 28 P.bΦ hZ hsched.radial second hP hPN η₀
    (inf_le_left.trans hQM) inf_le_right P.e (Z^P.τ) P.he hT hbeta hβhi
  let ψ : Live→RayCharacter:=fun r=>if second then r.val.2.2.1⁻¹ else r.val.2.1
  let signed : Live→O:=fun r=>if second then -r.val.2.2.2.val else r.val.2.2.2.val
  let st : Live→NaturalState Z 28 P.bΦ:=fun r=>widenHighState
    (retainedState Z 28 hZ ((datum r.val.1).τ (ψ r)) (internalQ Q η₀)
      ((datum r.val.1).R*(if second then (datum r.val.1).D else (datum r.val.1).C))
      (hP r.val.1) (hPN r.val.1) (datum r.val.1).radius (datum r.val.1).C (datum r.val.1).D
      (datum r.val.1).inactive) P.bΦ hsched.radial
  have hwidth (r : Live) : (st r).width≤2 := by
    cases second <;> exact (hadmitted (row r)).1
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
  let hfirst : ∀r,firstOriginal (row r).val.1=geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z
      (μ/64) hKfirst bin (column r):=fun _=>rfl
  let hf:=fun r=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s 1 1 (Z^(1:ℝ)) Z
    (μ/64) hKfirst bin (column r) originalDatum firstOriginal (row r) (hfirst r)
  let rawKey:=fun r=>secondEncodedNonzeroRow (fun q=>(originalDatum q).block) firstOriginal (row r)
    left u₀ unit (hf r)
  let key:=fun r=>if second then reflectedNonzeroJointLabel (rawKey r) else rawKey r
  have hsupport (r : Live) : ((Ideal.span {jointSourceRow left u₀ unit (key r).val}*
      firstSourceMissing left (key r).val.1).absNorm:ℝ)≤Z^(130:ℝ) := by
    have hj:=hjoint hZ (ι:=α) (α:=α) (Label:=↥Original) reflected s 1 1 (Z^(1:ℝ))
      (μ/64) amp (μ/8) 1 3 hKfirst squarefree_one caps.zero₁ caps.zero₂ caps.sourceCap le_rfl
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
        (originalDatum (row r).val.1).inactive Z 1 (Real.logb Z (volume s)) amp (μ/64) (μ/8) (μ/8))
        (μ/8) 2+μ/32≤130 :=
    ((literal (row r).val.1).2.2.2.2 (μ/8) (μ/8) (μ/32)
      (by rw [abs_of_nonneg (by positivity : 0≤μ/8)]; linarith)
      (by linarith)).1
  have hnorm (r : Live) : ((originalDatum (row r).val.1).C.absNorm:ℝ)≤Z^(130:ℝ) ∧
      ((originalDatum (row r).val.1).D.absNorm:ℝ)≤Z^(130:ℝ) :=
    ⟨(literal (row r).val.1).2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)),
      (literal (row r).val.1).2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))⟩
  have hsupply : (17/500:ℝ)*1≤∑j,w j := by
    simpa only [hm.scale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',mul_one] using hzslot.1
  have hsupplyUpper : (∑j,w j)≤(1/25:ℝ) := by
    simpa only [hm.scale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hzslot.2
  have hcell:=Cycle63.Moment.originalCell_mem hzslot
  let bAmpl:=Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑j,Real.logb Z (s.P j)))
  have hbAmpl : 3401/100000≤bAmpl ∧ bAmpl≤1/25:=Cycle63.Arithmetic.cellUpper_bounds hcell.1 hcell.2.1
  have htotalA : Real.logb Z (volume s)≤1*Cycle63.Arithmetic.totalA bAmpl := by
    simpa only [one_mul] using hvolumeCell
  have hampCell : amp≤1*Cycle63.Arithmetic.amp bAmpl := by
    dsimp only [amp,bAmpl]
    rw [div_one]
  have hprofile : (p.control G)^2*amplitude≤(p.control Sp)^2*amplitude := by
    have hc:=CenteredMomentEnergyBandMonotonicity.profile_control_mono p (Finset.subset_union_left : G⊆Sp)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Profiles.control_nonneg _ _) hc _) hampPositive.le
  have hraw : δ+2*geometryFinalPlainRate μ 31*31+2*δ*31*(Fintype.card α:ℝ)≤μ/4 :=
    geometry_affine_high_actual_raw_budget μ (Fintype.card α) Nbudget hμ hN
  have hfinal : omega+μ/8+μ/8+4*(μ/32)+μ/8+μ/4+μ/4+130*δ+μ/8+
      130*δ+3*(3*((Nbudget:ℝ)+2))*δ+δ+2*(μ/8)≤4*μ-3*δ := by
    have hl:=geometry_final_main_high_consumer_ledger μ 31 3 4 3 130 (3*((Nbudget:ℝ)+2))
      omega (μ/4) (μ/4) Nbudget hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by positivity) hω.2.2 le_rfl le_rfl
    dsimp only at hl
    rw [geometry_affine_final_dictionary_mass_rate_eq μ 130 (3*((Nbudget:ℝ)+2)) Nbudget hμ (by norm_num) (by norm_num)] at hl
    change omega+μ/8+μ/8+4*(μ/32)+μ/8+μ/4+μ/4+130*δ+μ/8+
      130*δ+3*(3*((Nbudget:ℝ)+2))*δ+δ+2*(μ/8)+3*δ≤4*μ at hl
    linarith only [hl]
  let selectedFirst:=fun q : rows=>first q.val.1
  let hSelected : ∀r : Live,jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun q=>(ordinary q).block) selectedFirst r)≠0:=fun r=>
    actual_joint_first_frequency_ne_zero left u₀ unit
      (secondEncodedRow (fun q=>(ordinary q).block) selectedFirst r) hu₀ (Units.ne_zero _)
      (geometryFirstSource s 1 1 (Z^(1:ℝ)) Z (μ/64) hKfirst bin (firstIndex r.val.1.val.1).1.val.1).hC
  have hkeys (r : Live) : key r=
      (if second then reflectedNonzeroJointLabel
        (secondEncodedNonzeroRow (fun q=>(ordinary q).block) selectedFirst r left u₀ unit (hSelected r))
      else secondEncodedNonzeroRow (fun q=>(ordinary q).block) selectedFirst r left u₀ unit (hSelected r)) :=
    affine_high_selected_live_reflected_key originalDatum embed firstOriginal r left second u₀ unit (hf r) (hSelected r)
  have hFibers : ∀target,((Finset.univ.filter (fun r : highRows=>key r.val=target)).card:ℝ)≤Cf*Z^(2*(μ/8)) := by
    intro target
    have hh:=hfib hZ (Label:=Label) reflected s 1 1 1 amp (μ/8) t squarefree_one caps.endpoints hvol3 le_rfl
      caps.zero₁ caps.zero₂ hamp0 (by positivity) bin firstIndex hf₁ hinj χ₀ (internalQ Q η₀) m
      highRows second hSelected target
    change ((Finset.univ.filter (fun r : highRows=>
      (if second then reflectedNonzeroJointLabel
        (secondEncodedNonzeroRow (fun q=>(ordinary q).block) selectedFirst r.val left u₀ unit (hSelected r.val))
      else secondEncodedNonzeroRow (fun q=>(ordinary q).block) selectedFirst r.val left u₀ unit (hSelected r.val))=target)).card:ℝ)≤Cf*Z^(2*(μ/8)) at hh
    simpa only [hkeys] using hh
  by_cases hnonempty : Nonempty Live
  · let : Nonempty Live:=hnonempty
    have hbefore:=he.2 (κ:=↥Live) reflected second s hsη 1 1 Ψ 1 (μ/64) amp (μ/8) t hKfirst one_ne_zero hZ bin
      caps.zero₁ caps.zero₂ (fun _=>χ₀) (fun _=>internalQ Q η₀) (fun _=>m) row ψ bAmpl (μ/4) (μ/4)
      ((p.control Sp)^2*amplitude) Cf (div_nonneg hμ.le (by norm_num))
      (div_nonneg hμ.le (by norm_num)) (mul_nonneg (sq_nonneg _) hampPositive.le) hCf.le
      highRows hFibers select (fun r _=>hcoordinate r) squarefree_one
      (caps.sourceCap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))
      (by rw [caps.lower]) hbAmpl.1 hbAmpl.2 rfl (by norm_num) (by norm_num)
      (caps.volumeLog.trans (by norm_num)) (hamp.trans (by norm_num)) (homega.trans (by norm_num))
      (by linarith [hω.2.2]) (by linarith only [hμcap]) (by linarith only [hμ.le]) htotalA hampCell (fun r _=>hnorm r)
    let stP : Live→NaturalState Z P.Bmask P.bΦ:=fun r=>reboundAffineHighState (st r)
      (by simpa only [hsched.mask] using (st r).puncture_bound)
    have hb:=hbefore
      stP (fun _=>inf_le_left.trans hQM) (fun _=>inf_le_right) signed hkeep (fun _=>rfl) (fun _=>rfl)
      (fun _=>rfl) (fun r _=>hcanon r) (fun r hr=>(Finset.mem_filter.mp hr).2)
      (fun r _=>hsupport r) (fun r _=>hzero.2.2 (select r)) rfl caps.controls
      (by rw [caps.b₁]) (by rw [caps.b₂]) caps.endpoints.1 caps.windows
      t₀ u height w σ freq θ p 1 hheight hfreq hSmall
      (by rw [hsched.degree,hsched.plain]; norm_num)
      (by simpa only [hsched.slot,hsched.slotCap] using hm) hsupply hsupplyUpper caps.plainScales
      (by linarith only [hδsmall,hμ]) (fun r _=>by rw [hsched.retainedWidth]; exact hwidth r) (fun r _=>hradial r) hw hwmarked
      (fun j=>by simpa only [hsched.degree,hsched.width] using hwr j)
      (fun j=>by rw [hsched.sigmaLo]; exact (hσ j).1)
      (fun j=>by rw [hsched.sigmaHi]; exact (hσ j).2) caps.profile₁ caps.profile₂ caps.b₁ caps.b₂ caps.poolCap
      hprofile (by simpa only [hsched.plainRate,hsched.slotRate,hsched.degree] using hraw)
      (fun _ _=>rfl) hfinal
    have htarget : -(1:ℝ)*(720486667/30493190000000)+4*μ-3*δ=geometryAffineHighTarget μ δ := by
      unfold geometryAffineHighTarget
      ring
    rw [htarget] at hb
    change Z^(-amp)*(∑r∈highRows,∑L∈secondResidualIdeals (fun q=>(ordinary q).block) r.val,
      mainNormalizedPhysicalCost (Fintype.card α) 1 (1/4) second ordinary coefficient t₀ u r.val L)≤
      Ks*Cf*((p.control Sp)^2*amplitude)*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*Z^(geometryAffineHighTarget μ δ) at hb
    rw [geometry_main_high_physical_row_sum (Fintype.card α) 1 (1/4) second ordinary coefficient t₀ u highRows] at hb
    have hu:=geometry_affine_high_unamplify Z amp (geometryAffineHighTarget μ δ) _
      (Ks*Cf*((p.control Sp)^2*amplitude)*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin) (zero_lt_one.trans hZ) hb
    simp only [pow_zero,mul_one]
    convert hu using 1; ring
  · let : IsEmpty Live:=not_nonempty_iff.mp hnonempty
    have hs : 0<geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin :=
      geometry_high_factor_pos reflected _ bin
        (geometrySupportConstant_pos (Fintype.card α) 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))
    have hempty : highRows=∅:=Finset.eq_empty_of_isEmpty highRows
    change (∑r∈highRows,
      (coefficient r.val.1*((ordinary r.val.1).K/lowerFactor (Fintype.card α) 1 (1/4))*
        normalizer (ordinary r.val.1).C (ordinary r.val.1).D (ordinary r.val.1).inactive)*
      highNormalizedRowCost second ordinary r
        ((ordinary r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((ordinary r.val.1).block.divisors.filter Squarefree))≤_
    rw [hempty,Finset.sum_empty]
    simp only [pow_zero,mul_one]
    positivity

/-- Genuine all-height payment on the same inclusive canonical high rows.
The density dictionary precedes the cutoff and the moving detector. -/
theorem actual_affine_high_selected_all_height_of_fibers
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤94/125)
    (μ Cs : ℝ)(Nbudget : ℕ)(hμ : 0<μ)(hμcap : μ≤1/100000000)(hCs : 1≤Cs)
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
    η₀ u₀ F₀ R₀ hu₀ W hbeta P μ δ Cs (excluded F₀.character R₀) hμ (hμcap.trans (by norm_num)) hδ hCs
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
    (hlo₁ : (41/100:ℝ)≤length Z X₁)(hlo₂ : (41/100:ℝ)≤length Z X₂)
    (hhi₁ : length Z X₁≤(44/100:ℝ))(hhi₂ : length Z X₂≤(44/100:ℝ))
    (hslots : (17/500:ℝ)≤∑i,w i ∧ (∑i,w i)≤1/25)
    (hcone : length Z X₁+length Z X₂+Cycle63.Arithmetic.lambda*(∑i,w i)≤Cycle63.Arithmetic.B),
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_main_low_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_main_low_profile_zero p 1
    ∀{Label : Type}[Fintype Label]
    (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
    let first:=fun l=>geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let amp:=(1:ℝ)*Cycle63.Arithmetic.amp (Cycle63.Arithmetic.cellUpper
      (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
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
        21/25≤bufferValue P.e (select r)),
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
    hheight hfreq hT hβhi hlo₁ hlo₂ hhi₁ hhi₂ hslots hcone s hz₁ hz₂
    Label _ reflected second bin t firstIndex first amp omega hf₁ hinj
    rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u hP hPN canonical firstMass childSrc ordinary coefficient select
  have cap₀:=hcaps θ η₀ w σ freq hσ bΦ state p tplain X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots.2
  obtain ⟨caps,hm⟩:=actual_affine_low_source_gates M H hH η₀ θ W hW hWs w σ freq hσ state p
    tplain X₁ X₂ hX₁ hX₂ Cs hZ hw hslots.2 hhi₁ hhi₂ cap₀
  have hlogs : ∀j,Real.logb Z (s.P j)=w j := by
    intro j
    change Real.logb Z (Z^(w j))=w j
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hsum : (∑j,Real.logb Z (s.P j))=∑j,w j := Finset.sum_congr rfl (fun j _=>hlogs j)
  have hηs : s.η=ηseed:=hη
  have hw₁ (j : α) : w j≤1 :=
    (Finset.single_le_sum (fun i _=>hw i) (Finset.mem_univ j)).trans (hslots.2.trans (by norm_num))
  have hwr (j : α) : w j/31≤1 := by linarith only [hw₁ j]
  have hcell:=Cycle63.Moment.originalCell_mem hslots
  have hbetaCell:=Cycle63.Arithmetic.cellUpper_bounds hcell.1 hcell.2.1
  have hamp0 : 0≤amp := by
    simpa only [amp,hsum,div_one,one_mul] using (Cycle63.Arithmetic.amp_pos hbetaCell).le
  have hamp : |amp|≤4 := by
    rw [abs_of_nonneg hamp0]
    have h:= (Cycle63.Arithmetic.amp_bounds hbetaCell).2.trans
      (by norm_num : (226566043/17233200000:ℝ)≤4)
    simpa only [amp,hsum,div_one,one_mul] using h
  have homega : |omega|≤4 := by
    rw [abs_of_nonneg hω.1]
    exact hω.2.trans (by linarith only [hμcap])
  have hvolume:=actual_affine_exceptional_volume_cell M H hH η₀ θ W hW hWs w σ freq hσ
    state p tplain X₁ X₂ hX₁ hX₂ hZ hlo₁ hlo₂ hslots hcone
  unfold GeometryAffineHighSelectedCostSpec at hspec
  have hb:=hspec hZ s p caps θ w σ freq hm hηs height mesh hw
    (fun j=>(hwm j).trans hmeshcap) hwr hmesh hwm hwmarked hσ hheight hfreq hT hβhi
    (by simpa only [hsum] using hslots) (by
      change length Z X₁+length Z X₂+Cycle63.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle63.Arithmetic.B
      simpa only [hsum] using hcone)
    (by simpa only [hsum] using hvolume)
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

/-- Actual high payment with its supported selected fibers proved internally. -/
theorem actual_affine_high_selected_small_height
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤94/125)
    (μ Cs : ℝ)(Nbudget : ℕ)(hμ : 0<μ)(hμcap : μ≤1/100000000)(hCs : 1≤Cs)
    (hN : Fintype.card α≤Nbudget) :
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
  exact actual_affine_high_selected_small_height_of_fibers (α:=α) M H hH η₀ u₀ F₀ R₀ hu₀
    W hWs hW hbeta hMarkedUpper μ Cs Nbudget hμ hμcap hCs hN
    (geometry_affine_high_selected_fiber_receipt (α:=α) η₀ u₀ F₀ R₀ hu₀ μ hμ)

/-- Actual high payment with its supported selected fibers proved internally. -/
theorem actual_affine_high_selected_all_height
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤94/125)
    (μ Cs : ℝ)(Nbudget : ℕ)(hμ : 0<μ)(hμcap : μ≤1/100000000)(hCs : 1≤Cs)
    (hN : Fintype.card α≤Nbudget) :
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
  exact actual_affine_high_selected_all_height_of_fibers (α:=α) M H hH η₀ u₀ F₀ R₀ hu₀
    W hWs hW hbeta hMarkedUpper μ Cs Nbudget hμ hμcap hCs hN
    (geometry_affine_high_selected_fiber_receipt (α:=α) η₀ u₀ F₀ R₀ hu₀ μ hμ)

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_high_actual_raw_budget
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_high_mass_rate

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_high_selected_coarse

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_high_schedule_gates

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_high_selected_small_height_of_fibers
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_high_selected_all_height_of_fibers

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_high_unamplify
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_high_amplify
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_high_selected_cost_mono
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_high_selected_height_splice

#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_main_high_spec_of_receipts

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_high_selected_fiber_receipt

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_high_selected_small_height

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_affine_high_selected_all_height
