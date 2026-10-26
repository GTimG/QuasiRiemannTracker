/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainHighParameters
/- Actual HIGH transport adapted from Hailey Collet and accepted PR60; Apache-2.0.
Private .874836 proof components. No completed endpoint is asserted. -/
import Candidate.Uneven.AuxiliaryAffineLowPayment
import Candidate.Uneven.UnevenMassMonotonicity
import Candidate.Uneven.BootstrapSchedule
import Candidate.Uneven.MainCellGeometry
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
set_option maxHeartbeats 800000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.MainHigh
open TargetHigh830 SaturatedPlain BootstrapPlain
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
variable (plane : Sil.Uneven.MainSource.Plane)



/-- The shared rate uses the ambient budget; Fourier data retain the actual count. -/
def geometryAffineHighDictionaryRate (μ : ℝ) (Nbudget : ℕ) : ℝ :=
  geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((Nbudget:ℝ)+2)) Nbudget

def geometryAffineHighTarget (μ δ : ℝ) : ℝ :=
  -(mainHighReserve:ℝ)+4*μ-3*δ

def geometryAffineHighCoarseExponent (μ δ : ℝ) (N : ℕ) : ℝ :=
  130+(39*(130+μ/8)+(130+μ/8)*δ+(130+μ/8)*δ+μ/8)+
    8*(130+μ/8)+3*(μ/8)+((N:ℝ)+2)*1+2*δ+3*(((N:ℝ)+2)*3)*δ+130

/-- The actual slot count pays the same ambient raw-error budget. -/
theorem geometry_affine_high_actual_raw_budget (μ : ℝ) (N Nbudget : ℕ)
    (hμ : 0< μ) (hN : N≤ Nbudget) :
    let δ:=geometryAffineHighDictionaryRate μ Nbudget
    δ+2*geometryFinalPlainRate μ 31*31+2*δ*31*(N:ℝ)≤ μ/4 := by
  intro δ
  have hb:=geometry_final_dictionary_budgets μ 31 3 4 3 130 (3*((Nbudget:ℝ)+2)) Nbudget
    hμ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  have hactual : (N:ℝ)≤ Nbudget := by exact_mod_cast hN
  have hslots:=mul_le_mul_of_nonneg_left hactual (show 0≤2*δ*31 by
    have hd : 0< δ:=hb.1
    positivity)
  have hδ : δ≤ μ/128:=hb.2.2.1
  have hplain:=hb.2.2.2.2.2.2.2.1
  have hraw:=hb.2.2.2.2.2.2.2.2
  change μ/16+2*31*geometryFinalPlainRate μ 31+2*31*(Nbudget:ℝ)*δ≤ μ/4 at hraw
  nlinarith only [hslots,hδ,hraw,hμ]


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
    (hwmarked : ∀j,w j≤ bootstrapRawMesh*fineRawCore)
    (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0≤ height)(hfreq : ∀j,|freq j|≤ height)(hT : 2< Z^P.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hzslot : (17/500:ℝ)≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤1/25)
    (haff : length Z s.X₁+length Z s.X₂+plane.lambda*(∑j,Real.logb Z (s.P j))≤
      plane.B)
    (hvolumeCell : Real.logb Z (volume s)≤ Sil.Uneven.MainSource.total plane
      (Sil.Uneven.MainSource.widthCellUpper (∑j,Real.logb Z (s.P j))))
    {Label : Type}[Fintype Label]
    (reflected second : Bool)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
    let first:=fun l=>geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let amp:=(1:ℝ)*Sil.Uneven.MainSource.amp plane (Sil.Uneven.MainSource.widthCellUpper ((∑j,Real.logb Z (s.P j))/(1:ℝ)))
    let omega:=frequencyLoss Z 32 (μ/64)+μ/8
    ∀(hamp0 : 0≤ amp)(hamp : |amp|≤4)(homega : |omega|≤4)
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
    ∀hPN : ∀r,((((datum r).R*(if second then (datum r).D else (datum r).C)).absNorm:ℝ))≤ Z^(28:ℝ),
    let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
      AuxiliaryPhysical.mainLowCanonicalSelector M H hH (datum r) χ₀ χ ψ (internalQ Q η₀) hQ72
        m hm₀ hml hm₂ Z 28 hZ second (hP r) (hPN r) η₀
        (inf_le_left.trans hQM) inf_le_right P.e (Z^P.τ) P.he hT hbeta hβhi
    let firstMass:=fun l=>unevenFirstHighMass reflected s 1 1 Ψ 1 Z (μ/64) δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
    let childSrc:=fun l=>geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
    let ordinary:=fun r=>ordinarySecondDatum (datum r) χ₀ (internalQ Q η₀) m
    let coefficient:=fun r=>firstMass r.val.1/volume (childSrc r.val.1)
    let select:=mainPhysicalFamilySelector second ordinary canonical
    (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(ordinary l).block)=>
        (1+plane.q)/2≤ bufferValue P.e (select r)),
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
    (hZ : 0< Z) (h : Z^(-amp)*cost≤ K*Z^exponent) :
    cost≤ K*Z^(amp+exponent) := by
  calc
    cost=Z^amp*(Z^(-amp)*cost) := by
      rw [←mul_assoc,←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero,one_mul]
    _≤ Z^amp*(K*Z^exponent) := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hZ.le _)
    _=K*Z^(amp+exponent) := by rw [Real.rpow_add hZ]; ring

/-- The physical coarse estimate on the literal selected high carrier. Its
exponent is coarse and contains no high saving. -/
theorem actual_affine_high_selected_coarse 
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (P : HighSourceParameters)(μ δ Cs : ℝ)(ηseed : Character)
    (hμ : 0< μ)(_hμcap : μ≤1/128)(hδ : 0< δ)(hCs : 1≤ Cs) :
    ∃K : ℝ,0< K ∧ ∀(Q : Ideal O)(hQM : Q≤ M)
      (hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}),∀ᶠZ : ℝ in atTop,
      2≤ Z ∧ GeometryAffineHighSelectedCostSpec (α:=α) M H hH plane W hbeta P μ δ
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
    (1+plane.q)/2≤ bufferValue P.e (select r))
  have hb:=hc hZ (Label:=Label) reflected s 1 1 1 amp (μ/8) t hKfirst squarefree_one caps.endpoints
    (by rw [caps.lower])
    (caps.sourceCap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))
    (caps.volumeLog.trans (by norm_num)) (by norm_num) (hamp.trans (by norm_num))
    (homega.trans (by norm_num)) caps.controls caps.windows caps.plainScales caps.primeScales
    caps.poolCap caps.support₁ caps.support₂ caps.zero₁ caps.zero₂ hamp0 (by positivity)
    bin firstIndex hinj hf₁ (fun _=>χ₀) (fun _=>internalQ Q η₀) (fun _=>m)
    highRows second Ψ t₀ u p {(0,0)} (by simp) caps.profile₁ caps.profile₂
  let oldcoefficient := fun r : rows=>geometryFirstHighMass reflected s 1 1 Ψ 1 Z (μ/64) δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex r.val.1).1.val /
      volume (childSrc r.val.1)
  change Z^(-amp)*(∑r∈highRows,∑L∈secondResidualIdeals (fun q=>(ordinary q).block) r.val,
    mainNormalizedPhysicalCost (Fintype.card α) 1 (1/4) second ordinary oldcoefficient t₀ u r.val L)≤
    K*(p.control {(0,0)})^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
      Z^(geometryAffineHighCoarseExponent μ δ (Fintype.card α)) at hb
  rw [geometry_main_high_physical_row_sum (Fintype.card α) 1 (1/4) second ordinary oldcoefficient t₀ u highRows] at hb
  have hh:=geometry_affine_high_unamplify Z amp (geometryAffineHighCoarseExponent μ δ (Fintype.card α))
    _ (K*(p.control {(0,0)})^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin) (zero_lt_one.trans hZ) hb
  have hcomp : ∀r : rows, coefficient r ≤ oldcoefficient r := by
    intro r
    apply div_le_div_of_nonneg_right _ (CenteredMomentExceptionalAmplitudePair.volume_pos _).le
    dsimp only [firstMass,oldcoefficient]
    exact uneven_first_high_mass_le reflected s 1 1 Ψ 1 Z (μ/64) δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex r.val.1).1.val hZ
  apply le_trans _ (by simpa only [pow_zero,mul_one] using hh)
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · apply mul_le_mul_of_nonneg_right (hcomp r.val.1)
      exact div_nonneg (ordinary r.val.1).K_pos.le (lowerFactor_pos (Fintype.card α) 1 (1/4) (by norm_num) (by norm_num)).le
    · exact (normalizer_pos (ordinary r.val.1).C (ordinary r.val.1).D (ordinary r.val.1).hC (ordinary r.val.1).inactive).le
  · exact high_normalized_row_cost_nonneg _ _ _ _ _

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

theorem geometry_affine_high_schedule_gates
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (μ bΦ τ : ℝ)(Nbudget : ℕ)(bound : ℕ→ℝ)
    (hμ : 0< μ)(hbΦ : 2≤ bΦ)(hτ : 0< τ)(hbound : ∀k,0≤ bound k) :
    GeometryAffineHighScheduleGates W μ (geometryAffineHighDictionaryRate μ Nbudget)
      (geometryAffineFinalHighSchedule W hWs hW μ 130 (3*((Nbudget:ℝ)+2)) bΦ τ Nbudget bound
        hμ (by norm_num) (by positivity) (by linarith) hτ hbound) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,hbΦ,rfl,rfl,rfl,rfl⟩


/-- A larger physical profile-control set pays the same exact carrier. -/
theorem geometry_affine_high_selected_cost_mono 
    (W : ℝ→ℂ)(hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (P : HighSourceParameters)(μ δ target : ℝ)(range : ℝ→ℝ→ℝ→ℝ→ℝ→Prop)
    (ηseed : Character)(Cs : ℝ)(S S₁ : Finset (ℕ×ℕ))(degree : ℕ)(K : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
    (Z : ℝ)(hK : 0≤ K)(hS : S⊆S₁)
    (hspec : GeometryAffineHighSelectedCostSpec (α:=α) M H hH plane W hbeta P μ δ target range ηseed Cs
      S degree K η₀ Q hQM hQ72 Z) :
    GeometryAffineHighSelectedCostSpec (α:=α) M H hH plane W hbeta P μ δ target range ηseed Cs
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
  have hside : 0≤ geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin :=
    (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos (Fintype.card α) 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  have hscalar : 0≤ K*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*
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
    (hZ : 0< Z) (h : cost≤ K*Z^(amp+exponent)) :
    Z^(-amp)*cost≤ K*Z^exponent := by
  calc
    _≤ Z^(-amp)*(K*Z^(amp+exponent)) := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hZ.le _)
    _=K*Z^exponent := by
      rw [Real.rpow_add hZ]
      calc
        _=K*(Z^(-amp)*Z^amp)*Z^exponent := by ring
        _=_ := by rw [←Real.rpow_add hZ,neg_add_cancel,Real.rpow_zero,mul_one]

/-- Splice the two checked selected-cost contracts at the actual combined
Mellin height, and keep the separate polynomial weights for both integrals. -/
theorem geometry_affine_high_selected_height_splice 
    (W : ℝ→ℂ)(hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (P : HighSourceParameters)(μ δ target coarse : ℝ)(ηseed : Character)(Cs : ℝ)
    (Sp : Finset (ℕ×ℕ)) :
    ∃degree : ℕ,∀(Ks Kc : ℝ)(_hKs : 0≤ Ks)(_hKc : 0≤ Kc)
      (η₀ : Character)(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)})
      (Z : ℝ),
      GeometryAffineHighSelectedCostSpec (α:=α) M H hH plane W hbeta P μ δ target
        (fun Z t height t₀ u=>|t|+height+2*Real.pi*(|u|+|t₀|)≤ Z^P.τ) ηseed Cs Sp 0 Ks η₀ Q hQM hQ72 Z →
      GeometryAffineHighSelectedCostSpec (α:=α) M H hH plane W hbeta P μ δ coarse
        (fun _ _ _ _ _=>True) ηseed Cs Sp 0 Kc η₀ Q hQM hQ72 Z →
      GeometryAffineHighSelectedCostSpec (α:=α) M H hH plane W hbeta P μ δ target
        (fun _ _ _ _ _=>True) ηseed Cs Sp degree ((2+4*Real.pi)^degree*(Ks+Kc)) η₀ Q hQM hQ72 Z := by
  obtain ⟨degree,hext⟩:=geometry_extend_shifted_height_bound coarse target P.τ P.hτ 0
  refine ⟨degree,?_⟩
  intro Ks Kc hKs hKc η₀ Q hQM hQ72 Z hs hc
  unfold GeometryAffineHighSelectedCostSpec at hs hc ⊢
  intro hZ s p caps θ w σ freq hm hsη height mesh hw hwL hwr hmesh hwm hwmarked hσ hheight hfreq hT hβhi
    hzslot haff hvolumeCell Label _ reflected second bin t firstIndex first amp omega hamp0 hamp homega hf₁ hinj
    rows datum χ₀ m hm₀ hml hm₂ Ψ t₀ u hRange hP hPN canonical firstMass childSrc ordinary coefficient select
  let cost:=∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(ordinary l).block)=>(1+plane.q)/2≤ bufferValue P.e (select r)),
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
  have hsmall : 2*(1+|t|+height+2*Real.pi*(|t₀|+|u|))≤ Z^P.τ →
      Z^(-amp)*cost≤ Ks*((p.control Sp)^2*side)*Z^target*
        (2*(1+|t|+height+2*Real.pi*(|t₀|+|u|)))^0 := by
    intro hh
    have hcombined : |t|+height+2*Real.pi*(|u|+|t₀|)≤ Z^P.τ := by
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
    (hbound : (st.puncture.absNorm:ℝ)≤ Z^Bmask') : NaturalState Z Bmask' bΦ :=
  {st with puncture_bound:=hbound}

end
end OAI.SevenEighths.MainHigh


