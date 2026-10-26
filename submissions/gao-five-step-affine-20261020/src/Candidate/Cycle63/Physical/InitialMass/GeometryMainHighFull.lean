import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighSelected
import Candidate.Cycle63.Physical.InitialMass.GeometryMainBufferedPartition
import Candidate.Cycle63.Physical.InitialMass.GeometryMainOrdinaryFiber
import Candidate.Cycle63.Physical.InitialMass.GeometryHighCoarseGates
import Candidate.Cycle63.Moment.HighParameters
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open Cycle63MarkedPlain
open scoped ContDiff
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

variable [Cycle63.AffineLedger] in
/-- Widening the radial ceiling preserves the actual whole-family bin,
including its original keep witness and both buffered height intervals. -/
theorem main_high_widen_zero_bin {Z Bmask : ℝ} (st : NaturalState Z Bmask 2)
    (bΦ : ℝ) (hbΦ : 2≤bΦ) (η₀ : Character)
    (hQM : st.fixedModulus≤M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e)
    (hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p) :
    GeometryZeroBin M H hH (widenHighState st bΦ hbΦ) η₀ hQM hQη z hz e T p := by
  exact hbin

variable [Cycle63.AffineLedger] in
/-- Every complete ordinary row has one literal bin before residual ideals
are grouped. The enlarged support ceiling keeps the actual unit-weight
profile and the same signed physical frequency. -/
theorem actual_main_high_widened_selector
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→SecondInputDatum α) (χ₀ : Label→RayCharacter) (Q : Ideal O)
    (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask bΦ : ℝ) (hZ : 1<Z) (hbΦ : 2≤bΦ) (second : Bool)
    (hP : ∀l,(d l).R*(if second then (d l).D else (d l).C)≠0)
    (hPN : ∀l,(((d l).R*(if second then (d l).D else (d l).C)).absNorm:ℝ)≤Z^Bmask)
    (η₀ : Character) (hQM : Q≤M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let ordinary:=fun l=>ordinarySecondDatum (d l) (χ₀ l) Q m
    let rows:=secondLiveRows (fun l=>(ordinary l).block)
    let signed:=fun r : rows=>mainLowSignedRow second r.val.2.2.2.val
    let base:=fun r : rows=>retainedState Z Bmask hZ
      (if second then (d r.val.1).τ r.val.2.2.1⁻¹ else (d r.val.1).τ r.val.2.1) Q
      ((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C))
      (hP r.val.1) (hPN r.val.1)
      (d r.val.1).radius (d r.val.1).C (d r.val.1).D (d r.val.1).inactive
    let st:=fun r=>widenHighState (base r) bΦ hbΦ
    ∃keep : ∀r : rows,(st r).radial.keep (signed r),
    ∃select : rows→BufferIndex e,∀r : rows,
      1≤((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re ∧
      (st r).radial.profile (normValue (signed r)/(st r).radial.scale)≠0 ∧ signed r≠0 ∧
      GeometryZeroBin M H hH (st r) η₀ hQM hQη (signed r) (keep r) e T (select r) := by
  intro ordinary rows signed base st
  obtain ⟨keep,select,hs⟩:=actual_main_buffered_row_selector M H hH d χ₀ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN η₀ hQM hQη e T he hT hβlo hβhi
  refine ⟨keep,select,?_⟩
  intro r
  have hweight:1≤((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re:=(hs r).1
  have hnonzero:(st r).radial.profile (normValue (signed r)/(st r).radial.scale)≠0:=by
    intro hzero
    rw [hzero] at hweight
    norm_num at hweight
  exact ⟨hweight,hnonzero,(st r).row_ne_zero _ (keep r),
    main_high_widen_zero_bin M H hH (base r) bΦ hbΦ η₀ hQM hQη (signed r) (keep r)
      e T (select r) (hs r).2.1⟩

theorem main_high_common_target (β omega εfreq εvolume : ℝ)
    (hβ : ((1+Cycle63.Arithmetic.q0)/2)≤β)(hβ' : β≤7/8)(hω : 0≤omega)(hε : 0≤εfreq) :
    (1-unmarkedDensity (2*β-1))*omega+unmarkedDensity (2*β-1)*εfreq+εvolume≤
      omega+εfreq+εvolume := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have hρ:=unmarkedDensity_le_one (δ:=2*β-1) (by linarith) (by linarith)
  have hρ₀:0≤unmarkedDensity (2*β-1):=le_trans (by norm_num)
    (unmarkedDensity_ge_two_sevenths (by linarith : 2*β-1≤3/4))
  have ho:=mul_le_mul_of_nonneg_right (by linarith : 1-unmarkedDensity (2*β-1)≤1) hω
  have he:=mul_le_mul_of_nonneg_right hρ hε
  linarith

private theorem main_high_height_target_payment (Z c height t tmax rest loss : ℝ)
    (hZ : 1≤Z)(hc : 0≤ c)(_hh : 0≤height)(hheight : height≤Z^loss)(ht : t≤tmax) :
    c*height*Z^(t+rest)≤ c*Z^(tmax+rest+loss) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  calc
    _≤ c*(Z^loss)*Z^(tmax+rest) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hheight hc
      · exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
      · exact Real.rpow_nonneg hz.le _
      · exact mul_nonneg hc (Real.rpow_nonneg hz.le _)
    _=c*Z^(tmax+rest+loss) := by
      rw [mul_assoc,←Real.rpow_add hz]
      rw [show loss+(tmax+rest)=tmax+rest+loss by ring]

/-- The genuine selected high estimate has a common exponent on every high zero bin. Its density-height polynomial is
paid by a loss chosen after the fixed density degree and before the moving sources. Without payment data the bound is
the transport form; with the cell payment data it is paid. -/
theorem actual_geometry_main_high_uniform_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (B Q loss ε : ℝ) (hB : 0≤B) (hQ : 0≤Q) (hQB : Q≤B) (hQmax : Q≤130)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0<lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀heightloss : ℝ,∀P : HighSourceParameters,P.profileBound=bound →
      MarkedSchedule P N Wslot (33/50) (33/50) →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      2*P.τ*((J:ℝ)+1)≤Cycle63.Optimization.geometryLossCap/8 → 2*P.τ*(J+1)≤heightloss →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn Cmove : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧ 0<Kcolumn ∧ 0<Cmove ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0<Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (β ampExponent reserveShift rawError allowance Kcontrol T width Wfiber : ℝ) (i : ℕ),
      ((1+Cycle63.Arithmetic.q0)/2) ≤ β → β ≤ 7/8 → 0≤ξ → 0≤ reserveShift → 0 ≤ Kcontrol → 1 ≤ T → 0<width →
      0≤Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ)≤Wfiber) →
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      (∀l∈labels,x l 2+width≤Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B → lo≤ s.lower →
      ξ≤εfreq →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,(datum (row l).val.1).radius=frequencyRadius
        (firstMainFourierScale reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent)
          reserveShift b N (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) Z ξ) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, β ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      i≤bufferCount P.e →
      (∀l∈labels,β≤geometryRowMaximum M H hH (st l) η₀ (hQM l) (hQη l)
        (z l) (hz l) ((3*i:ℕ)*Z^P.τ)) →
      (i:ℝ)≤Z^P.τ →
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      s.b₁≤bs → s.b₂≤bs → s.upper≤b →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
      let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
      let χ₁:=fun l=>geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l)
      ∀(B₁ : ∀l,actualAllocations s.pools (C₁ l))(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0) →
      let firstChild:=fun l=>child s (C₁ l) R (B₁ l) (χ₁ l) (t₁ l)
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      ∀(seed₂ : κ→ Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap : ℝ),
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      pad≤allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width≤P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<β+2*P.e) →
      (∀j,0≤w j) →
      (∀j,w j/P.d≤P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      ∀(t₀ u : ℝ),
      (∀l∈labels,(datum (row l).val.1).slots=liveIndices (B₁ l).val) →
      (∀l∈labels,HEq (datum (row l).val.1).input (firstChild l)) →
      (∀l∈labels,(datum (row l).val.1).K=firstMainRadius reflected (Z^D) (volume s) Z ξ
        (3*ampExponent) reserveShift (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) →
      (∀l∈labels,seed₂ l=(datum (row l).val.1).seed) →
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      (∀l∈labels,t l=(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))) →
      ∀pay : Option (HighCellPayment η₀ u₀ F₀ R₀ Z s D ξ ampExponent reserveShift εfreq B w),
      Z^(-ampExponent)*(∑l∈labels,∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)≤
      pay.elim
        ((1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
          geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*εmass)*
          keyBinnedCount labels key (fun l=>compensatedHighCoordinates (x l) (geometryHighSide reflected A
            (geometryExponents s R seed (Z^D) Z ξ (column l).1.val))) width
            (fun k=>Cmove*Kcontrol*(2*T)^(2*ε)*
              Z^(exponentBinUpper width k 0+(2*β-1)*exponentBinUpper width k 3+rawError+allowance))))))
        (fun _=>(1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
          Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(Cycle63.Arithmetic.lowReserve)+4*width+loss+rawError+allowance+B*εmass+heightloss)))))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_main_high_selected_shell (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  obtain ⟨F,G,Cprofile,C,Kcolumn,Cmove,hF,hCprofile,hC,hKcolumn,hCmove,hjoint⟩:=
    hhigh P hboundeq hmarked hslot hplain hmarkedHeight
  refine ⟨F,G,Cprofile,C,Kcolumn,Cmove,hF,hCprofile,hC,hKcolumn,hCmove,?_⟩
  filter_upwards [hjoint,eventually_high_truncated_heights P J heightloss hslot hplain hdensity] with Z he hhgt
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift rawError allowance Kcontrol T width Wfiber i
    hβ hβ' hξ hreserve hKcontrol hT hwidthbin hWfiber labels hfiber A x hq hseed hs₁ hs₂ hsource hlower
    hξε hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow
    hseed₂ hwidth hradial hzeroUpper hw hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
    t₀ u hslots hinput hKm hseedid hψ hshift pay
  let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
    unmarkedDensity (2*β-1)*εfreq+εvolume
  have hh:=he.2 reflected second s R seed W D ξ hK bin column datum first row
    hparent hfirst hR ψ β ampExponent reserveShift rawError allowance Kcontrol T width Wfiber i
    hβ hβ' hKcontrol hT hwidthbin hWfiber labels hfiber hq hseed hs₁ hs₂ hsource hlower
    hξε hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hM hb₁ hb₂ hupper hwin
    B₁ t₁ hf₁ seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow hseed₂ hwidth hradial
    hzeroUpper hw hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
    t₀ u hslots hinput hKm hseedid hψ hshift pay
  rcases pay with _ | _
  · exact hh
  dsimp only [Option.elim] at hh ⊢
  have hZ : 1≤Z:=by linarith [he.1]
  have htarget:=main_high_common_target β (frequencyLoss Z 32 ξ+reserveShift) εfreq εvolume
    hβ hβ' (add_nonneg (frequencyLoss_nonneg Z 32 ξ hhgt.1 (by norm_num) hξ) hreserve) hεfreq.le
  let c:=C*Cprofile^2*Kcontrol*(2*T)^(2*ε)
  let rest:=-D*(Cycle63.Arithmetic.lowReserve)+4*width+loss+rawError+allowance+B*εmass
  let tmax:=frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume
  have hpayment:=main_high_height_target_payment Z c ((1+3*(i+1:ℕ)*Z^P.τ)^J)
    target tmax rest heightloss hZ (by dsimp only [c]; positivity) (by positivity) (hhgt.2 i hi).2.2 htarget
  let pref:=(1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
    geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ))))
  have hfactor:= (geometry_high_factor_pos reflected (geometrySupportConstant N lo ap ap) bin
    (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
  have hlowerpos:0<lowerFactor N lo ap:=lowerFactor_pos N lo ap hlo hap
  have hZ0:0≤Z:=(by norm_num : (0:ℝ)≤2).trans he.1
  have hT0:0≤2*T:=mul_nonneg (by norm_num) (zero_le_one.trans hT)
  have hfront:0≤Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε):=
    mul_nonneg (mul_nonneg (mul_nonneg hKcolumn.le (Real.rpow_nonneg hT0 _))
      (pow_nonneg (zero_le_one.trans hCs) _)) (Real.rpow_nonneg hZ0 _)
  have hpref:0≤pref:=mul_nonneg (one_div_nonneg.mpr hlowerpos.le)
    (mul_nonneg hWfiber (mul_nonneg hfront (mul_nonneg hfactor (Nat.cast_nonneg _))))
  refine hh.trans ?_
  have he₁:target-D*(Cycle63.Arithmetic.lowReserve)+4*width+loss+rawError+allowance+B*εmass=
      target+rest:=by dsimp only [rest]; ring
  have he₂:frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(Cycle63.Arithmetic.lowReserve)+
      4*width+loss+rawError+allowance+B*εmass+heightloss=tmax+rest+heightloss:=by
    dsimp only [tmax,rest]; ring
  rw [he₁,he₂]
  convert mul_le_mul_of_nonneg_left hpayment hpref using 1 <;>
    dsimp only [pref,c] <;> ring

variable [Cycle63.AffineLedger] in
/-- A single literal buffered selector partitions the finite high family. The genuine analytic bound is summed with
only the fixed buffer count; physical first scalar mass and each residual projector stay inside the cost. Without
payment data the bound is the sum over the buffer bins of the transport forms of the rows of the bin; with the cell
payment data it is paid. -/
theorem actual_geometry_main_high_buffered_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤Cycle63.Optimization.plainCapacityCost)
    (B Q loss ε : ℝ) (hB : 0≤B) (hQ : 0≤Q) (hQB : Q≤B) (hQmax : Q≤130)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0<lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀heightloss : ℝ,∀P : HighSourceParameters,P.profileBound=bound →
      MarkedSchedule P N Wslot (33/50) (33/50) →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      2*P.τ*((J:ℝ)+1)≤Cycle63.Optimization.geometryLossCap/8 → 2*P.τ*(J+1)≤heightloss →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn Cmove : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧ 0<Kcolumn ∧ 0<Cmove ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0<Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
        (row : κ→secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (ampExponent reserveShift rawError allowance Kcontrol T width Wfiber : ℝ),
      0≤ξ → 0≤ reserveShift → 0 ≤ Kcontrol → 1 ≤ T → 0<width →
      0≤Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ)≤Wfiber) →
      ∀select : κ→BufferIndex P.e,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      (∀l∈labels,x l 2+width≤Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B → lo≤ s.lower →
      ξ≤εfreq →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,(datum (row l).val.1).radius=frequencyRadius
        (firstMainFourierScale reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent)
          reserveShift b N (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) Z ξ) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀l∈labels,GeometryZeroBin M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        P.e (Z^P.τ) (select l)) →
      (∀l∈labels,((1+Cycle63.Arithmetic.q0)/2)≤bufferValue P.e (select l)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (∀l∈labels,((select l).1.val:ℝ)≤Z^P.τ) →
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      s.b₁≤bs → s.b₂≤bs → s.upper≤b →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
      let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
      let χ₁:=fun l=>geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l)
      ∀(B₁ : ∀l,actualAllocations s.pools (C₁ l))(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0) →
      let firstChild:=fun l=>child s (C₁ l) R (B₁ l) (χ₁ l) (t₁ l)
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      ∀(seed₂ : κ→ Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap : ℝ),
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      pad≤allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width≤P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀j,0≤w j) →
      (∀j,w j/P.d≤P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      ∀(t₀ u : ℝ),
      (∀l∈labels,(datum (row l).val.1).slots=liveIndices (B₁ l).val) →
      (∀l∈labels,HEq (datum (row l).val.1).input (firstChild l)) →
      (∀l∈labels,(datum (row l).val.1).K=firstMainRadius reflected (Z^D) (volume s) Z ξ
        (3*ampExponent) reserveShift (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) →
      (∀l∈labels,seed₂ l=(datum (row l).val.1).seed) →
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      (∀l∈labels,t l=(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))) →
      ∀pay : Option (HighCellPayment η₀ u₀ F₀ R₀ Z s D ξ ampExponent reserveShift εfreq B w),
      Z^(-ampExponent)*(∑l∈labels,∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)≤
      pay.elim
        (∑q : BufferIndex P.e,(1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
          geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*εmass)*
          keyBinnedCount (labels.filter (fun l=>select l=q)) key
            (fun l=>compensatedHighCoordinates (x l) (geometryHighSide reflected A
              (geometryExponents s R seed (Z^D) Z ξ (column l).1.val))) width
            (fun k=>Cmove*Kcontrol*(2*T)^(2*ε)*
              Z^(exponentBinUpper width k 0+(2*bufferValue P.e q-1)*exponentBinUpper width k 3+rawError+allowance))))))
        (fun _=>(Fintype.card (BufferIndex P.e):ℝ)*((1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
          Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(Cycle63.Arithmetic.lowReserve)+4*width+loss+
            rawError+allowance+B*εmass+heightloss))))))) := by
  obtain ⟨bound,hbound,J,huniform⟩:=actual_geometry_main_high_uniform_shell (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  obtain ⟨F,G,Cprofile,C,Kcolumn,Cmove,hF,hCprofile,hC,hKcolumn,hCmove,hjoint⟩:=
    huniform heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  refine ⟨F,G,Cprofile,C,Kcolumn,Cmove,hF,hCprofile,hC,hKcolumn,hCmove,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key ampExponent reserveShift rawError allowance Kcontrol T width Wfiber
    hξ hreserve hKcontrol hT hwidthbin hWfiber labels hfiber select A x hq hseed hs₁ hs₂ hsource hlower
    hξε hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow
    hseed₂ hwidth hradial hw hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
    t₀ u hslots hinput hKm hseedid hψ hshift pay
  let cost:=fun l=>∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
    (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
      volume (datum (row l).val.1).input) t₀ u (row l).val L
  let rhsP:=(1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
    geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
      (C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
        Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(Cycle63.Arithmetic.lowReserve)+
          4*width+loss+rawError+allowance+B*εmass+heightloss)))))
  have hlowerpos:=lowerFactor_pos N lo ap hlo hap
  have hfactor:=(geometry_high_factor_pos reflected (geometrySupportConstant N lo ap ap) bin
    (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
  have hZ0:0≤Z:=(by norm_num : (0:ℝ)≤2).trans he.1
  have hT0:0≤2*T:=mul_nonneg (by norm_num) (zero_le_one.trans hT)
  have hfront:0≤Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε):=
    mul_nonneg (mul_nonneg (mul_nonneg hKcolumn.le (Real.rpow_nonneg hT0 _))
      (pow_nonneg (zero_le_one.trans hCs) _)) (Real.rpow_nonneg hZ0 _)
  have hback:0≤C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
      Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(Cycle63.Arithmetic.lowReserve)+
        4*width+loss+rawError+allowance+B*εmass+heightloss):=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) hKcontrol)
      (Real.rpow_nonneg hT0 _)) (Real.rpow_nonneg hZ0 _)
  have hrhsP:0≤ rhsP:=mul_nonneg (one_div_nonneg.mpr hlowerpos.le)
    (mul_nonneg hWfiber (mul_nonneg hfront
      (mul_nonneg (mul_nonneg hfactor (Nat.cast_nonneg _)) hback)))
  let xc:=fun l=>compensatedHighCoordinates (x l) (geometryHighSide reflected A
    (geometryExponents s R seed (Z^D) Z ξ (column l).1.val))
  let wt:=fun (q : BufferIndex P.e) (k : Fin 4→ℤ)=>Cmove*Kcontrol*(2*T)^(2*ε)*
    Z^(exponentBinUpper width k 0+(2*bufferValue P.e q-1)*exponentBinUpper width k 3+rawError+allowance)
  let rhsT:=fun q : BufferIndex P.e=>(1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
    geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*εmass)*
      keyBinnedCount (labels.filter (fun l=>select l=q)) key xc width (wt q))))
  let rhs:=fun q : BufferIndex P.e=>pay.elim (rhsT q) (fun _=>rhsP)
  have hrhsT (q : BufferIndex P.e) : 0≤ rhsT q := by
    have hwt (k : Fin 4→ℤ) : 0≤wt q k := by
      dsimp only [wt]
      exact mul_nonneg (mul_nonneg (mul_nonneg hCmove.le hKcontrol) (Real.rpow_nonneg hT0 _))
        (Real.rpow_nonneg hZ0 _)
    exact mul_nonneg (one_div_nonneg.mpr hlowerpos.le) (mul_nonneg hWfiber (mul_nonneg hfront
      (mul_nonneg (mul_nonneg hfactor (Real.rpow_nonneg hZ0 _)) (keyBinnedCount_nonneg _ _ _ _ _ hwt))))
  have hrhs (q : BufferIndex P.e) : 0≤ rhs q := by
    cases pay <;> first | exact hrhsT q | exact hrhsP
  have hone (q : BufferIndex P.e) : Z^(-ampExponent)*(∑l∈labels.filter (select ·=q),cost l)≤ rhs q := by
    let small:=labels.filter (select ·=q)
    have hsub : small⊆labels:=Finset.filter_subset _ _
    have heq {l : κ}(hl : l∈small):select l=q:=(Finset.mem_filter.mp hl).2
    by_cases hempty:small=∅
    · change Z^(-ampExponent)*(∑l∈small,cost l)≤ rhs q
      simpa only [hempty,Finset.sum_empty,mul_zero] using hrhs q
    · obtain ⟨l₀,hl₀⟩:=Finset.nonempty_iff_ne_empty.mpr hempty
      have hinterval (l : κ)(hl : l∈small):=And.intro (hhigh l (hsub hl)) (hbin l (hsub hl)).2.2.2
      have hβ:=hinterval l₀ hl₀
      rw [heq hl₀] at hβ
      let into : small→labels:=fun r=>⟨r.val,hsub r.property⟩
      have hinj:Function.Injective into:=by intro r t h; exact Subtype.ext (congrArg (fun q : labels=>q.val) h)
      have hsmallfiber:=high_restricted_key_fiber into hinj (fun r : labels=>key r.val) Wfiber hfiber
      have hj:=he.2 reflected second s R seed W D ξ hK bin column datum first row
        hparent hfirst hR ψ (bufferValue P.e q) ampExponent reserveShift rawError allowance
        Kcontrol T width Wfiber q.1.val hβ.1 hβ.2.1 hξ hreserve hKcontrol hT hwidthbin hWfiber
        small hsmallfiber
        (fun l hl=>hq l (hsub hl)) hseed hs₁ hs₂ hsource hlower
        hξε
        (fun l hl=>hnorm l (hsub hl)) (fun l hl=>hradius l (hsub hl))
        st hQM hQη z hz hchar hpuncture hrow
        (fun l hl=>by simpa only [heq hl,geometryRowMaximum,geometryRowFamily] using (hinterval l hl).2.2.2.2.1)
        (fun l hl=>hsupport l (hsub hl))
        (by simpa only [heq hl₀] using (hbin l₀ (hsub hl₀)).2.1)
        (fun l hl=>by simpa only [heq hl] using (hbin l (hsub hl)).2.2.2.2.1)
        (by simpa only [heq hl₀] using hi l₀ (hsub hl₀))
        hcard hM hb₁ hb₂ hupper hwin B₁ t₁ (fun l hl=>hf₁ l (hsub hl))
        seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow
        (fun l hl=>hseed₂ l (hsub hl)) (fun l hl=>hwidth l (hsub hl)) (fun l hl=>hradial l (hsub hl))
        (fun l hl=>by simpa only [heq hl,geometryRowMaximum,geometryRowFamily] using (hinterval l hl).2.2.2.2.2.1)
        hw hwr hσlo hσhi (fun l hl j=>by simpa only [heq hl] using hheight l (hsub hl) j)
        (fun l hl=>by simpa only [heq hl] using hplainheight l (hsub hl))
        (fun l hl=>hW l (hsub hl)) (fun l hl=>hDs l (hsub hl)) (fun l hl=>hdyad l (hsub hl))
        (fun l hl=>hcontrol l (hsub hl)) hledger t₀ u
        (fun l hl=>hslots l (hsub hl)) (fun l hl=>hinput l (hsub hl))
        (fun l hl=>hKm l (hsub hl)) (fun l hl=>hseedid l (hsub hl))
        (fun l hl=>hψ l (hsub hl)) (fun l hl=>hshift l (hsub hl)) pay
      exact hj
  have hsplit:Z^(-ampExponent)*(∑l∈labels,cost l)=
      ∑q : BufferIndex P.e,Z^(-ampExponent)*(∑l∈labels.filter (select ·=q),cost l) := by
    simp only [Finset.mul_sum,Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp
  have hfinal : Z^(-ampExponent)*(∑l∈labels,cost l)≤∑q : BufferIndex P.e,rhs q := by
    rw [hsplit]
    exact Finset.sum_le_sum (fun q _=>hone q)
  rcases pay with _ | _
  · exact hfinal
  · refine hfinal.trans_eq ?_
    simp only [rhs,Option.elim,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rfl

end
end OAI.SevenEighths.Cycle63InitialMass
