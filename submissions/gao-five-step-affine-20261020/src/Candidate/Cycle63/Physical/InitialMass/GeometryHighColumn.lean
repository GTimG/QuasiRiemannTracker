import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryHighFamily
import Candidate.Cycle63.Physical.InitialMass.GeometryHighActualShell
import Candidate.Cycle63.Physical.InitialMass.SecondWeightedCommon
import Candidate.Cycle63.Moment.JointWindowFamily
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 6000000
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

/-- Real physical weights remain inside supported common-allocation selection. -/
theorem high_real_common_selection {α : Type*} [Fintype α] [DecidableEq α]
    (b ε : ℝ)(hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀{κ : Type*}(rows : Finset κ)(slots : κ→Finset α)
      (s : (k : κ)→ Input (slots k))(C R : κ→ Ideal O)(Ds : κ→Finset (Ideal O))
      (z : κ→O)(weight : κ→ℝ)(E : ℝ),
      (∀k,0≤weight k) → (∀k∈rows,(s k).upper≤b) → (∀k∈rows,C k≠0) →
      (∀S : Finset rows,∀pick : (k : S)→actualAllocations (s k.val.val).pools (C k.val.val),
        (∀k,frozenCoefficient (pick k).val (C k.val.val) (R k.val.val)
          (s k.val.val).ν (s k.val.val).W (s k.val.val).P≠0) →
        (∑k : S,(weight k.val.val*(∏j,(s k.val.val).M j)^2*((C k.val.val).absNorm:ℝ)^(ε-1))*
          ∑L∈Ds k.val.val,∑a∈(commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k)).toSource.active L,
            retainedAllocationCost (commonData (s k.val.val) (C k.val.val) (R k.val.val) (pick k)) L a (z k.val.val))≤E) →
      (∑k∈rows,weight k*∑L∈Ds k,commonRetainedCost (s k) (C k) (R k) L (z k))≤K*E := by
  obtain ⟨K,hK,hcommon⟩:=actual_second_weighted_common_selection (α:=α) b ε hε
  refine ⟨K,hK,?_⟩
  intro κ rows slots s C R Ds z weight E hw hupper hC hjoint
  let scalar:=fun k=>(Real.sqrt (weight k):ℂ)
  have heq (k : κ) : ‖scalar k‖^2=weight k := by
    dsimp only [scalar]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw k)]
  have hh:=hcommon rows slots s C R Ds z scalar E hupper hC
    (fun S pick hne=>by
      simp only [heq]
      exact hjoint S pick (fun k=>right_ne_zero_of_mul (hne k)))
  simpa only [heq] using hh

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Actual normalized columns after supported allocation selection. Zero-shell and height gates remain literal partition
data, without an energy premise. Without payment data the bound is the transport form: the extraction and selection
constants times the binned count form of the compensated child coordinates; with the cell payment data it is paid. -/
theorem actual_geometry_selected_high_columns {α : Type} [Fintype α] [DecidableEq α]
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
      ∀P : HighSourceParameters,P.profileBound=bound →
      MarkedSchedule P N Wslot (33/50) (33/50) →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      2*P.τ*((J:ℝ)+1)≤Cycle63.Optimization.geometryLossCap/8 →
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
        (β ampExponent reserveShift rawError allowance Kcontrol T width : ℝ) (i : ℕ),
      ((1+Cycle63.Arithmetic.q0)/2) ≤ β → β ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T → 0<width →
      Function.Injective key →
      ∀labels : Finset κ,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
        unmarkedDensity (2*β-1)*εfreq+εvolume
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
      let R₂:=fun l=>(datum (row l).val.1).R
      let outer:=fun l=>Z^(-ampExponent)*
        (firstMainRadius reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent) reserveShift
          (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))/volume (firstChild l))*
        normalizer (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
      let hE : ∀l,Supported (E l):=fun l=>by
        dsimp only [E]; split <;> first | exact (datum (row l).val.1).hD | exact (datum (row l).val.1).hC
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
      ∀pay : Option (HighCellPayment η₀ u₀ F₀ R₀ Z s D ξ ampExponent reserveShift εfreq B w),
      (∑l∈labels,geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
        outer l*(∑L∈Ds l,‖normalizedColumn (withHeight (firstChild l) (st l).character (t l))
          (E l) (hE l) (R₂ l) (seed₂ l) L (z l)‖^2))≤
      pay.elim
        (Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
          geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*εmass)*
          binnedCount labels (fun l=>compensatedHighCoordinates (x l) (geometryHighSide reflected A
            (geometryExponents s R seed (Z^D) Z ξ (column l).1.val))) width
            (fun key=>Cmove*Kcontrol*(2*T)^(2*ε)*
              Z^(exponentBinUpper width key 0+(2*β-1)*exponentBinUpper width key 3+rawError+allowance))))
        (fun _=>Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
          geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
          ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
          (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
            Z^(target-D*(Cycle63.Arithmetic.lowReserve)+4*width+loss+rawError+allowance+B*εmass)))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_literal_high_shell (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  obtain ⟨Kextract,hKextract,hextract⟩:=actual_uniform_second_column_extraction (α:=α) ε hε
  obtain ⟨Kcommon,hKcommon,hcommon⟩:=high_real_common_selection.{0,0} (α:=α) b ε hε
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hmarked hslot hplain hmarkedHeight
  obtain ⟨F,G,Cprofile,C,Cmove,hF,hCprofile,hC,hCmove,hjoint⟩:=hhigh P hboundeq hmarked hslot hplain hmarkedHeight
  refine ⟨F,G,Cprofile,C,Kextract*Kcommon,Cmove,hF,hCprofile,hC,mul_pos hKextract hKcommon,hCmove,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift rawError allowance Kcontrol T width i
    hβ hβ' hKcontrol hT hwidthbin hinj labels A x target hq hseed hs₁ hs₂ hsource hlower
    hξε hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E R₂ outer hE seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow
    hseed₂ hwidth hradial hzeroUpper hw hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger pay
  let coeff:=fun l=>Z^(-ampExponent)*
    (firstMainRadius reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent) reserveShift
      (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))/volume (firstChild l))*
    (normalizer (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive/
      Z^(Real.logb Z ((E l).absNorm:ℝ)))
  have hZ : 1<Z:=(by norm_num : (1:ℝ)<2).trans_le he.1
  have hZpos : 0<Z:=zero_lt_one.trans hZ
  let mass:=fun l=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)
  let source:=fun l=>withHeight (firstChild l) (st l).character (t l)
  let xc:=fun l=>compensatedHighCoordinates (x l) (geometryHighSide reflected A
    (geometryExponents s R seed (Z^D) Z ξ (column l).1.val))
  let wt:=fun key : Fin 4→ℤ=>Cmove*Kcontrol*(2*T)^(2*ε)*
    Z^(exponentBinUpper width key 0+(2*β-1)*exponentBinUpper width key 3+rawError+allowance)
  have hwt (key : Fin 4→ℤ) : 0≤wt key := by dsimp only [wt]; positivity
  have hfac : 0≤geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*εmass) :=
    mul_nonneg (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le (Real.rpow_nonneg hZpos.le _)
  let rhsT:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*εmass)*
    binnedCount labels xc width wt
  let rhsP:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
    (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
      Z^(target-D*(Cycle63.Arithmetic.lowReserve)+4*width+loss+rawError+allowance+B*εmass))
  let rhs:=pay.elim rhsT (fun _=>rhsP)
  have hrhsT : 0≤ rhsT := mul_nonneg hfac (binnedCount_nonneg _ _ _ _ hwt)
  have hrhsP : 0≤ rhsP := by
    dsimp only [rhsP]
    exact mul_nonneg (mul_nonneg (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le (Nat.cast_nonneg _)) (by positivity)
  have hrhs : 0≤ rhs := by cases pay <;> first | exact hrhsT | exact hrhsP
  have houter (l : κ) : 0≤outer l := by
    dsimp only [outer]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hZpos.le _)
      (div_nonneg (first_main_radius_pos reflected (Z^D) (volume s) Z ξ (3*ampExponent)
        reserveShift hZpos _).le (volume_pos (firstChild l)).le))
      (normalizer_pos _ _ (datum (row l).val.1).hC _).le
  have hmass (l : κ) : 0≤ mass l :=geometry_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l)
  have hprod (l : κ) : (∏j,(source l).M j)^2≤Cs^(2*N) := by
    have hp : (∏j,(source l).M j)≤Cs^N := by
      calc
        _≤∏_j : liveIndices (B₁ l).val,Cs:=Finset.prod_le_prod₀
          (fun j _=>zero_le_one.trans ((source l).M_ge_one j)) (fun j _=>hM j.val)
        _=Cs^(Fintype.card (liveIndices (B₁ l).val)):=by simp
        _≤Cs^N:=pow_le_pow_right₀ hCs ((live_card_le (B₁ l).val).trans hcard)
    exact (pow_le_pow_left₀ (Finset.prod_nonneg (fun j _=>zero_le_one.trans ((source l).M_ge_one j))) hp 2).trans_eq
      (by rw [←pow_mul]; congr 1; omega)
  have hn (l : κ) : 0<((E l).absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ (hE l).1
  have hcoeff (l : κ) : outer l*((E l).absNorm:ℝ)^(ε-1)=coeff l*((E l).absNorm:ℝ)^ε := by
    have heq : Z^(Real.logb Z ((E l).absNorm:ℝ))=((E l).absNorm:ℝ):=Real.rpow_logb hZpos hZ.ne' (hn l)
    dsimp only [coeff,outer,E]
    rw [Real.rpow_sub (hn l),Real.rpow_one]
    rw [heq]
    ring
  have hcommonBound : (∑l∈labels,mass l*outer l*∑L∈Ds l,commonRetainedCost (source l) (E l) (R₂ l) L (z l))≤
      Kcommon*(Cs^(2*N)*Z^(B*ε)*rhs) := by
    apply hcommon labels (fun l=>liveIndices (B₁ l).val) source E R₂ Ds z (fun l=>mass l*outer l)
      (Cs^(2*N)*Z^(B*ε)*rhs) (fun l=>mul_nonneg (hmass l) (houter l))
      (fun _ _=>hupper) (fun l _=>(hE l).1)
    intro S pick hne
    by_cases hempty : S.Nonempty
    · let _ : Nonempty ↥S:=Finset.nonempty_coe_sort.mpr hempty
      have hselected:=he.2 reflected second s R seed W D ξ hK bin
        (fun l : S=>column l.val.val) datum first (fun l=>row l.val.val)
        (fun l=>hparent l.val.val) (fun l=>hfirst l.val.val) (fun l=>hR l.val.val) (fun l=>ψ l.val.val)
        β ampExponent reserveShift rawError allowance Kcontrol T width i
        hβ hβ' hKcontrol hT hwidthbin
        (fun j k heq=>Subtype.ext (Subtype.ext (hinj heq))) Finset.univ
        (fun l _=>hq l.val.val l.val.property) hseed hs₁ hs₂ hsource hlower
        hξε
        (fun l _=>hnorm l.val.val l.val.property) (fun l _=>hradius l.val.val l.val.property)
        (fun l=>st l.val.val) (fun l=>hQM l.val.val) (fun l=>hQη l.val.val)
        (fun l=>z l.val.val) (fun l=>hz l.val.val)
        (fun l=>hchar l.val.val) (fun l=>hpuncture l.val.val) (fun l=>hrow l.val.val)
        (fun l _=>hzero l.val.val l.val.property) (fun l _=>hsupport l.val.val l.val.property)
        hibuffer (fun l _=>hcurrent l.val.val l.val.property) hi hcard hM hb₁ hb₂ hupper hwin
        (fun l=>B₁ l.val.val) (fun l=>t₁ l.val.val) (fun l _=>hf₁ l.val.val l.val.property)
        pick (fun l=>t l.val.val) w σ v θ (fun l=>p l.val.val) (fun l=>Ds l.val.val) cap
        hcap hmatches hscales hpadallow (fun l _=>hne l)
        (fun l _=>hwidth l.val.val l.val.property) (fun l _=>hradial l.val.val l.val.property)
        (fun l _=>hzeroUpper l.val.val l.val.property) hw hwr hσlo hσhi
        (fun l _=>hheight l.val.val l.val.property) (fun l _=>hplainheight l.val.val l.val.property)
        (fun l _=>hW l.val.val l.val.property) (fun l _=>hDs l.val.val l.val.property)
        (fun l _=>hdyad l.val.val l.val.property) (fun l _=>hcontrol l.val.val l.val.property) hledger pay
      have hsub : (Finset.univ : Finset ↥S).image (fun l : ↥S=>l.val.val)⊆labels := by
        intro l hl
        obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hl
        exact r.val.property
      have hinjS : Set.InjOn (fun l : ↥S=>l.val.val) ↑(Finset.univ : Finset ↥S) :=
        fun a _ c _ h=>Subtype.ext (Subtype.ext h)
      have hsel : (∑l : S,mass l.val.val*coeff l.val.val*(∑L∈Ds l.val.val,∑a∈(commonData (source l.val.val)
          (E l.val.val) (R₂ l.val.val) (pick l)).toSource.active L,retainedAllocationCost (commonData
            (source l.val.val) (E l.val.val) (R₂ l.val.val) (pick l)) L a (z l.val.val)))≤ rhs := by
        cases pay with
        | none =>
          refine hselected.trans (mul_le_mul_of_nonneg_left ?_ hfac)
          exact le_of_eq_of_le (binnedCount_comp Finset.univ (fun l : ↥S=>l.val.val) hinjS xc width wt)
            (binnedCount_mono_labels hsub xc width wt hwt)
        | some _ => exact hselected
      let shell:=fun l : S=>∑L∈Ds l.val.val,∑a∈(commonData (source l.val.val) (E l.val.val) (R₂ l.val.val) (pick l)).toSource.active L,
        retainedAllocationCost (commonData (source l.val.val) (E l.val.val) (R₂ l.val.val) (pick l)) L a (z l.val.val)
      have hshell (l : S) : 0≤ shell l:=Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>retained_allocation_cost_nonneg _ _ _ _))
      have hncap (l : S) : ((E l.val.val).absNorm:ℝ)^ε≤Z^(B*ε):=
        (Real.rpow_le_rpow (hn l.val.val).le (by
          cases second
          · exact (hnorm l.val.val l.val.property).1
          · exact (hnorm l.val.val l.val.property).2) hε.le).trans_eq (Real.rpow_mul hZpos.le _ _).symm
      calc
        _≤∑l : S,(Cs^(2*N)*Z^(B*ε))*(mass l.val.val*coeff l.val.val*shell l) := by
          refine Finset.sum_le_sum fun l _ => ?_
          have hc : 0≤ coeff l.val.val := by
            have heq : coeff l.val.val=outer l.val.val/Z^(Real.logb Z ((E l.val.val).absNorm:ℝ)):=by
              dsimp only [coeff,outer];ring
            rw [heq]
            exact div_nonneg (houter _) (Real.rpow_nonneg hZpos.le _)
          have hh:=mul_le_mul (hprod l.val.val) (hncap l)
            (Real.rpow_nonneg (hn l.val.val).le _) (by positivity : 0≤Cs^(2*N))
          have hp:=mul_le_mul_of_nonneg_right hh (mul_nonneg (mul_nonneg (hmass l.val.val) hc) (hshell l))
          calc
            _=(∏j,(source l.val.val).M j)^2*(mass l.val.val*(outer l.val.val*((E l.val.val).absNorm:ℝ)^(ε-1))*shell l):=by ring
            _=(∏j,(source l.val.val).M j)^2*(mass l.val.val*(coeff l.val.val*((E l.val.val).absNorm:ℝ)^ε)*shell l):=by rw [hcoeff]
            _≤_:=by convert hp using 1; ring
        _=(Cs^(2*N)*Z^(B*ε))*(∑l : S,mass l.val.val*coeff l.val.val*shell l):=(Finset.mul_sum ..).symm
        _≤(Cs^(2*N)*Z^(B*ε))*rhs:=mul_le_mul_of_nonneg_left hsel (by positivity)
    · let _ : IsEmpty ↥S:=⟨fun l=>hempty ⟨l.val,l.property⟩⟩
      simp only [Finset.univ_eq_empty,Finset.sum_empty]
      positivity
  calc
    _≤∑l∈labels,mass l*outer l*(Kextract*(2*T)^ε*∑L∈Ds l,commonRetainedCost (source l) (E l) (R₂ l) L (z l)) := by
      refine Finset.sum_le_sum fun l hl => ?_
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hmass l) (houter l))
      calc
        _≤∑L∈Ds l,Kextract*(2*T)^ε*commonRetainedCost (source l) (E l) (R₂ l) L (z l) := by
          refine Finset.sum_le_sum fun L hL => ?_
          exact (hextract (liveIndices (B₁ l).val) (source l) (E l) (hE l) (R₂ l) (seed₂ l) L
            (hseed₂ l hl) (hDs l hl L hL) (z l)).trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (Nat.cast_nonneg _) (hdyad l hl L hL).2.le hε.le) hKextract.le)
              (common_retained_cost_nonneg _ _ _ _ _))
        _=Kextract*(2*T)^ε*∑L∈Ds l,commonRetainedCost (source l) (E l) (R₂ l) L (z l):=(Finset.mul_sum ..).symm
    _=(Kextract*(2*T)^ε)*(∑l∈labels,mass l*outer l*∑L∈Ds l,commonRetainedCost (source l) (E l) (R₂ l) L (z l)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    _≤(Kextract*(2*T)^ε)*(Kcommon*(Cs^(2*N)*Z^(B*ε)*rhs)):=
      mul_le_mul_of_nonneg_left hcommonBound (by positivity)
    _=_:=by cases pay <;> (dsimp only [rhs,rhsT,rhsP,xc,wt,Option.elim]; ring)

end
end OAI.SevenEighths.Cycle63InitialMass
