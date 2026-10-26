import Candidate.Cycle63.Physical.InitialMass.GeometryLiteralHighFrequency
import Candidate.Cycle63.Physical.InitialMass.GeometryZeroPartition
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryHighAdmission
import Candidate.Cycle63.Physical.InitialMass.MarkedGeometryPayment

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
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

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Joint high shell payment for the literal physical child coefficient.
The zero-shell parameter β and amplifier exponent are distinct inputs. -/
theorem actual_geometry_literal_unmarked_high_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤B) (hQ : 0≤Q) (hQB : Q≤B)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0<lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
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
        (β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width : ℝ) (i : ℕ),
      21/25 ≤ β → β ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T → 0<width →
      Function.Injective key →
      ∀labels : Finset κ,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
        unmarkedDensity (2*β-1)*εfreq+εvolume
      (7/10≤2*β-1 ∨ ∀l∈labels,33*D/1000≤
        Real.logb Z ((geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)).absNorm:ℝ)+
        Real.logb Z ((if second then (datum (row l).val.1).D else (datum (row l).val.1).C).absNorm:ℝ)) →
      (∀l∈labels,x l 2+width≤Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B → lo≤s.lower →
      3401/100000≤bAmpl → bAmpl≤1/25 → D=1 → 0≤D → |D|≤B → |A|≤B → |ampExponent|≤B →
      |frequencyLoss Z 32 ξ+reserveShift|≤B → εfreq≤B → ξ≤εfreq →
      A≤D*Cycle63.Arithmetic.totalA bAmpl → ampExponent≤D*Cycle63.Arithmetic.amp bAmpl →
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
      let coeff:=fun l=>Z^(-ampExponent)*
        (firstMainRadius reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent) reserveShift
          (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))/volume (firstChild l))*
        (normalizer (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive/
          Z^(Real.logb Z ((if second then (datum (row l).val.1).D
            else (datum (row l).val.1).C).absNorm:ℝ)))
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      let R₂:=fun l=>(datum (row l).val.1).R
      ∀(pick : ∀l,actualAllocations (firstChild l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap : ℝ),
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (17/500)*D≤∑j,w j →
      (∑j,w j)≤1/25 →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      pad≤allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R₂ l)
        (firstChild l).ν (firstChild l).W (firstChild l).P≠0) →
      (∀l∈labels,(st l).width≤P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<β+2*P.e) →
      (∀j,0≤w j) → (∀j,w j/P.d≤P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (firstChild l) (st l).character (t l)) (E l) (R₂ l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤rawError →
      (∑l∈labels,geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
        coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l)))≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-D*(720486667/30493190000000)+4*width+loss+rawError+allowance+B*εmass)) := by
  obtain ⟨bound,hbound,J,hpaid⟩ := actual_geometry_paid_binned_high_shell
    (α:=α) (bp:=bp) M H hH η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N lo εmass hlo hεmass Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hpaid P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint,eventual_actual_child_high_coefficient N lo εvolume hlo hεvolume,
    eventual_geometry_literal_high_frequency η₀ u₀ F₀ R₀ hu₀ b εfreq N
      (zero_lt_one.trans_le hb) hεfreq] with Z he hcoef hfrequency
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width i hβ hβ'
    hKcontrol hT hwidthbin hinj labels A x target hbranch hq hseed hz₁ hz₂ hsource hlower
    hbAmpl hbAmpl' hDunit hD hDbox hAbox hampbox hω hεbox hξ hA hamp hsecond hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hM hb₁ hb₂ hupperB hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild coeff E R₂ pick t w σ v θ p Ds cap
    hcap hmatches hsupply hsupplyUpper hscales hpadallow hf₂ hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq
    hW hDs hdyad src hcontrol hrawError
  have hZ : 1<Z := by linarith [he.1]
  have hδ : Cycle63.Arithmetic.q0≤2*β-1 ∧ 2*β-1≤3/4 := by
    norm_num [Cycle63.Arithmetic.q0]; constructor <;> linarith
  have hgeo (l : κ)(hl : l∈labels) := actual_geometry_compensated_high_gates s R seed (Z^D) Z ξ hK
    bin (column l) (datum (row l).val.1) reflected left second (datum (row l).val.1).inactive
    D A ampExponent reserveShift εfreq εvolume B bAmpl (2*β-1) hZ hB hseed hz₁ hz₂ hsource
    (hsecond l hl) hDbox hAbox hampbox hω (by rw [abs_of_pos hεfreq]; exact hεbox)
    ⟨hbAmpl,hbAmpl'⟩ hδ hD hA hamp
  have hx (l : κ)(hl : l∈labels) : ∀j,-(32*B+|εvolume|)≤x l j ∧ x l j≤32*B+|εvolume| := by
    have hn:=actual_geometry_norm_caps s R seed (Z^D) Z ξ B hseed hz₁ hz₂ hsource (column l).1.val
    exact (actual_geometry_high_coordinate_gates s R seed (Z^D) Z ξ hK bin (column l)
      (datum (row l).val.1) reflected left second (datum (row l).val.1).inactive
      D A ampExponent reserveShift εfreq εvolume B bAmpl (2*β-1) hZ hB
      ⟨(hn 0).2,(hn 1).2⟩ (hsecond l hl) hDbox hAbox hampbox hω
      (by rw [abs_of_pos hεfreq]; exact hεbox) ⟨hbAmpl,hbAmpl'⟩ hδ hD hA hamp).2.1
  have hcoeff (l : κ)(hl : l∈labels) : coeff l≤Z^(x l 0) := by
    have hC:Supported (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.1 :=
      (geometryFirstSource s R seed (Z^D) Z ξ hK bin (column l).1).hC
    have hD':Supported (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.2 :=
      (geometryFirstSource s R seed (Z^D) Z ξ hK bin (column l).1).hD
    have hsup:primeSupport (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.1=
      primeSupport (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.2 :=
      (geometryFirstSource s R seed (Z^D) Z ξ hK bin (column l).1).sameSupport
    exact hcoef.2 s hcard hlower reflected left second
      (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)) hC hD' hsup R (B₁ l) (χ₁ l) (t₁ l)
      (hf₁ l hl) (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).hC
      (datum (row l).val.1).inactive D ampExponent ξ reserveShift εfreq
  have hpoint (l : κ)(hl : l∈labels) : highExponentValue (2*β-1) (x l)≤
      geometryHighSide reflected A (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)+
        target-D*(720486667/30493190000000) := by
    have hh : highExponentValue (2*β-1) (compensatedHighCoordinates (x l)
        (geometryHighSide reflected A (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)))≤
        target-D*(720486667/30493190000000) := by
      rcases hbranch with hhigh | hlarge
      · exact actual_geometry_compensated_payment_of_reserve s R seed (Z^D) Z ξ hK
          bin (column l) (datum (row l).val.1) reflected left second (datum (row l).val.1).inactive
          D A ampExponent reserveShift εfreq εvolume bAmpl (2*β-1) _ hZ
          ⟨hbAmpl,hbAmpl'⟩ hδ hD hA hamp
          (Cycle63.Physical.unmarked_upper_high_reserve ⟨hbAmpl,hbAmpl'⟩ ⟨hhigh,hδ.2⟩)
      · by_cases hhigh : 7/10≤2*β-1
        · exact actual_geometry_compensated_payment_of_reserve s R seed (Z^D) Z ξ hK
            bin (column l) (datum (row l).val.1) reflected left second (datum (row l).val.1).inactive
            D A ampExponent reserveShift εfreq εvolume bAmpl (2*β-1) _ hZ
            ⟨hbAmpl,hbAmpl'⟩ hδ hD hA hamp
            (Cycle63.Physical.unmarked_upper_high_reserve ⟨hbAmpl,hbAmpl'⟩ ⟨hhigh,hδ.2⟩)
        · have hpay:=actual_geometry_compensated_allocation_payment s R seed (Z^D) Z ξ hK
            bin (column l) (datum (row l).val.1) reflected left second (datum (row l).val.1).inactive
            D A ampExponent reserveShift εfreq εvolume bAmpl (2*β-1) hZ
            ⟨hbAmpl,hbAmpl'⟩ ⟨hδ.1,le_of_lt (lt_of_not_ge hhigh)⟩ hD hA hamp
          have hr:=Cycle63.Physical.marked_high_reserve ⟨hbAmpl,hbAmpl'⟩ hδ
          have hmul:=mul_le_mul_of_nonneg_left hr hD
          have hlarge':=hlarge l hl
          change 33*D/1000≤
            Real.logb Z ((if reflected then
              (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.2 else
              (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.1).absNorm:ℝ)+
            Real.logb Z ((if second then (datum (row l).val.1).D else (datum (row l).val.1).C).absNorm:ℝ)
            at hlarge'
          dsimp only at hpay
          change highExponentValue (2*β-1) (compensatedHighCoordinates (x l)
            (geometryHighSide reflected A (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)))≤
            target-D*Cycle63.Physical.highMainReserve bAmpl (2*β-1)-_ at hpay
          nlinarith only [hpay,hmul,hlarge',hD]
    rw [compensated_high_exponent] at hh
    linarith only [hh]
  have hnorm (l : κ)(hl : l∈labels) :
      ((key l).val.1.1.1.absNorm:ℝ)≤Z^B ∧ ((key l).val.1.1.2.absNorm:ℝ)≤Z^B ∧
      ((key l).val.2.1.1.absNorm:ℝ)≤Z^B ∧ ((key l).val.2.1.2.absNorm:ℝ)≤Z^B := by
    have hn:=actual_geometry_norm_caps s R seed (Z^D) Z ξ B hseed hz₁ hz₂ hsource (column l).1.val
    have h₁ : ((geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.1.absNorm:ℝ)≤Z^B ∧
      ((geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.2.absNorm:ℝ)≤Z^B := ⟨(hn 0).2,(hn 1).2⟩
    cases second <;> simpa only [key,rawKey,secondEncodedNonzeroRow,secondEncodedRow,
      reflectedNonzeroJointLabel,reflectedJointLabel,SecondInputDatum.block,originalSecondBlock,
      Bool.false_eq_true,ite_false,ite_true,hfirst] using ⟨h₁.1,h₁.2,(hsecond l hl).1,(hsecond l hl).2⟩
  have hmissing (l : κ)(hl : l∈labels) : ((firstSourceMissing left (key l).val.1).absNorm:ℝ)≤Z^(x l 1) := by
    have hk : (key l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l) := by
      cases second <;> exact hfirst l
    rw [hk]
    have hh:=(hgeo l hl).1
    simpa only [x,compensatedHighCoordinates,childHighCoordinates,show (1:Fin 4)≠0 by decide,
      ite_false,add_zero] using hh.le

  have hzero' (l : κ)(hl : l∈labels) : rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^(x l 2) ∧
      β≤HeckeDetectorZeros.zeroMaximum (wholeSourceFamily M H hH η₀
        (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
          (st l).puncture)) (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l)
            (z l) (hz l) _) (3*(i+1:ℕ)*Z^P.τ) := by
    exact ⟨hfrequency.2 reflected second s R seed D ξ hK bin (column l) datum first (row l)
      (hfirst l) ampExponent reserveShift εvolume hξ (hradius l hl),hzero l hl⟩
  have hmask (l : κ)(_hl : l∈labels) : (st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
      idealGenerator (R₂ l*E l) := by
    simp only [NaturalState.mask,hpuncture l]
    rfl
  have hledger (l : κ)(hl : l∈labels) :
      (2*β-1)*(A-Real.logb Z ((C₁ l).absNorm:ℝ)-Real.logb Z ((E l).absNorm:ℝ))+pad+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤(2*β-1)*x l 3+rawError := by
    have hcards : (Fintype.card α:ℝ)≤N := Nat.cast_le.mpr hcard
    have hp : 0≤2*P.εslot*P.d := mul_nonneg
      (mul_nonneg (by norm_num : (0:ℝ)≤2) P.hεs.le) P.hd.le
    have hh:=mul_le_mul_of_nonneg_left hcards hp
    have hraw : pad+2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤rawError := by linarith
    have hx3 : x l 3=A-Real.logb Z ((C₁ l).absNorm:ℝ)-Real.logb Z ((E l).absNorm:ℝ) := by
      change (A-Real.logb Z ((C₁ l).absNorm:ℝ)-Real.logb Z ((E l).absNorm:ℝ))+0=_
      exact add_zero _
    rw [hx3]
    linarith
  have hh:=he.2 reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    β rawError allowance Kcontrol T width (32*B+|εvolume|) target (D*(720486667/30493190000000)) i
    hβ hβ' hKcontrol hT hwidthbin hinj labels x coeff hx hq hcoeff hpoint
    hseed hz₁ hz₂ hsource hAbox hlower st hQM hQη z hz hchar hpuncture hrow hzero' hsupport hnorm
    hmissing hi hcard hM hb₁ hb₂ hupperB hwin C₁ (fun _=>R) B₁ χ₁ t₁ hf₁ E R₂ pick t w σ v θ p Ds cap A
    hcap hmatches hscales (by exact le_refl _) hpadallow hf₂ hmask hwidth hradial hupper
    hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad hcontrol hledger
  simpa only [show 32*B+|εvolume|+5*B=37*B+|εvolume| by ring] using hh

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_geometry_literal_high_frequency
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_literal_unmarked_high_shell
