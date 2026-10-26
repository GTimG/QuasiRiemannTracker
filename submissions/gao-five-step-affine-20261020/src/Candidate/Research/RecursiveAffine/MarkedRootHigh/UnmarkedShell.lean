import Candidate.Cycle63.Physical.InitialMass.GeometryUnmarkedActualShell
import Candidate.Research.RecursiveAffine.MarkedRootHigh.GeometryPayment
import Candidate.Research.RecursiveAffine.MarkedRootHigh.RootReserve
import Candidate.Cycle63.Physical.InitialMass.GeometryLiteralHighFrequency
import Candidate.Cycle63.Physical.InitialMass.GeometryZeroPartition
import Candidate.Cycle63.Physical.InitialMass.MarkedGeometryPayment

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OAI.SevenEighths.Cycle153RootHigh
open Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
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

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

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
      ((1+Cycle153.MarkedRootPrice.q)/2) ≤ β → β ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T → 0<width →
      Function.Injective key →
      ∀labels : Finset κ,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
        unmarkedDensity (2*β-1)*εfreq+εvolume
      ((2/3:ℝ)≤2*β-1 ∨ ∀l∈labels,Cycle63.Optimization.suppliedAt bAmpl*D≤
        Real.logb Z ((geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)).absNorm:ℝ)+
        Real.logb Z ((if second then (datum (row l).val.1).D else (datum (row l).val.1).C).absNorm:ℝ)) →
      (∀l∈labels,x l 2+width≤Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B → lo≤ s.lower →
      Cycle63.Optimization.firstCellTop≤bAmpl → bAmpl≤Cycle153.MarkedRootPrice.top → D=1 → 0≤D → |D|≤B → |A|≤B → |ampExponent|≤B →
      |frequencyLoss Z 32 ξ+reserveShift|≤B → εfreq≤B → ξ≤εfreq →
      A≤D*Cycle153.MarkedRootPrice.totalA bAmpl → ampExponent≤D*Cycle153.MarkedRootPrice.amp bAmpl →
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
      (bAmpl-Cycle63.Optimization.cellMesh)*D≤∑j,w j →
      (∑j,w j)≤Cycle153.MarkedRootPrice.top →
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
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      (∑l∈labels,geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
        coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l)))≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-D*(Cycle153.MarkedRootPrice.lowReserve)+4*width+loss+rawError+allowance+B*εmass))  := by
  obtain ⟨J,Ccount,hCcount,hpay⟩ := actual_geometry_high_transport_payment
    (α:=α) M H hH η₀ u₀ F₀ R₀ hu₀ B Q loss hB hQ hQB hloss
  obtain ⟨bound,hbound,htransport⟩ := actual_geometry_literal_unmarked_high_transport
    (α:=α) (bp:=bp) M H hH η₀ u₀ F₀ R₀ hu₀ B ε hε hap
    N lo εmass εfreq εvolume hlo hεmass hεvolume Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,Cshell,hF,hCprofile,hCshell,hjoint⟩ := htransport P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,Ccount*Cshell,hF,hCprofile,mul_pos hCcount hCshell,?_⟩
  filter_upwards [hjoint,
    eventual_geometry_literal_high_frequency η₀ u₀ F₀ R₀ hu₀ b εfreq N
      (zero_lt_one.trans_le hb) hεfreq] with Z he hfrequency
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
    constructor <;> linarith [Cycle153.MarkedRootPrice.q_native,Cycle63.Arithmetic.q0_bounds.1, Cycle63.Arithmetic.q0_bounds.2,
      (show (2/3:ℝ)≤2/3 from le_rfl), (show (2/3:ℝ)≤3/4 by norm_num)]
  have hgeo (l : κ) := actual_geometry_compensated_high_missing s R seed (Z^D) Z ξ hK
    bin (column l) (datum (row l).val.1) reflected left second (datum (row l).val.1).inactive
    D A ampExponent reserveShift εfreq εvolume hZ
  have hx (l : κ)(hl : l∈labels) : ∀j,-(32*B+|εvolume|)≤x l j ∧ x l j≤32*B+|εvolume| := by
    have hn:=actual_geometry_norm_caps s R seed (Z^D) Z ξ B hseed hz₁ hz₂ hsource (column l).1.val
    exact (actual_geometry_high_coordinate_gates s R seed (Z^D) Z ξ hK bin (column l)
      (datum (row l).val.1) reflected left second (datum (row l).val.1).inactive
      D A ampExponent reserveShift εfreq εvolume B hZ hB
      ⟨(hn 0).2,(hn 1).2⟩ (hsecond l hl) hDbox hAbox hampbox hω
      (by rw [abs_of_pos hεfreq]; exact hεbox)).2
  have hpoint (l : κ)(hl : l∈labels) : highExponentValue (2*β-1) (x l)≤
      geometryHighSide reflected A (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)+
        target-D*(Cycle153.MarkedRootPrice.lowReserve) := by
    have hh : highExponentValue (2*β-1) (compensatedHighCoordinates (x l)
        (geometryHighSide reflected A (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)))≤
        target-D*(Cycle153.MarkedRootPrice.lowReserve) := by
      have hunmarked (hhigh : (2/3:ℝ)≤2*β-1) :=
        actual_geometry_compensated_payment_of_reserve s R seed (Z^D) Z ξ hK
          bin (column l) (datum (row l).val.1) reflected left second (datum (row l).val.1).inactive
          D A ampExponent reserveShift εfreq εvolume bAmpl (2*β-1) Cycle153.MarkedRootPrice.lowReserve hZ
          ⟨hbAmpl,hbAmpl'⟩ hδ hD hA hamp rfl
          (by linarith [Cycle153.MarkedRootPrice.unmarked_upper_high_reserve ⟨hbAmpl,hbAmpl'⟩ ⟨hhigh,hδ.2⟩,
            Cycle153.MarkedRootPrice.markedLoss_pos])
      rcases hbranch with hhigh | hlarge
      · exact hunmarked hhigh
      · by_cases hhigh : (2/3:ℝ)≤2*β-1
        · exact hunmarked hhigh
        · have hpay:=actual_geometry_compensated_allocation_payment s R seed (Z^D) Z ξ hK
            bin (column l) (datum (row l).val.1) reflected left second (datum (row l).val.1).inactive
            D A ampExponent reserveShift εfreq εvolume bAmpl (2*β-1) hZ
            ⟨hbAmpl,hbAmpl'⟩ hδ hD hA hamp rfl
          have hr:=Cycle153.MarkedRootPrice.marked_high_reserve ⟨hbAmpl,hbAmpl'⟩
            ⟨by linarith,le_of_lt (lt_of_not_ge hhigh)⟩
          have hlarge':=hlarge l hl
          change Cycle63.Optimization.suppliedAt bAmpl*D≤
            Real.logb Z ((if reflected then
              (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.2 else
              (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.1).absNorm:ℝ)+
            Real.logb Z ((if second then (datum (row l).val.1).D else (datum (row l).val.1).C).absNorm:ℝ)
            at hlarge'
          dsimp only at hpay
          change highExponentValue (2*β-1) (compensatedHighCoordinates (x l)
            (geometryHighSide reflected A (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)))≤
            target-D*Cycle153.MarkedRootPrice.highMainReserve bAmpl (2*β-1)-_ at hpay
          have hrate := Cycle63.Physical.commonRate_nonneg hδ
          have hpl := mul_le_mul_of_nonneg_left hlarge' hrate
          have hl0 : 0 ≤ D*Cycle153.MarkedRootPrice.markedLoss :=
            mul_nonneg hD Cycle153.MarkedRootPrice.markedLoss_pos.le
          change _ ≤ _+OAI.SevenEighths.Cycle63Moment.ValuationCone.commonRate (2*β-1)*_ at hr
          have hmul:=mul_le_mul_of_nonneg_left hr hD
          linarith only [hpay,hmul,hpl,hl0]
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
    have hh:=hgeo l
    simpa only [x,compensatedHighCoordinates,childHighCoordinates,show (1:Fin 4)≠0 by decide,
      ite_false,add_zero] using hh.le

  have hzero' (l : κ)(hl : l∈labels) : rawFrequencyNorm (nonzeroJointSourceRow (key l))≤Z^(x l 2) ∧
      β≤HeckeDetectorZeros.zeroMaximum (wholeSourceFamily M H hH η₀
        (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
          (st l).puncture)) (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l)
            (z l) (hz l) _) (3*(i+1:ℕ)*Z^P.τ) := by
    exact ⟨hfrequency.2 reflected second s R seed D ξ hK bin (column l) datum first (row l)
      (hfirst l) ampExponent reserveShift εvolume hξ (hradius l hl),hzero l hl⟩
  have hzpos : 0<Z := zero_lt_one.trans hZ
  have hfactor : 0<geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin :=
    geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N lo ap ap hlo hap hap)
  have htr := he.2 reflected second s R seed W D ξ hK bin column datum first row hfirst
    β ampExponent reserveShift rawError allowance Kcontrol T width i
    (by linarith [Cycle63.Arithmetic.q0_bounds.1]) hβ' hKcontrol hT hwidthbin hinj labels
    hseed hz₁ hz₂ hsource hlower st hQM hQη z hz hpuncture hi hcard hM hb₁ hb₂ hupperB hwin
    B₁ t₁ hf₁ pick t w σ v θ p Ds cap hcap hmatches hscales hpadallow hf₂ hwidth hradial hupper
    hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad hcontrol hrawError
  have hpaid := hpay Z he.1 P.Bmask P.bΦ reflected second s hη R seed (Z^D) ξ hK bin column datum first row
    hparent hfirst hR ψ β (Cshell*Cprofile^2*Kcontrol*(2*T)^(2*ε)) rawError allowance width (32*B+|εvolume|)
    target (D*Cycle153.MarkedRootPrice.lowReserve) (3*(i+1:ℕ)*Z^P.τ) (by linarith [Cycle153.MarkedRootPrice.q_native]) hβ' (by positivity) hwidthbin (by positivity)
    hinj labels x hx hq hpoint hseed hz₁ hz₂ hsource hAbox st hQM hQη z hz hchar hpuncture hrow
    hzero' hsupport hnorm hmissing
  rw [show 32*B+|εvolume|+5*B=37*B+|εvolume| by ring] at hpaid
  calc _ ≤ geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*εmass)*
          binnedCount labels (fun l=>compensatedHighCoordinates (x l) (geometryHighSide reflected A
            (geometryExponents s R seed (Z^D) Z ξ (column l).1.val))) width
          (fun key=>Cshell*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
            Z^(exponentBinUpper width key 0+(2*β-1)*exponentBinUpper width key 3+rawError+allowance)) := htr
    _ ≤ geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^(B*εmass)*
          (((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
          (Cshell*Cprofile^2*Kcontrol*(2*T)^(2*ε)*(Ccount*(1+3*(i+1:ℕ)*Z^P.τ)^J)*
            Z^(target-D*Cycle153.MarkedRootPrice.lowReserve+4*width+loss+(rawError+allowance)))) :=
          mul_le_mul_of_nonneg_left hpaid (mul_pos hfactor (Real.rpow_pos_of_pos hzpos _)).le
    _ = _ := by
        rw [show target-D*Cycle153.MarkedRootPrice.lowReserve+4*width+loss+rawError+allowance+B*εmass=
          (target-D*Cycle153.MarkedRootPrice.lowReserve+4*width+loss+(rawError+allowance))+B*εmass by ring,
          Real.rpow_add hzpos (target-D*Cycle153.MarkedRootPrice.lowReserve+4*width+loss+(rawError+allowance)) (B*εmass)]
        ring

end
end OAI.SevenEighths.Cycle153RootHigh

#print axioms OAI.SevenEighths.Cycle153RootHigh.actual_geometry_literal_unmarked_high_shell
