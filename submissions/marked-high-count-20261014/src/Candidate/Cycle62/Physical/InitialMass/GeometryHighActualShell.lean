import Candidate.Cycle62.Physical.InitialMass.GeometryMarkedActualShell
import Candidate.Cycle62.Physical.InitialMass.GeometryHighBranchJoin
import Candidate.Cycle62.Physical.InitialMass.GeometryLiteralHighFrequency
import Candidate.Cycle62.Physical.InitialMass.GeometryZeroPartition
import Candidate.Cycle62.Physical.InitialMass.GeometryHighPayment
import Candidate.Cycle62.Physical.InitialMass.GeometryHighAdmission

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open Cycle62MarkedPlain
open scoped ContDiff
open scoped Classical BigOperators SchwartzMap
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle62HighProfiles Cycle62FinalLow CenteredMomentFiniteProfileExceptional
open Cycle62HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle62Moment
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
theorem actual_geometry_literal_high_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : 51/100≤HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1≤94/125)
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
      2*P.τ*((J:ℝ)+1)≤1/800000000 →
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
      (∀l∈labels,x l 2+width≤Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B → lo≤s.lower →
      3401/100000≤bAmpl → bAmpl≤1/25 → D=1 → 0≤D → |D|≤B → |A|≤B → |ampExponent|≤B →
      |frequencyLoss Z 32 ξ+reserveShift|≤B →
      frequencyLoss Z 32 ξ+reserveShift≤1/1000 → εfreq≤B → ξ≤εfreq →
      A≤D*Cycle62.Arithmetic.totalA bAmpl → ampExponent≤D*Cycle62.Arithmetic.amp bAmpl →
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
      (∀second j,Cycle62.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
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
      (∀j,0≤w j) → (∀j,w j≤ markedRawMesh*markedCoreMin) →
      (∀j,w j/P.d≤P.Rwidth) →
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
  obtain ⟨boundM,hboundM,JM,hmarked⟩ := actual_geometry_literal_marked_high_shell
    (α:=α) (bp:=bp) M H hH η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth
    hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume Cs bs b window pad
    hCs hbs hb hwindow hpad
  obtain ⟨boundU,hboundU,JU,hunmarked⟩ := actual_geometry_literal_unmarked_high_shell
    (α:=α) (bp:=bp) M H hH η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume Cs bs b window pad
    hCs hbs hb hwindow hpad
  refine ⟨boundM,hboundM,max JU JM,?_⟩
  intro P hboundeq hsched hslot hplain hheight
  have hmheight : 2*P.τ*((JM:ℝ)+1)≤1/800000000 := by
    apply le_trans ?_ hheight
    have hJM : (JM:ℝ)≤(max JU JM:ℕ) := Nat.cast_le.mpr (le_max_right JU JM)
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by norm_num) P.hτ.le)
  obtain ⟨FM,GM,CMp,CM,hFM,hCMp,hCM,heM⟩ := hmarked P hboundeq hsched hslot hplain hmheight
  let PU : HighSourceParameters := {P with profileBound:=boundU,hprofile:=fun k=>(hboundU k).le}
  obtain ⟨FU,GU,CUp,CU,hFU,hCUp,hCU,heU⟩ := hunmarked PU rfl hslot hplain
  refine ⟨FM∪FU,GM∪GU,1,CU*CUp^2+CM*CMp^2,
    Finset.mem_union.mpr (Or.inl hFM),by norm_num,by positivity,?_⟩
  filter_upwards [heU,heM] with Z hU hM
  refine ⟨hM.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width i hβ hβ'
    hKcontrol hT hwidthbin hinj labels A x target hq hseed hz₁ hz₂ hsource hlower
    hbAmpl hbAmpl' hDunit hD hDbox hAbox hampbox hω hωsmall hεbox hξ hA hamp hsecond hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hMs hb₁ hb₂ hupperB hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild coeff E R₂ pick t w σ v θ p Ds cap
    hcap hmatches hsupply hsupplyUpper hscales hpadallow hf₂ hwidth hradial hupper hw hmesh hwr hσlo hσhi hfreq hplainfreq
    hW hDs hdyad src hcontrol hrawError
  have hZ : 1<Z := by linarith [hM.1]
  have hzpos : 0<Z := zero_lt_one.trans hZ
  have hcM (l : κ)(hl : l∈labels) : ((p l).control GM)^2*(2*bs*Cs^N)^2≤Kcontrol := by
    apply le_trans ?_ (hcontrol l hl)
    have hh:=CenteredMomentEnergyBandMonotonicity.profile_control_mono (p l)
      (Finset.subset_union_left : GM⊆GM∪GU)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ((p l).control_nonneg _) hh 2) (sq_nonneg _)
  have hcU (l : κ)(hl : l∈labels) : ((p l).control GU)^2*(2*bs*Cs^N)^2≤Kcontrol := by
    apply le_trans ?_ (hcontrol l hl)
    have hh:=CenteredMomentEnergyBandMonotonicity.profile_control_mono (p l)
      (Finset.subset_union_right : GU⊆GM∪GU)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ((p l).control_nonneg _) hh 2) (sq_nonneg _)
  let removed := fun l=>Real.logb Z ((C₁ l).absNorm:ℝ)+Real.logb Z ((E l).absNorm:ℝ)
  let summand := fun l=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
    coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,retainedAllocationCost (src l) L alloc (z l))
  let factor := geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)
  let ht := 1+3*(i+1:ℕ)*Z^P.τ
  let rest := Kcontrol*(2*T)^(2*ε)*
    Z^(target-D*(720486667/30493190000000)+4*width+loss+rawError+allowance+B*εmass)
  have hfactor : 0≤factor := by
    dsimp only [factor]
    exact mul_nonneg (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le (Nat.cast_nonneg _)
  have hht : 1≤ht := by
    dsimp only [ht]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (Real.rpow_nonneg hzpos.le _))
  have hrest : 0≤rest := by dsimp only [rest];positivity
  have hhU : ht^JU≤ht^(max JU JM) := pow_le_pow_right₀ hht (le_max_left _ _)
  have hhM : ht^JM≤ht^(max JU JM) := pow_le_pow_right₀ hht (le_max_right _ _)
  have unmarked (ls : Finset κ)(hls : ls⊆labels)
      (hbranch : 7/10≤2*β-1 ∨ ∀l∈ls,33/1000≤removed l) :
      (∑l∈ls,summand l)≤factor*(CU*CUp^2)*ht^(max JU JM)*rest := by
    have hb : 7/10≤2*β-1 ∨ ∀l∈ls,33*D/1000≤removed l := by
      simpa only [hDunit,mul_one] using hbranch
    have hh:=hU.2 reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
      β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width i hβ hβ'
      hKcontrol hT hwidthbin hinj ls hb
      (fun l hl=>hq l (hls hl)) hseed hz₁ hz₂ hsource hlower
      hbAmpl hbAmpl' hDunit hD hDbox hAbox hampbox hω hεbox hξ hA hamp
      (fun l hl=>hsecond l (hls hl)) (fun l hl=>hradius l (hls hl))
      st hQM hQη z hz hchar hpuncture hrow (fun l hl=>hzero l (hls hl))
      (fun l hl=>hsupport l (hls hl)) hibuffer (fun l hl=>hcurrent l (hls hl)) hi
      hcard hMs hb₁ hb₂ hupperB hwin B₁ t₁ (fun l hl=>hf₁ l (hls hl))
      pick t w σ v θ p Ds cap hcap hmatches hsupply hsupplyUpper hscales hpadallow
      (fun l hl=>hf₂ l (hls hl)) (fun l hl=>hwidth l (hls hl))
      (fun l hl=>hradial l (hls hl)) (fun l hl=>hupper l (hls hl)) hw hwr hσlo hσhi
      (fun l hl=>hfreq l (hls hl)) (fun l hl=>hplainfreq l (hls hl))
      (fun l hl=>hW l (hls hl)) (fun l hl=>hDs l (hls hl)) (fun l hl=>hdyad l (hls hl))
      (fun l hl=>hcU l (hls hl)) hrawError
    have heq : factor*(CU*CUp^2)*ht^JU*rest=
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (CU*CUp^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^JU*(2*T)^(2*ε)*
          Z^(target-D*(720486667/30493190000000)+4*width+loss+rawError+allowance+B*εmass)) := by
      dsimp only [factor,ht,rest];ring
    change (∑l∈ls,summand l)≤_ at hh
    rw [←heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hhU (by positivity)) hrest)
  have marked (ls : Finset κ)(hls : ls⊆labels)(hβm : β≤17/20)
      (hsmall : ∀l∈ls,removed l≤33/1000) :
      (∑l∈ls,summand l)≤factor*(CM*CMp^2)*ht^(max JU JM)*rest := by
    have hh:=hM.2 reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
      β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width i hβ hβm
      hKcontrol hT hwidthbin hinj ls hsmall
      (fun l hl=>hq l (hls hl)) hseed hz₁ hz₂ hsource hlower
      hbAmpl hbAmpl' hDunit hD hDbox hAbox hampbox hω hωsmall hεbox hξ hA hamp
      (fun l hl=>hsecond l (hls hl)) (fun l hl=>hradius l (hls hl))
      st hQM hQη z hz hchar hpuncture hrow (fun l hl=>hzero l (hls hl))
      (fun l hl=>hsupport l (hls hl)) hibuffer (fun l hl=>hcurrent l (hls hl)) hi
      hcard hMs hb₁ hb₂ hupperB hwin B₁ t₁ (fun l hl=>hf₁ l (hls hl))
      pick t w σ v θ p Ds cap hcap hmatches hsupply hsupplyUpper hscales hpadallow
      (fun l hl=>hf₂ l (hls hl)) (fun l hl=>hwidth l (hls hl))
      (fun l hl=>hradial l (hls hl)) (fun l hl=>hupper l (hls hl)) hw hmesh hwr hσlo hσhi
      (fun l hl=>hfreq l (hls hl)) (fun l hl=>hplainfreq l (hls hl))
      (fun l hl=>hW l (hls hl)) (fun l hl=>hDs l (hls hl)) (fun l hl=>hdyad l (hls hl))
      (fun l hl=>hcM l (hls hl)) hrawError
    have heq : factor*(CM*CMp^2)*ht^JM*rest=
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (CM*CMp^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^JM*(2*T)^(2*ε)*
          Z^(target-D*(720486667/30493190000000)+4*width+loss+rawError+allowance+B*εmass)) := by
      dsimp only [factor,ht,rest];ring
    change (∑l∈ls,summand l)≤_ at hh
    rw [←heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hhM (by positivity)) hrest)
  have hresult : (∑l∈labels,summand l)≤factor*(CU*CUp^2+CM*CMp^2)*ht^(max JU JM)*rest := by
    have hh:=high_branch_sum_join labels summand removed (2*β-1) factor (CU*CUp^2) (CM*CMp^2)
      ht rest (max JU JM) (max JU JM) hfactor (by positivity) (by positivity) hht hrest
      unmarked (fun ls hls hd hs=>marked ls hls (by linarith) hs)
    simpa only [max_self] using hh
  change (∑l∈labels,summand l)≤_
  convert hresult using 1 <;> dsimp only [factor,ht,rest] <;> ring

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_literal_high_shell
