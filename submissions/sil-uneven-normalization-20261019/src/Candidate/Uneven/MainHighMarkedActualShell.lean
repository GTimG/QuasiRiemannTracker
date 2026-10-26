/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainHighCoordinates
import Candidate.Uneven.MainHighParameters
import Candidate.Uneven.MainHighAdmission
import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryLiteralHighFrequency
import Candidate.Cycle63.Physical.InitialMass.GeometryZeroPartition
import Candidate.Uneven.HighMass
import Candidate.Cycle63.Physical.InitialMass.GeometryHighAdmission
import Candidate.Uneven.MainPointwise
import Candidate.Uneven.MainHighBootstrapActualShell
import Candidate.Uneven.MainHighSaturatedActualShell

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OAI.SevenEighths.MainHigh
open TargetHigh830 SaturatedPlain BootstrapPlain
open OAI.SevenEighths.Cycle63InitialMass
open Target830 Marked830Plain
noncomputable section
open Cycle63MarkedPlain
open scoped ContDiff
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
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M  ≤  H)

/-- Joint high shell payment for the literal physical child coefficient.
The zero-shell parameter β and amplifier exponent are distinct inputs. -/
theorem actual_geometry_literal_marked_high_shell {α : Type} [Fintype α] [DecidableEq α]
    (plane : Sil.Uneven.MainSource.Plane)
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hMarkedUpper : HeckeZeroSupremum.beta ≤ 7/8)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hQmax : Q ≤ 130)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0<lo)(hεmass : 0 ≤ εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Cs bs b window pad : ℝ)
    (hCs : 1 ≤ Cs)(hbs : 1 ≤ bs)(hb : 1 ≤ b)(hwindow : 0 ≤ window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      FineMarkedSchedule P N Wslot (33/50) (33/50) →
      8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
      2*P.τ*((J:ℝ)+1) ≤ 1/1000000000000 →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2 ≤ Z ∧
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
      (1+plane.q)/2 ≤ β → β  ≤  7/8 → 0  ≤  Kcontrol → 1  ≤  T → 0<width →
      Function.Injective key →
      ∀labels : Finset κ,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
        unmarkedDensity (2*β-1)*εfreq+εvolume
      (∀l∈labels,Real.logb Z ((geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)).absNorm:ℝ)+
        Real.logb Z ((if second then (datum (row l).val.1).D else (datum (row l).val.1).C).absNorm:ℝ) ≤ Sil.Uneven.MainSource.supplied bAmpl) →
      (∀l∈labels,x l 2+width ≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s ≤ Z^B → lo ≤  s.lower →
      Sil.Uneven.MainSource.widthLo ≤ bAmpl → bAmpl ≤ Sil.Uneven.MainSource.widthHi → D=1 → 0 ≤ D → |D| ≤ B → |A| ≤ B → |ampExponent| ≤ B →
      |frequencyLoss Z 32 ξ+reserveShift| ≤ B →
      frequencyLoss Z 32 ξ+reserveShift ≤ Sil.Uneven.MainSource.frequencyAllowance → εfreq ≤ B → ξ ≤ εfreq →
      A ≤ D*Sil.Uneven.MainSource.total plane bAmpl → ampExponent ≤ D*Sil.Uneven.MainSource.amp plane bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ) ≤ Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ) ≤ Z^B) →
      (∀l∈labels,(datum (row l).val.1).radius=frequencyRadius
        (firstMainFourierScale reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent)
          reserveShift b N (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) Z ξ) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus  ≤  M) (hQη : ∀ l, (st l).fixedModulus  ≤  η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, β  ≤  HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ)  ≤  Z^B) →
      i ≤ bufferCount P.e →
      (∀l∈labels,β ≤ geometryRowMaximum M H hH (st l) η₀ (hQM l) (hQη l)
        (z l) (hz l) ((3*i:ℕ)*Z^P.τ)) →
      (i:ℝ) ≤ Z^P.τ →
      Fintype.card α ≤ N → (∀j,s.M j ≤ Cs) →
      s.b₁ ≤ bs → s.b₂ ≤ bs → s.upper ≤ b →
      (∀j,logWindow (s.lo j) (s.hi j) ≤ window) →
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
      cap ≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (1/50)*D ≤ ∑j,w j →
      (∑j,w j) ≤ 1/25 →
      bAmpl-Sil.Uneven.MainSource.widthMesh ≤ ∑j,w j →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j ≤ Z^cap) →
      pad ≤ allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R₂ l)
        (firstChild l).ν (firstChild l).W (firstChild l).P≠0) →
      (∀l∈labels,(st l).width ≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<β+2*P.e) →
      (∀j,0 ≤ w j) → (∀j,w j ≤  bootstrapRawMesh*fineRawCore) →
      (∀j,w j/P.d ≤ P.Rwidth) →
      (∀j,P.σmin ≤ σ j) → (∀j,σ j ≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T ≤ (L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (firstChild l) (st l).character (t l)) (E l) (R₂ l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2 ≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ) ≤ rawError →
      (∑l∈labels,unevenFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
        coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l))) ≤ 
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(38*B+|εvolume|)/width⌋:ℤ) ⌊(38*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-D*(mainHighReserve)+4*width+loss+rawError+allowance+B*εmass)) := by
  obtain ⟨boundL,hboundL,JL,hpaidL⟩ := actual_geometry_literal_bootstrap_high_shell
    (α:=α) (bp:=bp) M H hH plane η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth
    hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume Cs bs b window pad
    hCs hbs hb hwindow hpad
  obtain ⟨boundH,hboundH,JH,hpaidH⟩ := actual_geometry_literal_saturated_high_shell
    (α:=α) (bp:=bp) M H hH plane η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth
    hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume Cs bs b window pad
    hCs hbs hb hwindow hpad
  refine ⟨boundL,hboundL,max JL JH,?_⟩
  intro P hboundeq hmarked hslot hplain hheight
  have height_cap (j : ℕ) (hj : j≤ max JL JH) : 2*P.τ*((j:ℝ)+1)≤1/1000000000000 := by
    apply le_trans ?_ hheight
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hj 1)
      (mul_nonneg (by norm_num) P.hτ.le)
  obtain ⟨FL,controlsLow,CLp,CL,hFL,hCLp,hCL,heL⟩ :=
    hpaidL P hboundeq hmarked hslot hplain (height_cap JL (le_max_left _ _))
  let PH : HighSourceParameters := {P with profileBound:=boundH,hprofile:=fun k=>(hboundH k).le}
  have hmarkedH : FineMarkedSchedule PH N Wslot (33/50) (33/50) :=
    ⟨hmarked.slot,hmarked.slotCap,hmarked.sigmaLo,hmarked.sigmaHi,hmarked.degree,
      hmarked.mask,hmarked.heightZero,hmarked.heightWitness,hmarked.buffer,hmarked.slotLoss⟩
  obtain ⟨FH,controlsHigh,CHp,CH,hFH,hCHp,hCH,heH⟩ :=
    hpaidH PH rfl hmarkedH hslot hplain (height_cap JH (le_max_right _ _))
  refine ⟨FL∪FH,controlsLow∪controlsHigh,1,CL*CLp^2+CH*CHp^2,
    Finset.mem_union.mpr (Or.inl hFL),by norm_num,by positivity,?_⟩
  filter_upwards [heL,heH] with Z hL hH
  refine ⟨hL.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width i hβ hβ'
    hKcontrol hT hwidthbin hinj labels A x target hsmall hq hseed hz₁ hz₂ hsource hlower
    hbAmpl hbAmpl' hDunit hD hDbox hAbox hampbox hω hωsmall hεbox hξ hA hamp hsecond hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hM hb₁ hb₂ hupperB hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild coeff E R₂ pick t w σ v θ p Ds cap
    hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow hf₂ hwidth hradial hupper hw hmesh hwr hσlo hσhi hfreq hplainfreq
    hW hDs hdyad src hcontrol hrawError
  have hZ : 1<Z := by linarith [hL.1]
  have hzpos : 0<Z := zero_lt_one.trans hZ
  have hcL (l : κ)(hl : l∈labels) : ((p l).control controlsLow)^2*(2*bs*Cs^N)^2≤Kcontrol := by
    apply le_trans ?_ (hcontrol l hl)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ((p l).control_nonneg _)
      (CenteredMomentEnergyBandMonotonicity.profile_control_mono (p l)
        (Finset.subset_union_left : controlsLow⊆controlsLow∪controlsHigh)) 2) (sq_nonneg _)
  have hcH (l : κ)(hl : l∈labels) : ((p l).control controlsHigh)^2*(2*bs*Cs^N)^2≤Kcontrol := by
    apply le_trans ?_ (hcontrol l hl)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ((p l).control_nonneg _)
      (CenteredMomentEnergyBandMonotonicity.profile_control_mono (p l)
        (Finset.subset_union_right : controlsHigh⊆controlsLow∪controlsHigh)) 2) (sq_nonneg _)
  let summand := fun l=>unevenFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
    coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,retainedAllocationCost (src l) L alloc (z l))
  let factor := geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(38*B+|εvolume|)/width⌋:ℤ) ⌊(38*B+|εvolume|)/width⌋).card^4:ℕ)
  let ht := 1+3*(i+1:ℕ)*Z^P.τ
  let rest := Kcontrol*(2*T)^(2*ε)*
    Z^(target-D*mainHighReserve+4*width+loss+rawError+allowance+B*εmass)
  have hfactor : 0≤factor := by
    dsimp only [factor]
    exact mul_nonneg (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le (Nat.cast_nonneg _)
  have hht : 1≤ht := by dsimp only [ht]; exact le_add_of_nonneg_right (by positivity)
  have hrest : 0≤rest := by dsimp only [rest]; positivity
  have upgrade (Csub : ℝ) (j : ℕ) (hc : Csub≤CL*CLp^2+CH*CHp^2) (hj : j≤ max JL JH)
      (hh : (∑l∈labels,summand l)≤factor*Csub*ht^j*rest) :
      (∑l∈labels,summand l)≤factor*(CL*CLp^2+CH*CHp^2)*ht^(max JL JH)*rest := by
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ hrest
    exact mul_le_mul (mul_le_mul_of_nonneg_left hc hfactor)
      (pow_le_pow_right₀ hht hj) (pow_nonneg (by linarith) _) (by positivity)
  have hfinal : (∑l∈labels,summand l)≤factor*(CL*CLp^2+CH*CHp^2)*ht^(max JL JH)*rest := by
    by_cases hsplit : β≤83/100
    · have hh:=hL.2 reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
        β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width i hβ hsplit
        hKcontrol hT hwidthbin hinj labels hsmall hq hseed hz₁ hz₂ hsource hlower
        hbAmpl hbAmpl' hDunit hD hDbox hAbox hampbox hω hωsmall hεbox hξ hA hamp hsecond hradius
        st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hM hb₁ hb₂ hupperB hwin
        B₁ t₁ hf₁ pick t w σ v θ p Ds cap hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow
        hf₂ hwidth hradial hupper hw hmesh hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad hcL hrawError
      apply upgrade (CL*CLp^2) JL (le_add_of_nonneg_right (by positivity)) (le_max_left _ _)
      convert hh using 1 <;> dsimp only [summand,factor,ht,rest] <;> ring
    · have hmeshH : ∀j,w j≤fineRawMesh*fineRawCore := by
        intro j
        exact (hmesh j).trans (mul_le_mul_of_nonneg_right
          (show bootstrapRawMesh≤fineRawMesh from min_le_left _ _)
          (by norm_num [fineRawCore]))
      have hh:=hH.2 reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
        β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width i (le_of_lt (lt_of_not_ge hsplit)) hβ'
        hKcontrol hT hwidthbin hinj labels hsmall hq hseed hz₁ hz₂ hsource hlower
        hbAmpl hbAmpl' hDunit hD hDbox hAbox hampbox hω hωsmall hεbox hξ hA hamp hsecond hradius
        st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hM hb₁ hb₂ hupperB hwin
        B₁ t₁ hf₁ pick t w σ v θ p Ds cap hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow
        hf₂ hwidth hradial hupper hw hmeshH hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad hcH hrawError
      apply upgrade (CH*CHp^2) JH (le_add_of_nonneg_left (by positivity)) (le_max_right _ _)
      convert hh using 1 <;> dsimp only [summand,factor,ht,rest] <;> ring
  change (∑l∈labels,summand l)≤_
  convert hfinal using 1 <;> dsimp only [factor,ht,rest] <;> ring

end
end OAI.SevenEighths.MainHigh
