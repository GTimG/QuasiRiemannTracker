/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainHighCoordinates
import Candidate.Target830.Marked.Schedule
import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule
import Candidate.Uneven.MainHighMainFull
import Candidate.Cycle63.Physical.InitialMass.GeometryHighCostNormalization
import Candidate.Cycle63.Physical.InitialMass.SecondProjectorShell

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.MainHigh
open TargetHigh830 SaturatedPlain BootstrapPlain
open OAI.SevenEighths.Cycle63InitialMass
open Target830 Marked830Plain
noncomputable section
open Cycle63MarkedPlain
open scoped ContDiff
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

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

open CenteredMomentCommonPairedSource CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonWindowColumn CenteredMomentHeckeColumnWindow FourierBridge

open CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
open CenteredMomentSecondInputCapacitySource

private theorem buffered_projector_scale_mono
    (a b c d e f g h s t ε : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 ≤ g) (hh : 0 ≤ h)
    (hs : 0 ≤  s) (hst : s ≤ t) (hε : 0 ≤ ε) :
    a*(b*(c*(2*s)^ε*d*e*(f*(g*(2*s)^(2*ε)*h)))) ≤ 
    a*(b*(c*(2*t)^ε*d*e*(f*(g*(2*t)^(2*ε)*h)))) := by
  have ht : 0 ≤ t:=hs.trans hst
  gcongr

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M  ≤  H)

/-- All high buffered bins share one projector union. Its shell count is
paid once, preserving the physical side factor and original row weights. -/
theorem actual_geometry_main_high_buffered_projectors {α : Type} [Fintype α] [DecidableEq α]
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
    (Lprojector εprojector : ℝ) (hLprojector : 0 ≤ Lprojector) (hεprojector : 0<εprojector)
    (Cs bs b window pad : ℝ)
    (hCs : 1 ≤ Cs)(hbs : 1 ≤ bs)(hb : 1 ≤ b)(hwindow : 0 ≤ window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀heightloss : ℝ,∀P : HighSourceParameters,P.profileBound=bound →
      FineMarkedSchedule P N Wslot (33/50) (33/50) →
      8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
      2*P.τ*((J:ℝ)+1) ≤ 1/1000000000000 → 2*P.τ*(J+1) ≤ heightloss →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧ 0<Kcolumn ∧
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
        (ampExponent reserveShift bAmpl rawError allowance Kcontrol width Wfiber : ℝ),
      0 ≤ ξ → 0 ≤ reserveShift → 0  ≤  Kcontrol → 0<width →
      0 ≤ Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ) ≤ Wfiber) →
      ∀select : κ→BufferIndex P.e,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      (∀l∈labels,x l 2+width ≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s ≤ Z^B → lo ≤  s.lower →
      Sil.Uneven.MainSource.widthLo ≤ bAmpl → bAmpl ≤ Sil.Uneven.MainSource.widthHi → D=1 → 0 ≤ D → |D| ≤ B → |A| ≤ B → |ampExponent| ≤ B →
      |frequencyLoss Z 32 ξ+reserveShift| ≤ B → frequencyLoss Z 32 ξ+reserveShift ≤ Sil.Uneven.MainSource.frequencyAllowance → εfreq ≤ B → ξ ≤ εfreq →
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
      (∀l∈labels,GeometryZeroBin M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
        P.e (Z^P.τ) (select l)) →
      (∀l∈labels,(1+plane.q)/2 ≤ bufferValue P.e (select l)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ)  ≤  Z^B) →
      (∀l∈labels,((select l).1.val:ℝ) ≤ Z^P.τ) →
      Fintype.card α ≤ N → (∀j,s.M j ≤ Cs) →
      s.b₁ ≤ bs → s.b₂ ≤ bs → s.upper ≤ b →
      (∀j,logWindow (s.lo j) (s.hi j) ≤ window) →
      let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
      let χ₁:=fun l=>geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l)
      ∀(B₁ : ∀l,actualAllocations s.pools (C₁ l))(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0) →
      let firstChild:=fun l=>child s (C₁ l) R (B₁ l) (χ₁ l) (t₁ l)
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      ∀(seed₂ : κ→Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap : ℝ),
      cap ≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (1/50)*D ≤ ∑j,w j →
      (∑j,w j) ≤ 1/25 →
      bAmpl-Sil.Uneven.MainSource.widthMesh ≤ ∑j,w j →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j ≤ Z^cap) →
      pad ≤ allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width ≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀j,0 ≤ w j) → (∀j,w j ≤  bootstrapRawMesh*fineRawCore) →
      (∀j,w j/P.d ≤ P.Rwidth) →
      (∀j,P.σmin ≤ σ j) → (∀j,σ j ≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2 ≤ (3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2 ≤ (3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,(L.absNorm:ℝ) ≤ Z^Lprojector) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2 ≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ) ≤ rawError →
      ∀(t₀ u : ℝ),
      (∀l∈labels,(datum (row l).val.1).slots=liveIndices (B₁ l).val) →
      (∀l∈labels,HEq (datum (row l).val.1).input (firstChild l)) →
      (∀l∈labels,(datum (row l).val.1).K=firstMainRadius reflected (Z^D) (volume s) Z ξ
        (3*ampExponent) reserveShift (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) →
      (∀l∈labels,seed₂ l=(datum (row l).val.1).seed) →
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      (∀l∈labels,t l=(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))) →
      Z^(-ampExponent)*(∑l∈labels,∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>unevenFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L) ≤ 
      (Fintype.card (BufferIndex P.e):ℝ)*((1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*Z^εprojector*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(38*B+|εvolume|)/width⌋:ℤ) ⌊(38*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(2*Z^Lprojector)^(2*ε)*
          Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(mainHighReserve)+4*width+loss+rawError+allowance+B*εmass+heightloss)))))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_main_high_buffered_shell (α:=α) M H hH plane
    η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
     N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  obtain ⟨Cp,hCp,hprojectors⟩:=shared_projector_shell_payment Lprojector εprojector hLprojector hεprojector
  refine ⟨bound,hbound,J,?_⟩
  intro heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hjoint⟩:=hhigh heightloss P hboundeq hmarked hslot hplain hmarkedHeight hdensity
  refine ⟨F,G,Cprofile,C,Cp*Kcolumn,hF,hCprofile,hC,by positivity,?_⟩
  filter_upwards [hjoint,hprojectors] with Z he hp
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key ampExponent reserveShift bAmpl rawError allowance Kcontrol width Wfiber
    hξ hreserve hKcontrol hwidthbin hWfiber labels hfiber select A x hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hDunit hD hDcap hA hamp homega homegaSmall hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E seed₂ t w σ v θ p Ds cap hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow
    hseed₂ hwidth hradial hw hwmarked hwr hσlo hσhi hheight hplainheight hW hDs hnormL hcontrol hledger
    t₀ u hslots hinput hKm hseedid hψ hshift
  let projectors : labels→Finset (Ideal O):=fun l=>Ds l.val
  let cost (l : labels) (L : Ideal O):=Z^(-ampExponent)*mainNormalizedPhysicalCost N lo ap second datum
    (fun _=>unevenFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l.val)/
      volume (datum (row l.val).val.1).input) t₀ u (row l.val).val L
  let Ebound:=(Fintype.card (BufferIndex P.e):ℝ)*((1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*(
    geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(38*B+|εvolume|)/width⌋:ℤ) ⌊(38*B+|εvolume|)/width⌋).card^4:ℕ)*
      (C*Cprofile^2*Kcontrol*(2*Z^Lprojector)^(2*ε)*
        Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(mainHighReserve)+4*width+loss+rawError+allowance+B*εmass+heightloss))))))
  have hZpos : 0<Z:=zero_lt_one.trans hp.1
  have hfactor : 0 ≤ geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin:=
    (geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
  have hLower:0<lowerFactor N lo ap:=lowerFactor_pos N lo ap hlo hap
  have hEbound : 0 ≤ Ebound:=by
    dsimp only [Ebound]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply mul_nonneg (one_div_nonneg.mpr hLower.le)
    apply mul_nonneg hWfiber
    apply mul_nonneg (by positivity)
    apply mul_nonneg (mul_nonneg hfactor (Nat.cast_nonneg _))
    positivity
  have hc (l : labels) (L : Ideal O) : 0 ≤ cost l L := by
    have hm:=uneven_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l.val) hZpos.le
    have hv:0<volume (datum (row l.val).val.1).input:=CenteredMomentAmplificationChildInput.volume_pos _
    have hl:0<lowerFactor N lo ap:=lowerFactor_pos N lo ap hlo hap
    have hk:0<(datum (row l.val).val.1).K:=(datum (row l.val).val.1).K_pos
    have hn:=normalizer_pos _ _ (datum (row l.val).val.1).hC (datum (row l.val).val.1).inactive
    dsimp only [cost,mainNormalizedPhysicalCost]
    apply mul_nonneg (Real.rpow_nonneg hZpos.le _)
    apply mul_nonneg (by positivity)
    split <;> exact sq_nonneg _
  have hnormp : ∀l : labels,∀L∈projectors l,(L.absNorm:ℝ) ≤ Z^Lprojector:=
    fun l L hL=>hnormL l.val l.property L hL
  have hpay (n : ℤ) (hn : n∈selectedShells (sharedProjectors projectors)) :
      (∑l : labels,∑L∈shell (sharedProjectors projectors) n,cost l L) ≤ Ebound := by
    have hscale:=shared_projector_shell_scale projectors Z Lprojector hnormp n hn
    have hh:=he.2 reflected second s hη R seed W D ξ hK bin column datum first row
      hparent hfirst hR ψ ampExponent reserveShift bAmpl rawError allowance Kcontrol
      (dyadicScale n) width Wfiber hξ hreserve hKcontrol hscale.1 hwidthbin hWfiber labels hfiber select
      hq hseed hs₁ hs₂ hsource hlower hbAmpl hbAmpl' hDunit hD hDcap hA hamp homega homegaSmall hεfreqB hξε htotalA hampcap hnorm hradius
      st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
      B₁ t₁ hf₁ seed₂ t w σ v θ p (fun _=>shell (sharedProjectors projectors) n) cap
      hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow hseed₂ hwidth hradial hw hwmarked hwr hσlo hσhi hheight hplainheight hW
      (fun _ _ L hL=>(shared_projector_shell_gates projectors n L hL).1)
      (fun _ _ L hL=>(shared_projector_shell_gates projectors n L hL).2.2)
      hcontrol hledger t₀ u hslots hinput hKm hseedid hψ hshift
    have hleft : (∑l : labels,∑L∈shell (sharedProjectors projectors) n,cost l L)=
        Z^(-ampExponent)*(∑l∈labels,∑L∈shell (sharedProjectors projectors) n,
          mainNormalizedPhysicalCost N lo ap second datum
            (fun _=>unevenFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
              volume (datum (row l).val.1).input) t₀ u (row l).val L) := by
      dsimp only [cost]
      simp only [←Finset.mul_sum]
      congr 1
      exact Finset.sum_coe_sort labels (fun l=>∑L∈shell (sharedProjectors projectors) n,
        mainNormalizedPhysicalCost N lo ap second datum
          (fun _=>unevenFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
            volume (datum (row l).val.1).input) t₀ u (row l).val L)
    rw [hleft]
    apply hh.trans
    dsimp only [Ebound]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply buffered_projector_scale_mono
      (1/lowerFactor N lo ap) Wfiber Kcolumn (Cs^(2*N)) (Z^(B*ε))
      (geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        ((Finset.Icc (⌊-(38*B+|εvolume|)/width⌋:ℤ) ⌊(38*B+|εvolume|)/width⌋).card^4:ℕ))
      (C*Cprofile^2*Kcontrol)
      (Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(mainHighReserve)+4*width+loss+rawError+allowance+B*εmass+heightloss))
      (dyadicScale n) (Z^Lprojector) ε
    · exact one_div_nonneg.mpr hLower.le
    · exact hWfiber
    · exact hKcolumn.le
    · positivity
    · exact Real.rpow_nonneg hZpos.le _
    · exact mul_nonneg hfactor (Nat.cast_nonneg _)
    · positivity
    · exact Real.rpow_nonneg hZpos.le _
    · exact zero_le_one.trans hscale.1
    · exact hscale.2
    · exact hε.le
  have hpaid:=hp.2 projectors (fun l L hL=>hDs l.val l.property L hL)
    hnormp cost Ebound hc hEbound hpay
  have hleft : Z^(-ampExponent)*(∑l∈labels,∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
      (fun _=>unevenFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
        volume (datum (row l).val.1).input) t₀ u (row l).val L)=
      ∑l : labels,∑L∈projectors l,cost l L := by
    dsimp only [cost,projectors]
    simp only [←Finset.mul_sum]
    congr 1
    exact (Finset.sum_coe_sort labels (fun l=>∑L∈Ds l,
      mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>unevenFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)).symm
  rw [hleft]
  apply hpaid.trans_eq
  dsimp only [Ebound]
  ring


end
end OAI.SevenEighths.MainHigh
