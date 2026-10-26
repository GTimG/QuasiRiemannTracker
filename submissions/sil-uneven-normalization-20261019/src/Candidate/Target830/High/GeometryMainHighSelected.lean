import Candidate.Target830.High.Coordinates
import Candidate.Target830.Marked.Schedule
import Candidate.Cycle63.Physical.InitialMass.MarkedSchedule
import Candidate.Target830.High.GeometryHighNormalized
import Candidate.Cycle63.Physical.InitialMass.GeometryHighCostNormalization
import Candidate.Cycle63.Physical.InitialMass.SecondProjectorShell

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.TargetHigh830
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

private theorem main_high_projector_scale_mono
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

/-- Literal source identification, including the signed row and shifted
height, converts the analytic column cost to the amplified physical cost. -/
theorem main_high_physical_column_identity
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (lo ap Z amp mass K : ℝ) (_hZ : 0<Z) (second : Bool)
    (d : Label→SecondInputDatum α) (r : secondLiveRows (fun l=>(d l).block))
    (slots : Finset α) (source : Input slots)
    (hslots : (d r.val.1).slots=slots) (hinput : HEq (d r.val.1).input source)
    (hK : (d r.val.1).K=K)
    (τ : Character) (hτ : τ=(d r.val.1).τ
      (if second then r.val.2.2.1⁻¹ else r.val.2.1))
    (z : O) (hz : z=if second then -r.val.2.2.2.val else r.val.2.2.2.val)
    (seed₂ : Ideal O) (hseed : seed₂=(d r.val.1).seed)
    (t₀ u t : ℝ) (ht : t=(d r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
    (Ds : Finset (Ideal O)) :
    let E:=if second then (d r.val.1).D else (d r.val.1).C
    let hE : Supported E:=by cases second; exact (d r.val.1).hC; exact (d r.val.1).hD
    Z^(-amp)*(∑L∈Ds,mainNormalizedPhysicalCost N lo ap second d
      (fun _=>mass/volume (d r.val.1).input) t₀ u r.val L)=
      (1/lowerFactor N lo ap)*(mass*(Z^(-amp)*(K/volume source)*
        normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        ∑L∈Ds,‖normalizedColumn (withHeight source τ t) E hE
          (d r.val.1).R seed₂ L z‖^2) := by
  intro E hE
  subst slots
  have hi : (d r.val.1).input=source:=eq_of_heq hinput
  subst source
  subst τ z seed₂ t K
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  cases second <;>
    simp only [mainNormalizedPhysicalCost,E,Bool.false_eq_true,ite_false,ite_true] <;> ring

/-- Genuine high-density payment for a finite selected physical row shell.
The exact original datum/source identification restores no amplification loss;
first scalar mass and the complete outer normalizer remain inside the joint sum. -/
theorem actual_geometry_main_high_selected_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1 ≤ 3/4)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hQmax : Q ≤ 130)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (plane : SourcePlane)(N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0<lo)(hεmass : 0 ≤ εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Cs bs b window pad : ℝ)
    (hCs : 1 ≤ Cs)(hbs : 1 ≤ bs)(hb : 1 ≤ b)(hwindow : 0 ≤ window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      MarkedSchedule830 P N Wslot (33/50) (33/50) →
      8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
      2*P.τ*((J:ℝ)+1) ≤ 1/1000000000 →
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
        (β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber : ℝ) (i : ℕ),
      (1+plane.q)/2  ≤  β → β  ≤  7/8 → 0  ≤  Kcontrol → 1  ≤  T → 0<width →
      0 ≤ Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ) ≤ Wfiber) →
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
        unmarkedDensity (2*β-1)*εfreq+εvolume
      (∀l∈labels,x l 2+width ≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s ≤ Z^B → lo ≤  s.lower →
      17/500 ≤ bAmpl → bAmpl ≤ 1/25 → D=1 → 0 ≤ D → |D| ≤ B → |A| ≤ B → |ampExponent| ≤ B →
      |frequencyLoss Z 32 ξ+reserveShift| ≤ B → frequencyLoss Z 32 ξ+reserveShift ≤ frequencyAllowance → εfreq ≤ B → ξ ≤ εfreq →
      A ≤ D*plane.total bAmpl → ampExponent ≤ D*plane.amp bAmpl →
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
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      ∀(seed₂ : κ→Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap : ℝ),
      cap ≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (17/500)*D ≤ ∑j,w j →
      (∑j,w j) ≤ 1/25 →
      bAmpl-sourceWidthMesh ≤ ∑j,w j →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j ≤ Z^cap) →
      pad ≤ allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width ≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<β+2*P.e) →
      (∀j,0 ≤ w j) → (∀j,w j ≤  rawMesh830*rawCore830) →
      (∀j,w j/P.d ≤ P.Rwidth) →
      (∀j,P.σmin ≤ σ j) → (∀j,σ j ≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T ≤ (L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
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
        (fun _=>balancedFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L) ≤ 
      (1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-D*(highReserve)+4*width+loss+rawError+allowance+B*εmass))))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_full_high_columns (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
    plane N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hmarked hslot hplain hmarkedHeight
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hjoint⟩:=hhigh P hboundeq hmarked hslot hplain hmarkedHeight
  refine ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber i
    hβ hβ' hKcontrol hT hwidthbin hWfiber labels hfiber A x target hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hDunit hD hDcap hA hamp homega homegaSmall hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E seed₂ t w σ v θ p Ds cap hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow
    hseed₂ hwidth hradial hzeroUpper hw hwmarked hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
    t₀ u hslots hinput hKm hseedid hψ hshift
  let R₂:=fun l=>(datum (row l).val.1).R
  let outer:=fun l=>Z^(-ampExponent)*
    (firstMainRadius reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent) reserveShift
      (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))/volume (firstChild l))*
      normalizer (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
  let hE : ∀l,Supported (E l):=fun l=>by
    dsimp only [E]; split <;> first | exact (datum (row l).val.1).hD | exact (datum (row l).val.1).hC
  have hh:=he.2 reflected second s hη R seed W D ξ hK bin column datum first row
    hparent hfirst hR ψ β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber i
    hβ hβ' hKcontrol hT hwidthbin hWfiber labels hfiber hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hDunit hD hDcap hA hamp homega homegaSmall hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hM hb₁ hb₂ hupper hwin
    B₁ t₁ hf₁ seed₂ t w σ v θ p Ds cap hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow hseed₂ hwidth hradial
    hzeroUpper hw hwmarked hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
  have hZpos : 0<Z:= (by norm_num : (0:ℝ)<2).trans_le he.1
  have heq (l : κ) (hl : l∈labels) := main_high_physical_column_identity N lo ap Z ampExponent
    (balancedFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l))
    (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*ampExponent) reserveShift
      (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) hZpos second datum (row l)
    (liveIndices (B₁ l).val) (firstChild l) (hslots l hl) (hinput l hl) (hKm l hl)
    (st l).character (by rw [hchar l,hψ l hl]) (z l) (hrow l) (seed₂ l) (hseedid l hl)
    t₀ u (t l) (hshift l hl) (Ds l)
  have hleft : Z^(-ampExponent)*(∑l∈labels,∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
      (fun _=>balancedFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
        volume (datum (row l).val.1).input) t₀ u (row l).val L)=
      (1/lowerFactor N lo ap)*(∑l∈labels,balancedFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
        outer l*(∑L∈Ds l,‖normalizedColumn (withHeight (firstChild l) (st l).character (t l))
          (E l) (hE l) (R₂ l) (seed₂ l) L (z l)‖^2)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    simpa only [Finset.mul_sum,outer,R₂,E,CenteredMomentExceptionalAmplitudePair.volume,
      CenteredMomentAmplificationChildInput.volume] using heq l hl
  rw [hleft]
  exact mul_le_mul_of_nonneg_left hh (one_div_nonneg.mpr (lowerFactor_pos N lo ap hlo hap).le)

/-- Ordinary restriction preserves the original physical child, radius and
projector. These identities need no nonzero restricted-block hypothesis. -/
theorem actual_geometry_main_high_datum_identification
    {α : Type*} [Fintype α] [DecidableEq α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
    (bin : ℤ×(Fin 5→ℤ)) (hs₁ : s.W₁ 0=0) (hs₂ : s.W₂ 0=0)
    (χ₀ : RayCharacter) (Q₀ : Ideal O) (m : O)
    (j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin) :
    let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
    let d:=geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin
      hs₁ hs₂ χ₀ Q₀ m j
    let source:=geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ hK bin t j.1
    let label:=geometryFirstLabel s R seed (Z^Mrow) Z ξ hK bin j.1.1.val
    d.slots=liveIndices j.1.2.val ∧ HEq d.input source ∧
      d.K=firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve label ∧
      d.seed=j.1.1.val.2.1.val ∧
      d.R=R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK bin j.1.1.val ∧
      d.input.η=geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ hK bin j.1.1.val ∧
      d.input.t=t ∧
      d.radius=frequencyRadius (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ
        (3*amp) reserve b N label) Z ξ :=
  ⟨rfl,HEq.rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Complete second-projector payment uses a single union before dyads.
The genuine high-density estimate pays every shell jointly; no first-label
cardinality and no assumed selected-energy bound enter the conclusion. -/
theorem actual_geometry_main_high_selected_projectors {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (Wslot : ℝ→ℂ)(hWslotSupport : Function.support Wslot⊆Set.Icc (1:ℝ) 2)
    (hWslotSmooth : ContDiff ℝ ∞ Wslot)
    (hMarkedBeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hMarkedUpper : 2*HeckeZeroSupremum.beta-1 ≤ 3/4)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hQmax : Q ≤ 130)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (plane : SourcePlane)(N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0<lo)(hεmass : 0 ≤ εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Lprojector εprojector : ℝ) (hLprojector : 0 ≤ Lprojector) (hεprojector : 0<εprojector)
    (Cs bs b window pad : ℝ)
    (hCs : 1 ≤ Cs)(hbs : 1 ≤ bs)(hb : 1 ≤ b)(hwindow : 0 ≤ window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      MarkedSchedule830 P N Wslot (33/50) (33/50) →
      8*P.τ ≤ P.d*P.vslot → 16*P.τ ≤ P.d*P.vplain →
      2*P.τ*((J:ℝ)+1) ≤ 1/1000000000 →
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
        (β ampExponent reserveShift bAmpl rawError allowance Kcontrol width Wfiber : ℝ) (i : ℕ),
      (1+plane.q)/2  ≤  β → β  ≤  7/8 → 0  ≤  Kcontrol → 0<width →
      0 ≤ Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ) ≤ Wfiber) →
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
        unmarkedDensity (2*β-1)*εfreq+εvolume
      (∀l∈labels,x l 2+width ≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s ≤ Z^B → lo ≤  s.lower →
      17/500 ≤ bAmpl → bAmpl ≤ 1/25 → D=1 → 0 ≤ D → |D| ≤ B → |A| ≤ B → |ampExponent| ≤ B →
      |frequencyLoss Z 32 ξ+reserveShift| ≤ B → frequencyLoss Z 32 ξ+reserveShift ≤ frequencyAllowance → εfreq ≤ B → ξ ≤ εfreq →
      A ≤ D*plane.total bAmpl → ampExponent ≤ D*plane.amp bAmpl →
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
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      ∀(seed₂ : κ→Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap : ℝ),
      cap ≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (17/500)*D ≤ ∑j,w j →
      (∑j,w j) ≤ 1/25 →
      bAmpl-sourceWidthMesh ≤ ∑j,w j →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j ≤ Z^cap) →
      pad ≤ allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width ≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<β+2*P.e) →
      (∀j,0 ≤ w j) → (∀j,w j ≤  rawMesh830*rawCore830) →
      (∀j,w j/P.d ≤ P.Rwidth) →
      (∀j,P.σmin ≤ σ j) → (∀j,σ j ≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2 ≤ (3*i+2:ℕ)*Z^P.τ) →
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
        (fun _=>balancedFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L) ≤ 
      (1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*Z^εprojector*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*Z^Lprojector)^(2*ε)*
          Z^(target-D*(highReserve)+4*width+loss+rawError+allowance+B*εmass))))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_main_high_selected_shell (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ Wslot hWslotSupport hWslotSmooth hMarkedBeta hMarkedUpper B Q loss ε hB hQ hQB hQmax hloss hε hap
    plane N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  obtain ⟨Cp,hCp,hprojectors⟩:=shared_projector_shell_payment Lprojector εprojector hLprojector hεprojector
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hmarked hslot hplain hmarkedHeight
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hjoint⟩:=hhigh P hboundeq hmarked hslot hplain hmarkedHeight
  refine ⟨F,G,Cprofile,C,Cp*Kcolumn,hF,hCprofile,hC,by positivity,?_⟩
  filter_upwards [hjoint,hprojectors] with Z he hp
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift bAmpl rawError allowance Kcontrol width Wfiber i
    hβ hβ' hKcontrol hwidthbin hWfiber labels hfiber A x target hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hDunit hD hDcap hA hamp homega homegaSmall hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E seed₂ t w σ v θ p Ds cap hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow
    hseed₂ hwidth hradial hzeroUpper hw hwmarked hwr hσlo hσhi hheight hplainheight hW hDs hnormL hcontrol hledger
    t₀ u hslots hinput hKm hseedid hψ hshift
  let projectors : labels→Finset (Ideal O):=fun l=>Ds l.val
  let cost (l : labels) (L : Ideal O):=Z^(-ampExponent)*mainNormalizedPhysicalCost N lo ap second datum
    (fun _=>balancedFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l.val)/
      volume (datum (row l.val).val.1).input) t₀ u (row l.val).val L
  let Ebound:=(1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*(
    geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
      (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*Z^Lprojector)^(2*ε)*
        Z^(target-D*(highReserve)+4*width+loss+rawError+allowance+B*εmass)))))
  have hZpos : 0<Z:=zero_lt_one.trans hp.1
  have hfactor : 0 ≤ geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin:=
    (geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
  have hLower:0<lowerFactor N lo ap:=lowerFactor_pos N lo ap hlo hap
  have hEbound : 0 ≤ Ebound:=by
    dsimp only [Ebound]
    apply mul_nonneg (one_div_nonneg.mpr hLower.le)
    apply mul_nonneg hWfiber
    apply mul_nonneg (by positivity)
    apply mul_nonneg (mul_nonneg hfactor (Nat.cast_nonneg _))
    positivity
  have hc (l : labels) (L : Ideal O) : 0 ≤ cost l L := by
    have hm:=balanced_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l.val) hZpos.le
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
      hparent hfirst hR ψ β ampExponent reserveShift bAmpl rawError allowance Kcontrol
      (dyadicScale n) width Wfiber i hβ hβ' hKcontrol hscale.1 hwidthbin hWfiber labels hfiber
      hq hseed hs₁ hs₂ hsource hlower hbAmpl hbAmpl' hDunit hD hDcap hA hamp homega homegaSmall hεfreqB hξε htotalA hampcap hnorm hradius
      st hQM hQη z hz hchar hpuncture hrow hzero hsupport hibuffer hcurrent hi hcard hM hb₁ hb₂ hupper hwin
      B₁ t₁ hf₁ seed₂ t w σ v θ p (fun _=>shell (sharedProjectors projectors) n) cap
      hcap hmatches hsupply hsupplyUpper hcellSupply hscales hpadallow hseed₂ hwidth hradial hzeroUpper hw hwmarked hwr hσlo hσhi hheight hplainheight hW
      (fun _ _ L hL=>(shared_projector_shell_gates projectors n L hL).1)
      (fun _ _ L hL=>(shared_projector_shell_gates projectors n L hL).2.2)
      hcontrol hledger t₀ u hslots hinput hKm hseedid hψ hshift
    have hleft : (∑l : labels,∑L∈shell (sharedProjectors projectors) n,cost l L)=
        Z^(-ampExponent)*(∑l∈labels,∑L∈shell (sharedProjectors projectors) n,
          mainNormalizedPhysicalCost N lo ap second datum
            (fun _=>balancedFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
              volume (datum (row l).val.1).input) t₀ u (row l).val L) := by
      dsimp only [cost]
      simp only [←Finset.mul_sum]
      congr 1
      exact Finset.sum_coe_sort labels (fun l=>∑L∈shell (sharedProjectors projectors) n,
        mainNormalizedPhysicalCost N lo ap second datum
          (fun _=>balancedFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
            volume (datum (row l).val.1).input) t₀ u (row l).val L)
    rw [hleft]
    apply hh.trans
    dsimp only [Ebound]
    apply main_high_projector_scale_mono
      (1/lowerFactor N lo ap) Wfiber Kcolumn (Cs^(2*N)) (Z^(B*ε))
      (geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ))
      (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J)
      (Z^(target-D*(highReserve)+4*width+loss+rawError+allowance+B*εmass))
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
      (fun _=>balancedFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
        volume (datum (row l).val.1).input) t₀ u (row l).val L)=
      ∑l : labels,∑L∈projectors l,cost l L := by
    dsimp only [cost,projectors]
    simp only [←Finset.mul_sum]
    congr 1
    exact (Finset.sum_coe_sort labels (fun l=>∑L∈Ds l,
      mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>balancedFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)).symm
  rw [hleft]
  apply hpaid.trans_eq
  dsimp only [Ebound]
  ring

end
end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.main_high_physical_column_identity

#print axioms OAI.SevenEighths.TargetHigh830.actual_geometry_main_high_selected_shell

#print axioms OAI.SevenEighths.TargetHigh830.actual_geometry_main_high_datum_identification

#print axioms OAI.SevenEighths.TargetHigh830.actual_geometry_main_high_selected_projectors
