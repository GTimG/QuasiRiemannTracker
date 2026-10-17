/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B109
import Candidate.Bundles.B161
import Candidate.Bundles.B172
import Candidate.Bundles.B173
import Candidate.Bundles.B176

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighSelected; sha256 dc592e3b99870108b168b4a59647e5228a36561e32c8d63059488ab3236032c8 -/
section
                                                          
                                                                 
                                                        

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
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
    (ha : 0≤ a) (hb : 0≤ b) (hc : 0≤ c) (hd : 0≤ d)
    (he : 0≤ e) (hf : 0≤ f) (hg : 0≤ g) (hh : 0≤ h)
    (hs : 0≤ s) (hst : s≤ t) (hε : 0≤ε) :
    a*(b*(c*(2*s)^ε*d*e*(f*(g*(2*s)^(2*ε)*h))))≤
    a*(b*(c*(2*t)^ε*d*e*(f*(g*(2*t)^(2*ε)*h)))) := by
  have ht : 0≤ t:=hs.trans hst
  gcongr

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Literal source identification, including the signed row and shifted
height, converts the analytic column cost to the amplified physical cost. -/
theorem main_high_physical_column_identity
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (N : ℕ) (lo ap Z amp mass K : ℝ) (_hZ : 0< Z) (second : Bool)
    (d : Label→ SecondInputDatum α) (r : secondLiveRows (fun l=>(d l).block))
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
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0< lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧ 0< Kcolumn ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0< Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→ FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→ SecondInputDatum α)(first : DataLabel→ FirstSourceLabel)
        (row : κ→ secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→ RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber : ℝ) (i : ℕ),
      167/200 ≤ β → β ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T → 0< width →
      0≤ Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ)≤ Wfiber) →
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
        unmarkedDensity (2*β-1)*εfreq+εvolume
      (∀l∈labels,x l 2+width≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B → lo≤ s.lower →
      3401/100000≤ bAmpl → bAmpl≤1/25 → 0≤ D → |D|≤ B → |A|≤ B → |ampExponent|≤ B →
      |frequencyLoss Z 32 ξ+reserveShift|≤ B → εfreq≤ B → ξ≤εfreq →
      A≤ D*Cycle61.Arithmetic.totalA bAmpl → ampExponent≤ D*Cycle61.Arithmetic.amp bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤ Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤ Z^B) →
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
      (i:ℝ)≤ Z^P.τ →
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      s.b₁≤ bs → s.b₂≤ bs → s.upper≤ b →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
      let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
      let χ₁:=fun l=>geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l)
      ∀(B₁ : ∀l,actualAllocations s.pools (C₁ l))(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0) →
      let firstChild:=fun l=>child s (C₁ l) R (B₁ l) (χ₁ l) (t₁ l)
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      ∀(seed₂ : κ→ Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(Ds : κ→ Finset (Ideal O))(cap : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      pad≤ allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<β+2*P.e) →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      ∀(t₀ u : ℝ),
      (∀l∈labels,(datum (row l).val.1).slots=liveIndices (B₁ l).val) →
      (∀l∈labels,HEq (datum (row l).val.1).input (firstChild l)) →
      (∀l∈labels,(datum (row l).val.1).K=firstMainRadius reflected (Z^D) (volume s) Z ξ
        (3*ampExponent) reserveShift (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) →
      (∀l∈labels,seed₂ l=(datum (row l).val.1).seed) →
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      (∀l∈labels,t l=(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))) →
      Z^(-ampExponent)*(∑l∈labels,∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)≤
      (1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass))))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_full_high_columns (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hjoint⟩:=hhigh P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber i
    hβ hβ' hKcontrol hT hwidthbin hWfiber labels hfiber A x target hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow
    hseed₂ hwidth hradial hzeroUpper hw hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
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
    hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hi hcard hM hb₁ hb₂ hupper hwin
    B₁ t₁ hf₁ seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow hseed₂ hwidth hradial
    hzeroUpper hw hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
  have hZpos : 0< Z:= (by norm_num : (0:ℝ)<2).trans_le he.1
  have heq (l : κ) (hl : l∈labels) := main_high_physical_column_identity N lo ap Z ampExponent
    (geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l))
    (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*ampExponent) reserveShift
      (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) hZpos second datum (row l)
    (liveIndices (B₁ l).val) (firstChild l) (hslots l hl) (hinput l hl) (hKm l hl)
    (st l).character (by rw [hchar l,hψ l hl]) (z l) (hrow l) (seed₂ l) (hseedid l hl)
    t₀ u (t l) (hshift l hl) (Ds l)
  have hleft : Z^(-ampExponent)*(∑l∈labels,∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
      (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
        volume (datum (row l).val.1).input) t₀ u (row l).val L)=
      (1/lowerFactor N lo ap)*(∑l∈labels,geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
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
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z)
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
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0< lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Lprojector εprojector : ℝ) (hLprojector : 0≤ Lprojector) (hεprojector : 0<εprojector)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧ 0< Kcolumn ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0< Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→ FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→ SecondInputDatum α)(first : DataLabel→ FirstSourceLabel)
        (row : κ→ secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→ RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (β ampExponent reserveShift bAmpl rawError allowance Kcontrol width Wfiber : ℝ) (i : ℕ),
      167/200 ≤ β → β ≤ 7/8 → 0 ≤ Kcontrol → 0< width →
      0≤ Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ)≤ Wfiber) →
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
        unmarkedDensity (2*β-1)*εfreq+εvolume
      (∀l∈labels,x l 2+width≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B → lo≤ s.lower →
      3401/100000≤ bAmpl → bAmpl≤1/25 → 0≤ D → |D|≤ B → |A|≤ B → |ampExponent|≤ B →
      |frequencyLoss Z 32 ξ+reserveShift|≤ B → εfreq≤ B → ξ≤εfreq →
      A≤ D*Cycle61.Arithmetic.totalA bAmpl → ampExponent≤ D*Cycle61.Arithmetic.amp bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤ Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤ Z^B) →
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
      (i:ℝ)≤ Z^P.τ →
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      s.b₁≤ bs → s.b₂≤ bs → s.upper≤ b →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
      let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
      let χ₁:=fun l=>geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l)
      ∀(B₁ : ∀l,actualAllocations s.pools (C₁ l))(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0) →
      let firstChild:=fun l=>child s (C₁ l) R (B₁ l) (χ₁ l) (t₁ l)
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      ∀(seed₂ : κ→ Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(Ds : κ→ Finset (Ideal O))(cap : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      pad≤ allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<β+2*P.e) →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,(L.absNorm:ℝ)≤ Z^Lprojector) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      ∀(t₀ u : ℝ),
      (∀l∈labels,(datum (row l).val.1).slots=liveIndices (B₁ l).val) →
      (∀l∈labels,HEq (datum (row l).val.1).input (firstChild l)) →
      (∀l∈labels,(datum (row l).val.1).K=firstMainRadius reflected (Z^D) (volume s) Z ξ
        (3*ampExponent) reserveShift (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) →
      (∀l∈labels,seed₂ l=(datum (row l).val.1).seed) →
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      (∀l∈labels,t l=(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))) →
      Z^(-ampExponent)*(∑l∈labels,∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)≤
      (1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*Z^εprojector*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*Z^Lprojector)^(2*ε)*
          Z^(target-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass))))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_main_high_selected_shell (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  obtain ⟨Cp,hCp,hprojectors⟩:=shared_projector_shell_payment Lprojector εprojector hLprojector hεprojector
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hjoint⟩:=hhigh P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,Cp*Kcolumn,hF,hCprofile,hC,by positivity,?_⟩
  filter_upwards [hjoint,hprojectors] with Z he hp
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift bAmpl rawError allowance Kcontrol width Wfiber i
    hβ hβ' hKcontrol hwidthbin hWfiber labels hfiber A x target hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow
    hseed₂ hwidth hradial hzeroUpper hw hwr hσlo hσhi hheight hplainheight hW hDs hnormL hcontrol hledger
    t₀ u hslots hinput hKm hseedid hψ hshift
  let projectors : labels→ Finset (Ideal O):=fun l=>Ds l.val
  let cost (l : labels) (L : Ideal O):=Z^(-ampExponent)*mainNormalizedPhysicalCost N lo ap second datum
    (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l.val)/
      volume (datum (row l.val).val.1).input) t₀ u (row l.val).val L
  let Ebound:=(1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*(
    geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
      (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*Z^Lprojector)^(2*ε)*
        Z^(target-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass)))))
  have hZpos : 0< Z:=zero_lt_one.trans hp.1
  have hfactor : 0≤ geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin:=
    (geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
  have hLower:0< lowerFactor N lo ap:=lowerFactor_pos N lo ap hlo hap
  have hEbound : 0≤ Ebound:=by
    dsimp only [Ebound]
    apply mul_nonneg (one_div_nonneg.mpr hLower.le)
    apply mul_nonneg hWfiber
    apply mul_nonneg (by positivity)
    apply mul_nonneg (mul_nonneg hfactor (Nat.cast_nonneg _))
    positivity
  have hc (l : labels) (L : Ideal O) : 0≤ cost l L := by
    have hm:=geometry_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l.val)
    have hv:0< volume (datum (row l.val).val.1).input:=CenteredMomentAmplificationChildInput.volume_pos _
    have hl:0< lowerFactor N lo ap:=lowerFactor_pos N lo ap hlo hap
    have hk:0<(datum (row l.val).val.1).K:=(datum (row l.val).val.1).K_pos
    have hn:=normalizer_pos _ _ (datum (row l.val).val.1).hC (datum (row l.val).val.1).inactive
    dsimp only [cost,mainNormalizedPhysicalCost]
    apply mul_nonneg (Real.rpow_nonneg hZpos.le _)
    apply mul_nonneg (by positivity)
    split <;> exact sq_nonneg _
  have hnormp : ∀l : labels,∀L∈projectors l,(L.absNorm:ℝ)≤ Z^Lprojector:=
    fun l L hL=>hnormL l.val l.property L hL
  have hpay (n : ℤ) (hn : n∈selectedShells (sharedProjectors projectors)) :
      (∑l : labels,∑L∈shell (sharedProjectors projectors) n,cost l L)≤ Ebound := by
    have hscale:=shared_projector_shell_scale projectors Z Lprojector hnormp n hn
    have hh:=he.2 reflected second s hη R seed W D ξ hK bin column datum first row
      hparent hfirst hR ψ β ampExponent reserveShift bAmpl rawError allowance Kcontrol
      (dyadicScale n) width Wfiber i hβ hβ' hKcontrol hscale.1 hwidthbin hWfiber labels hfiber
      hq hseed hs₁ hs₂ hsource hlower hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm hradius
      st hQM hQη z hz hchar hpuncture hrow hzero hsupport hi hcard hM hb₁ hb₂ hupper hwin
      B₁ t₁ hf₁ seed₂ t w σ v θ p (fun _=>shell (sharedProjectors projectors) n) cap
      hcap hmatches hscales hpadallow hseed₂ hwidth hradial hzeroUpper hw hwr hσlo hσhi hheight hplainheight hW
      (fun _ _ L hL=>(shared_projector_shell_gates projectors n L hL).1)
      (fun _ _ L hL=>(shared_projector_shell_gates projectors n L hL).2.2)
      hcontrol hledger t₀ u hslots hinput hKm hseedid hψ hshift
    have hleft : (∑l : labels,∑L∈shell (sharedProjectors projectors) n,cost l L)=
        Z^(-ampExponent)*(∑l∈labels,∑L∈shell (sharedProjectors projectors) n,
          mainNormalizedPhysicalCost N lo ap second datum
            (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
              volume (datum (row l).val.1).input) t₀ u (row l).val L) := by
      dsimp only [cost]
      simp only [←Finset.mul_sum]
      congr 1
      exact Finset.sum_coe_sort labels (fun l=>∑L∈shell (sharedProjectors projectors) n,
        mainNormalizedPhysicalCost N lo ap second datum
          (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
            volume (datum (row l).val.1).input) t₀ u (row l).val L)
    rw [hleft]
    apply hh.trans
    dsimp only [Ebound]
    apply main_high_projector_scale_mono
      (1/lowerFactor N lo ap) Wfiber Kcolumn (Cs^(2*N)) (Z^(B*ε))
      (geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ))
      (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J)
      (Z^(target-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass))
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
      (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
        volume (datum (row l).val.1).input) t₀ u (row l).val L)=
      ∑l : labels,∑L∈projectors l,cost l L := by
    dsimp only [cost,projectors]
    simp only [←Finset.mul_sum]
    congr 1
    exact (Finset.sum_coe_sort labels (fun l=>∑L∈Ds l,
      mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)).symm
  rw [hleft]
  apply hpaid.trans_eq
  dsimp only [Ebound]
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_high_physical_column_identity

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_high_selected_shell

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_high_datum_identification

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_high_selected_projectors

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighSelected -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainOrdinaryFiber; sha256 5f03430a101a29b784376d184bc77ab5577e2f2cc779f86c440a26cda58729af -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                 

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61HighResidual ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle61FinalNatural
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open ConcreteTraceCRT CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentAllocatedRayDictionary CenteredMomentFiniteProfileExceptional CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondEnergySplit CenteredMomentFirstAmplificationChoice
local notation "O" => HeckeFamily.O
local instance mainOrdinaryFiberSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- An injective change of key cannot enlarge a fiber, including the literal
reflected nonzero joint label. -/
theorem main_injective_key_fiber {Row Key : Type*} [Fintype Row] [DecidableEq Key]
    (key : Row→ Key) (f : Key→ Key) (hf : Function.Injective f) (W : ℝ) (hW : 0≤ W)
    (hbound : ∀k,((Finset.univ.filter (fun r=>key r=k)).card:ℝ)≤ W) :
    ∀k,((Finset.univ.filter (fun r=>f (key r)=k)).card:ℝ)≤ W := by
  intro k
  by_cases hex : ∃r,f (key r)=k
  · obtain ⟨r₀,hr₀⟩:=hex
    have he (r : Row) : f (key r)=k ↔ key r=key r₀ := by
      rw [←hr₀]
      exact hf.eq_iff
    simp only [he]
    exact hbound (key r₀)
  · have he (r : Row) : f (key r)≠k := fun h=>hex ⟨r,h⟩
    simp only [he,Finset.filter_false,Finset.card_empty,Nat.cast_zero]
    exact hW

/-- Transfer the full original fiber certificate to any ordinary subset
through the exact row inclusion, without asking its restricted block to be
nonzero. The original finite image is the sole larger family. -/
theorem main_ordinary_key_fiber
    {α Label Key : Type*} [Fintype α] [DecidableEq α] [Fintype Label] [DecidableEq Key]
    (d : Label→ SecondInputDatum α) (χ : Label→ RayCharacter) (Q : Label→ Ideal O) (m : Label→ O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (key : secondLiveRows (fun l=>(d l).block)→ Key) (W : ℝ)
    (hfull : ∀rows : Finset (secondLiveRows (fun l=>(d l).block)),∀k,
      ((Finset.univ.filter (fun r : rows=>key r.val=k)).card:ℝ)≤ W)
    (rows : Finset (secondLiveRows
      (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block))) :
    ∀k,((Finset.univ.filter (fun r : rows=>
      key (ordinaryHighOriginalRow d χ Q m hrows r.val)=k)).card:ℝ)≤ W := by
  let embed:=ordinaryHighOriginalRow d χ Q m hrows
  let image:=rows.image embed
  let into : rows→ image:=fun r=>⟨embed r.val,Finset.mem_image.mpr ⟨r.val,r.property,rfl⟩⟩
  have hinj : Function.Injective into := by
    intro r s h
    apply Subtype.ext
    exact ordinary_high_original_row_injective d χ Q m hrows (congrArg Subtype.val h)
  exact high_restricted_key_fiber into hinj (fun r : image=>key r.val) W (hfull image)

/-- The restricted and original nonzero encodings agree even when their
nonzero proofs were obtained through different physical admission receipts. -/
theorem ordinary_main_nonzero_key_eq
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α)(χ : Label→ RayCharacter)(Q : Label→ Ideal O)(m : Label→ O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (first : Label→ FirstSourceLabel) (left : Bool) (u₀ : O) (unit : FirstSourceLabel→ O)
    (r : secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block))
    (hf : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(d l).block) first (ordinaryHighOriginalRow d χ Q m hrows r))≠0)
    (ho : jointFirstFrequency left u₀ unit
      (secondEncodedRow (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block) first r)≠0) :
    secondEncodedNonzeroRow (fun l=>(d l).block) first
      (ordinaryHighOriginalRow d χ Q m hrows r) left u₀ unit hf=
    secondEncodedNonzeroRow (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block)
      first r left u₀ unit ho := by
  apply Subtype.ext
  rfl

/-- The filter tests the ORIGINAL full physical block; the ordinary
restriction never substitutes its possibly zero block value. -/
def mainOrdinaryOriginalNonzeroRows {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α) (χ : Label→ RayCharacter) (Q : Label→ Ideal O) (m : Label→ O) :
    Finset (secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block)) :=
  Finset.univ.filter (fun r=>(d r.val.1).block.value ballProfile≠0)

theorem actual_geometry_main_ordinary_row_fiber_bound (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(b bs ε Amax Mmax ξ : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hε : 0<ε)
    (hA : 0≤ Amax)(hM : 0≤ Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃D : ℝ,0< D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(K a reserve t : ℝ)(hK : 0< K),
      Squarefree seed → Fintype.card α≤ N → Endpoints b bs bs s → volume s≤ Z^Amax → K≤ Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed K Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed K Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→ actualAllocations s.pools (C l),
      (∀l,frozenCoefficient (alloc l).val (C l) R s.ν s.W s.P≠0) →
      let slots := fun l=>liveIndices (alloc l).val
      let source := fun l=>child s (C l) R (alloc l) (χ l) t
      let first := fun l=>geometryFirstLabel s R seed K Z ξ hK bin (column l).val
      let projector := fun l=>(column l).val.2.1.val
      let Kmain := firstMainRadius reflected K (volume s) Z ξ (3*a) reserve
      let Tsec := firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0< Kmain (first l) := fun l=>first_main_radius_pos reflected K (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
      let block := fun q : Index=>(datum q).block
      let label := fun q : Index=>first q.1
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hunit : ∀l,unit l≠0 := fun _=>Units.ne_zero _
      let hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0 :=
        fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
          hu₀ (hunit _) (geometryFirstSource s R seed K Z ξ hK bin (column r.val.1.1).val.1).hC
      ∀(χ₀ : Index→ RayCharacter)(Q : Index→ Ideal O)(m : Index→ O),
      let ordinary:=fun q=>ordinarySecondDatum (datum q) (χ₀ q) (Q q) (m q)
      let fullRows : ∀q,(datum q).rows=sourceRows (datum q).C (datum q).D (datum q).inactive (datum q).radius := fun _=>rfl
      let embed:=ordinaryHighOriginalRow datum χ₀ Q m fullRows
      ∀(rows : Finset (secondLiveRows (fun q=>(ordinary q).block))),
      (∀r∈rows,(datum r.val.1).block.value ballProfile≠0) →
      ∀second : Bool,
      let key := fun r : rows=>secondEncodedNonzeroRow block label (embed r.val) left u₀ unit (hf (embed r.val))
      ∀target : NonzeroJointSourceLabel left u₀ unit,
      ((Finset.univ.filter (fun r : rows=>
        (if second then reflectedNonzeroJointLabel (key r) else key r)=target)).card:ℝ)≤ D*Z^(2*ε) := by
  obtain ⟨D,hD,hbase⟩:=actual_geometry_high_row_fiber_bound η₀ u₀ F₀ R₀ hu₀
    N b bs ε Amax Mmax ξ hb hbs hε hA hM hξ hξε
  refine ⟨D,hD,?_⟩
  filter_upwards [hbase] with Z hz
  intro hZ α Label _ _ _ reflected s R seed K a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index datum block label left unit hunit hf χ₀ Q m ordinary fullRows embed rows _hnonzero second key target
  have hfull:=hz hZ reflected s R seed K a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj alloc halloc
  have hraw:=main_ordinary_key_fiber datum χ₀ Q m fullRows
    (fun r=>secondEncodedNonzeroRow block label r left u₀ unit (hf r)) (D*Z^(2*ε)) hfull rows
  cases second
  · exact hraw target
  · apply main_injective_key_fiber key reflectedNonzeroJointLabel _ (D*Z^(2*ε)) (by positivity) hraw target
    intro j k h
    apply Subtype.ext
    exact reflected_joint_involutive.injective (congrArg Subtype.val h)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_injective_key_fiber
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_ordinary_key_fiber
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_ordinary_row_fiber_bound
#print axioms OAI.SevenEighths.Cycle61InitialMass.ordinary_main_nonzero_key_eq

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainOrdinaryFiber -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighFull; sha256 d4e8b9b8752bf610f205e382726a9d11a28a4947f642c79361c1777647126cf5 -/
section
                                                            
                                                                 
                                                             
                                                           
                                    

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
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


open Cycle61FinalNatural CenteredMomentSourceRow CenteredMomentSecondEnergySplit
open CenteredMomentSecondHeightFamily Cycle61Moment.LowBranch

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Widening the radial ceiling preserves the actual whole-family bin,
including its original keep witness and both buffered height intervals. -/
theorem main_high_widen_zero_bin {Z Bmask : ℝ} (st : NaturalState Z Bmask 2)
    (bΦ : ℝ) (hbΦ : 2≤ bΦ) (η₀ : Character)
    (hQM : st.fixedModulus≤ M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e)
    (hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p) :
    GeometryZeroBin M H hH (widenHighState st bΦ hbΦ) η₀ hQM hQη z hz e T p := by
  exact hbin

/-- Every complete ordinary row has one literal bin before residual ideals
are grouped. The enlarged support ceiling keeps the actual unit-weight
profile and the same signed physical frequency. -/
theorem actual_main_high_widened_selector
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α) (χ₀ : Label→ RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask bΦ : ℝ) (hZ : 1< Z) (hbΦ : 2≤ bΦ) (second : Bool)
    (hP : ∀l,(d l).R*(if second then (d l).D else (d l).C)≠0)
    (hPN : ∀l,(((d l).R*(if second then (d l).D else (d l).C)).absNorm:ℝ)≤ Z^Bmask)
    (η₀ : Character) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
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
    ∃select : rows→ BufferIndex e,∀r : rows,
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

omit [NeZero M] in
/-- Ordinary row membership supplies the actual keep and unit profile.
Only the scalar logarithmic width ceiling remains for the coarse gate
adapter; the dictionary and puncture are literal physical quantities. -/
theorem actual_main_high_ordinary_state
    {ι α Label : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected second : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (hu₀ : u₀≠0)(s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ amp reserve b Mcap Bmask bΦ : ℝ)(N : ℕ)
    (hK : 0< K)(hZ : 1< Z)(hb : 0< b)(hbΦ : 2≤ bΦ)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→ SecondInputDatum α)(first : Label→ FirstSourceLabel)
    (χ₀ : Label→ RayCharacter)(Q : Ideal O)(hQ : Q≤ Ideal.span {(72:O)})
    (m : O)(hm : m≠0)(hml : ConcretePrimeRowBridge.goodLambda∣m)(hm2 : (2:O)∣m)
    (r : secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ₀ l) Q m).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hradius : (d r.val.1).radius=frequencyRadius
      (firstMainFourierScale reflected K (volume s) Z ξ (3*amp) reserve b N
        (geometryFirstLabel s R seed K Z ξ hK bin j)) Z ξ)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R≠0)(hQM : Q≤ M)(hQη : Q≤η₀.modulus)
    (hPN : (((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)).absNorm:ℝ)≤ Z^Bmask)
    (hwidth :
      let src:=geometryFirstSource s R seed K Z ξ hK bin j.1
      let c:=Real.logb Z ((if reflected then src.D else src.C).absNorm:ℝ)
      let e:=Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)
      (Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)-max (c-e) 0-6*amp-
        frequencyLoss Z 32 ξ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator (d r.val.1).C (d r.val.1).D))+
        Real.logb Z ((∏p∈(d r.val.1).inactive,p.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)))≤ Mcap) :
    let ordinary:=fun l=>ordinarySecondDatum (d l) (χ₀ l) Q m
    let ψ:=if second then r.val.2.2.1⁻¹ else r.val.2.1
    let unit:=fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let hf:=geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin
      j ordinary first r hfirst
    let rawKey:=secondEncodedNonzeroRow (fun l=>(ordinary l).block) first r (!reflected) u₀ unit hf
    let key:=if second then reflectedNonzeroJointLabel rawKey else rawKey
    let z:=mainLowSignedRow second r.val.2.2.2.val
    let puncture:=(d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)
    let hP:puncture≠0:=mul_ne_zero hR (by
      split <;> first | exact (d r.val.1).hD.1 | exact (d r.val.1).hC.1)
    let base:=retainedState Z Bmask hZ ((d r.val.1).τ ψ) Q puncture hP hPN
      (d r.val.1).radius (d r.val.1).C (d r.val.1).D (d r.val.1).inactive
    let st:=widenHighState base bΦ hbΦ
    let holes:=(d r.val.1).input.η.modulus*puncture
    st.fixedModulus≤ M ∧ st.fixedModulus≤η₀.modulus ∧
      st.character=(ordinary r.val.1).τ ψ ∧ st.puncture=puncture ∧
      st.width≤ Mcap ∧ holes≠0 ∧ ∃keep:st.radial.keep z,
        1≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re ∧
        st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0 ∧ ∀I : Ideal O,
        idealCoeff (excluded (naturalRow st.character z (st.row_ne_zero z keep)).character st.puncture) I=
        idealCoeff (excluded (naturalRow (secondFixedDictionary η₀
          (geometryDictionaryRay reflected s R seed K Z ξ hK bin j,ψ))
          (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I := by
  intro ordinary ψ unit hf rawKey key z puncture hP base st holes
  have ha:=actual_main_ordinary_row_admission (d r.val.1) (χ₀ r.val.1) r.val.2.1 r.val.2.2.1
    Q hQ m hm hml hm2 Z Bmask hZ second hP hPN r.val.2.2.2.val r.val.2.2.2.property
  have hkeep:st.radial.keep z := by
    cases second <;> exact ha.1
  have hweightN:1≤(st.radial.profile (normValue z/st.radial.scale)).re := by
    cases second <;> exact ha.2
  have hweight:1≤(st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re := by
    simpa only [normValue_eq_embedding] using hweightN
  have hn:st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0:=by
    intro hz
    rw [hz] at hweight
    norm_num at hweight
  have hd:=actual_geometry_natural_dictionary reflected second η₀ u₀ F₀ R₀ hu₀ s hη
    R seed K Z ξ hK bin j ordinary first r hparent hfirst hR ψ
  have hw:=actual_geometry_second_width reflected s R seed K Z ξ amp reserve b N
    hK hZ hb bin j ordinary r hparent hradius Bmask ψ Q puncture hP hPN
  refine ⟨hQM,hQη,rfl,rfl,hw.trans hwidth,hd.1,hkeep,hweight,hn,?_⟩
  exact hd.2

/-- The fixed original dictionary absorbs the actual retained-width logs
before moving source data. Ordinary restriction changes only the row set. -/
theorem eventually_actual_main_high_ordinary_width (η : Character)(N : ℕ)(b : ℝ)(hb : 0< b) :
    ∀ᶠZ : ℝ in atTop,∀hZ : 1< Z,
      ∀{ι α Label : Type*}[Fintype ι][Fintype α][DecidableEq α][Fintype Label]
      (reflected second : Bool)(s : Input ι)(_hη : s.η=η)(R seed : Ideal O)
      (ξ amp reserve Bmask bΦ : ℝ)(hbΦ : 2≤ bΦ)(hK : 0< Z),
      0≤ amp → 0≤ reserve → 0≤ξ → ξ≤1 →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (j : FirstColumnIndex (geometryFirstSource s R seed Z Z ξ hK bin))
        (d : Label→ SecondInputDatum α)(χ₀ : Label→ RayCharacter)(Q : Ideal O)(m : O)
        (r : secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ₀ l) Q m).block)),
      (d r.val.1).input.η=geometryColumnCharacter reflected s R seed Z Z ξ hK bin j →
      (d r.val.1).radius=frequencyRadius
        (firstMainFourierScale reflected Z (volume s) Z ξ (3*amp) reserve b N
          (geometryFirstLabel s R seed Z Z ξ hK bin j)) Z ξ →
      ∀(hP : (d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)≠0)
        (hPN : (((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)).absNorm:ℝ)≤ Z^Bmask),
      let ψ:=if second then r.val.2.2.1⁻¹ else r.val.2.1
      let base:=retainedState Z Bmask hZ ((d r.val.1).τ ψ) Q
        ((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)) hP hPN
        (d r.val.1).radius (d r.val.1).C (d r.val.1).D (d r.val.1).inactive
      (widenHighState base bΦ hbΦ).width≤2 := by
  filter_upwards [eventual_high_width_one_gate η N b] with Z hw
  intro hZ ι α Label _ _ _ _ reflected second s hη R seed ξ amp reserve Bmask bΦ hbΦ hK
    hamp hreserve hξ hξ1 bin j d χ₀ Q m r hparent hradius hP hPN ψ base
  let ordinary:=fun l=>ordinarySecondDatum (d l) (χ₀ l) Q m
  have hwidth:=actual_geometry_second_width reflected s R seed Z Z ξ amp reserve b N
    hK hZ hb bin j ordinary r hparent hradius Bmask ψ Q
    ((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)) hP hPN
  apply hwidth.trans
  dsimp only
  rw [hη]
  exact hw.2 (d r.val.1).C (d r.val.1).D (d r.val.1).hC (d r.val.1).inactive
    _ _ amp reserve ξ hamp hreserve hξ hξ1

/-- A single original projector union remains outside the buffered bin.
Dropping membership costs only nonnegative literal physical terms. -/
theorem actual_main_high_global_shell_bin_le
    {α Label : Type*}[Fintype α][DecidableEq α][Fintype Label]
    (N : ℕ)(lo ap Z amp : ℝ)(hlo : 0< lo)(hap : 0< ap)(hZ : 0≤ Z)
    (second : Bool)(d : Label→ SecondInputDatum α)(coefficient : Label→ℝ)
    (hcoefficient : ∀l,0≤ coefficient l)(t u e : ℝ)
    (select : (secondLiveRows (fun l=>(d l).block))→ BufferIndex e)
    (Ds : (secondLiveRows (fun l=>(d l).block))→ Finset (Ideal O))(n : ℤ)(p : BufferIndex e) :
    let rows:=secondLiveRows (fun l=>(d l).block)
    let cost:=fun (r : rows) L=>mainNormalizedPhysicalCost N lo ap second d coefficient t u r.val L
    Z^(-amp)*mainBufferedShellBin rows e select Ds cost n p≤
      Z^(-amp)*(∑r∈rows.attach.filter (fun r=>select r=p),
        ∑L∈shell (sharedProjectors Ds) n,cost r L) := by
  intro rows cost
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ _)
  dsimp only [mainBufferedShellBin]
  rw [Finset.sum_filter]
  simp only [Finset.attach_eq_univ]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : select r=p
  · simp only [hr,ite_true]
    apply Finset.sum_le_sum
    intro L _
    by_cases hL : L∈Ds r
    · simp only [hL,ite_true,le_refl]
    · simp only [hL,ite_false]
      dsimp only [cost,mainNormalizedPhysicalCost]
      apply mul_nonneg
      · exact mul_nonneg (mul_nonneg (hcoefficient _)
          (div_nonneg (d r.val.1).K_pos.le (lowerFactor_pos N lo ap hlo hap).le))
          (normalizer_pos _ _ (d r.val.1).hC _).le
      · split <;> exact sq_nonneg _
  · simp only [hr,ite_false,le_refl]

/-- One original outer-height condition controls every literal signed
Mellin shift. The threshold precedes all source labels, bin indices and
moving profile frequencies. -/
theorem eventually_actual_main_high_shifted_family (outer inner : ℝ)(hgap : inner< outer) :
    ∀ᶠZ : ℝ in atTop,1≤ Z ∧
      ∀{α Label : Type*}[Fintype α][DecidableEq α][Fintype Label]
      (d : Label→ SecondInputDatum α)(second : Bool)(t height t₀ u : ℝ)(v : α→ℝ)(i : ℕ),
      (∀l,(d l).input.t=t) → 0≤ height →
      |t|+height+2*Real.pi*|t₀|≤ Z^outer/2 →
      1+‖u‖≤ Z^inner → (∀j,|v j|≤ height) →
      ∀l,(∀j,|(d l).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))+v j|+
        Z^outer/2≤(3*i+2:ℕ)*Z^outer) ∧
        |(d l).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))|+
          Z^outer/2≤(3*i+2:ℕ)*Z^outer := by
  filter_upwards [eventually_geometry_inner_shift_admission outer inner hgap] with Z hz
  refine ⟨hz.1,?_⟩
  intro α Label _ _ _ d second t height t₀ u v i ht hh hbase hu hv l
  have hbase' : |t|+height+2*Real.pi*|if second then -t₀ else t₀|≤ Z^outer/2 := by
    cases second <;> simpa only [Bool.false_eq_true,ite_false,ite_true,abs_neg] using hbase
  have ha (j : α):=hz.2 t height (if second then -t₀ else t₀) u i (v j) hh hbase' hu (hv j)
  have hp:=hz.2 t height (if second then -t₀ else t₀) u i 0 hh hbase' hu
    (by simpa only [abs_zero] using hh)
  rw [ht l]
  exact ⟨fun j=>(ha j).1,hp.2⟩

theorem main_high_common_target (β omega εfreq εvolume : ℝ)
    (hβ : 167/200≤β)(hβ' : β≤7/8)(hω : 0≤ omega)(hε : 0≤εfreq) :
    (1-unmarkedDensity (2*β-1))*omega+unmarkedDensity (2*β-1)*εfreq+εvolume≤
      omega+εfreq+εvolume := by
  have hρ:=unmarkedDensity_le_one (δ:=2*β-1) (by linarith) (by linarith)
  have hρ₀:0≤ unmarkedDensity (2*β-1):=le_trans (by norm_num)
    (unmarkedDensity_ge_two_sevenths (by linarith : 2*β-1≤3/4))
  have ho:=mul_le_mul_of_nonneg_right (by linarith : 1-unmarkedDensity (2*β-1)≤1) hω
  have he:=mul_le_mul_of_nonneg_right hρ hε
  linarith

private theorem main_high_height_target_payment (Z c height t tmax rest loss : ℝ)
    (hZ : 1≤ Z)(hc : 0≤ c)(_hh : 0≤ height)(hheight : height≤ Z^loss)(ht : t≤ tmax) :
    c*height*Z^(t+rest)≤ c*Z^(tmax+rest+loss) := by
  have hz:0< Z:=zero_lt_one.trans_le hZ
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

/-- The genuine selected high estimate has a common exponent on every high
zero bin. Its density-height polynomial is paid by a loss chosen after the
fixed density degree and before the moving sources. -/
theorem actual_geometry_main_high_uniform_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0< lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀heightloss : ℝ,∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain → 2*P.τ*(J+1)≤ heightloss →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧ 0< Kcolumn ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0< Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→ FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→ SecondInputDatum α)(first : DataLabel→ FirstSourceLabel)
        (row : κ→ secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→ RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber : ℝ) (i : ℕ),
      167/200 ≤ β → β ≤ 7/8 → 0≤ξ → 0≤ reserveShift → 0 ≤ Kcontrol → 1 ≤ T → 0< width →
      0≤ Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ)≤ Wfiber) →
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      (∀l∈labels,x l 2+width≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B → lo≤ s.lower →
      3401/100000≤ bAmpl → bAmpl≤1/25 → 0≤ D → |D|≤ B → |A|≤ B → |ampExponent|≤ B →
      |frequencyLoss Z 32 ξ+reserveShift|≤ B → εfreq≤ B → ξ≤εfreq →
      A≤ D*Cycle61.Arithmetic.totalA bAmpl → ampExponent≤ D*Cycle61.Arithmetic.amp bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤ Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤ Z^B) →
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
      (i:ℝ)≤ Z^P.τ →
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      s.b₁≤ bs → s.b₂≤ bs → s.upper≤ b →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
      let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
      let χ₁:=fun l=>geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l)
      ∀(B₁ : ∀l,actualAllocations s.pools (C₁ l))(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0) →
      let firstChild:=fun l=>child s (C₁ l) R (B₁ l) (χ₁ l) (t₁ l)
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      ∀(seed₂ : κ→ Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(Ds : κ→ Finset (Ideal O))(cap : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      pad≤ allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<β+2*P.e) →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      ∀(t₀ u : ℝ),
      (∀l∈labels,(datum (row l).val.1).slots=liveIndices (B₁ l).val) →
      (∀l∈labels,HEq (datum (row l).val.1).input (firstChild l)) →
      (∀l∈labels,(datum (row l).val.1).K=firstMainRadius reflected (Z^D) (volume s) Z ξ
        (3*ampExponent) reserveShift (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) →
      (∀l∈labels,seed₂ l=(datum (row l).val.1).seed) →
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      (∀l∈labels,t l=(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))) →
      Z^(-ampExponent)*(∑l∈labels,∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)≤
      (1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
          Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass+heightloss))))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_main_high_selected_shell (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro heightloss P hboundeq hslot hplain hdensity
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hjoint⟩:=hhigh P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,?_⟩
  filter_upwards [hjoint,eventually_high_truncated_heights P J heightloss hslot hplain hdensity] with Z he hhgt
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber i
    hβ hβ' hξ hreserve hKcontrol hT hwidthbin hWfiber labels hfiber A x hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow
    hseed₂ hwidth hradial hzeroUpper hw hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
    t₀ u hslots hinput hKm hseedid hψ hshift
  let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
    unmarkedDensity (2*β-1)*εfreq+εvolume
  have hh:=he.2 reflected second s hη R seed W D ξ hK bin column datum first row
    hparent hfirst hR ψ β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber i
    hβ hβ' hKcontrol hT hwidthbin hWfiber labels hfiber hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hi hcard hM hb₁ hb₂ hupper hwin
    B₁ t₁ hf₁ seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow hseed₂ hwidth hradial
    hzeroUpper hw hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
    t₀ u hslots hinput hKm hseedid hψ hshift
  have hZ : 1≤ Z:=by linarith [he.1]
  have htarget:=main_high_common_target β (frequencyLoss Z 32 ξ+reserveShift) εfreq εvolume
    hβ hβ' (add_nonneg (frequencyLoss_nonneg Z 32 ξ hhgt.1 (by norm_num) hξ) hreserve) hεfreq.le
  let c:=C*Cprofile^2*Kcontrol*(2*T)^(2*ε)
  let rest:=-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass
  let tmax:=frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume
  have hpayment:=main_high_height_target_payment Z c ((1+3*(i+1:ℕ)*Z^P.τ)^J)
    target tmax rest heightloss hZ (by dsimp only [c]; positivity) (by positivity) (hhgt.2 i hi).2.2 htarget
  let pref:=(1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
    geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ))))
  have hfactor:= (geometry_high_factor_pos reflected (geometrySupportConstant N lo ap ap) bin
    (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
  have hlowerpos:0< lowerFactor N lo ap:=lowerFactor_pos N lo ap hlo hap
  have hZ0:0≤ Z:=(by norm_num : (0:ℝ)≤2).trans he.1
  have hT0:0≤2*T:=mul_nonneg (by norm_num) (zero_le_one.trans hT)
  have hfront:0≤ Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε):=
    mul_nonneg (mul_nonneg (mul_nonneg hKcolumn.le (Real.rpow_nonneg hT0 _))
      (pow_nonneg (zero_le_one.trans hCs) _)) (Real.rpow_nonneg hZ0 _)
  have hpref:0≤ pref:=mul_nonneg (one_div_nonneg.mpr hlowerpos.le)
    (mul_nonneg hWfiber (mul_nonneg hfront (mul_nonneg hfactor (Nat.cast_nonneg _))))
  refine hh.trans ?_
  have he₁:target-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass=
      target+rest:=by dsimp only [rest]; ring
  have he₂:frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(781136071/45083880000000)+
      4*width+loss+rawError+allowance+B*εmass+heightloss=tmax+rest+heightloss:=by
    dsimp only [tmax,rest]; ring
  rw [he₁,he₂]
  convert mul_le_mul_of_nonneg_left hpayment hpref using 1 <;>
    dsimp only [pref,c] <;> ring


/-- A single literal buffered selector partitions the finite high family.
The genuine analytic bound is summed with only the fixed buffer count;
physical first scalar mass and each residual projector stay inside the cost. -/
theorem actual_geometry_main_high_buffered_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0< lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀heightloss : ℝ,∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain → 2*P.τ*(J+1)≤ heightloss →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧ 0< Kcolumn ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0< Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→ FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→ SecondInputDatum α)(first : DataLabel→ FirstSourceLabel)
        (row : κ→ secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→ RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber : ℝ),
      0≤ξ → 0≤ reserveShift → 0 ≤ Kcontrol → 1 ≤ T → 0< width →
      0≤ Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ)≤ Wfiber) →
      ∀select : κ→ BufferIndex P.e,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      (∀l∈labels,x l 2+width≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B → lo≤ s.lower →
      3401/100000≤ bAmpl → bAmpl≤1/25 → 0≤ D → |D|≤ B → |A|≤ B → |ampExponent|≤ B →
      |frequencyLoss Z 32 ξ+reserveShift|≤ B → εfreq≤ B → ξ≤εfreq →
      A≤ D*Cycle61.Arithmetic.totalA bAmpl → ampExponent≤ D*Cycle61.Arithmetic.amp bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤ Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤ Z^B) →
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
      (∀l∈labels,167/200≤ bufferValue P.e (select l)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (∀l∈labels,((select l).1.val:ℝ)≤ Z^P.τ) →
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      s.b₁≤ bs → s.b₂≤ bs → s.upper≤ b →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
      let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
      let χ₁:=fun l=>geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l)
      ∀(B₁ : ∀l,actualAllocations s.pools (C₁ l))(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0) →
      let firstChild:=fun l=>child s (C₁ l) R (B₁ l) (χ₁ l) (t₁ l)
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      ∀(seed₂ : κ→ Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(Ds : κ→ Finset (Ideal O))(cap : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      pad≤ allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      ∀(t₀ u : ℝ),
      (∀l∈labels,(datum (row l).val.1).slots=liveIndices (B₁ l).val) →
      (∀l∈labels,HEq (datum (row l).val.1).input (firstChild l)) →
      (∀l∈labels,(datum (row l).val.1).K=firstMainRadius reflected (Z^D) (volume s) Z ξ
        (3*ampExponent) reserveShift (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) →
      (∀l∈labels,seed₂ l=(datum (row l).val.1).seed) →
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      (∀l∈labels,t l=(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))) →
      Z^(-ampExponent)*(∑l∈labels,∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)≤
      (Fintype.card (BufferIndex P.e):ℝ)*((1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
          Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass+heightloss)))))) := by
  obtain ⟨bound,hbound,J,huniform⟩:=actual_geometry_main_high_uniform_shell (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro heightloss P hboundeq hslot hplain hdensity
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hjoint⟩:=
    huniform heightloss P hboundeq hslot hplain hdensity
  refine ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key ampExponent reserveShift bAmpl rawError allowance Kcontrol T width Wfiber
    hξ hreserve hKcontrol hT hwidthbin hWfiber labels hfiber select A x hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow
    hseed₂ hwidth hradial hw hwr hσlo hσhi hheight hplainheight hW hDs hdyad hcontrol hledger
    t₀ u hslots hinput hKm hseedid hψ hshift
  let cost:=fun l=>∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
    (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
      volume (datum (row l).val.1).input) t₀ u (row l).val L
  let rhs:=(1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε)*(
    geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
      (C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
        Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(781136071/45083880000000)+
          4*width+loss+rawError+allowance+B*εmass+heightloss)))))
  have hlowerpos:=lowerFactor_pos N lo ap hlo hap
  have hfactor:=(geometry_high_factor_pos reflected (geometrySupportConstant N lo ap ap) bin
    (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
  have hZ0:0≤ Z:=(by norm_num : (0:ℝ)≤2).trans he.1
  have hT0:0≤2*T:=mul_nonneg (by norm_num) (zero_le_one.trans hT)
  have hfront:0≤ Kcolumn*(2*T)^ε*Cs^(2*N)*Z^(B*ε):=
    mul_nonneg (mul_nonneg (mul_nonneg hKcolumn.le (Real.rpow_nonneg hT0 _))
      (pow_nonneg (zero_le_one.trans hCs) _)) (Real.rpow_nonneg hZ0 _)
  have hback:0≤ C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
      Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(781136071/45083880000000)+
        4*width+loss+rawError+allowance+B*εmass+heightloss):=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) hKcontrol)
      (Real.rpow_nonneg hT0 _)) (Real.rpow_nonneg hZ0 _)
  have hrhs:0≤ rhs:=mul_nonneg (one_div_nonneg.mpr hlowerpos.le)
    (mul_nonneg hWfiber (mul_nonneg hfront
      (mul_nonneg (mul_nonneg hfactor (Nat.cast_nonneg _)) hback)))
  have hone (q : BufferIndex P.e) : Z^(-ampExponent)*(∑l∈labels.filter (select ·=q),cost l)≤ rhs := by
    let small:=labels.filter (select ·=q)
    have hsub : small⊆labels:=Finset.filter_subset _ _
    have heq {l : κ}(hl : l∈small):select l=q:=(Finset.mem_filter.mp hl).2
    by_cases hempty:small=∅
    · change Z^(-ampExponent)*(∑l∈small,cost l)≤ rhs
      simpa only [hempty,Finset.sum_empty,mul_zero] using hrhs
    · obtain ⟨l₀,hl₀⟩:=Finset.nonempty_iff_ne_empty.mpr hempty
      have hinterval (l : κ)(hl : l∈small):=
        actual_main_high_bin_intervals M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
          P.e (Z^P.τ) (select l) (hbin l (hsub hl)) (hhigh l (hsub hl))
      have hβ:=hinterval l₀ hl₀
      rw [heq hl₀] at hβ
      let into : small→ labels:=fun r=>⟨r.val,hsub r.property⟩
      have hinj:Function.Injective into:=by intro r t h; exact Subtype.ext (congrArg (fun q : labels=>q.val) h)
      have hsmallfiber:=high_restricted_key_fiber into hinj (fun r : labels=>key r.val) Wfiber hfiber
      have hj:=he.2 reflected second s hη R seed W D ξ hK bin column datum first row
        hparent hfirst hR ψ (bufferValue P.e q) ampExponent reserveShift bAmpl rawError allowance
        Kcontrol T width Wfiber q.1.val hβ.1 hβ.2.1 hξ hreserve hKcontrol hT hwidthbin hWfiber
        small hsmallfiber
        (fun l hl=>hq l (hsub hl)) hseed hs₁ hs₂ hsource hlower
        hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap
        (fun l hl=>hnorm l (hsub hl)) (fun l hl=>hradius l (hsub hl))
        st hQM hQη z hz hchar hpuncture hrow
        (fun l hl=>by simpa only [heq hl,geometryRowMaximum,geometryRowFamily] using (hinterval l hl).2.2.2.2.1)
        (fun l hl=>hsupport l (hsub hl)) (by simpa only [heq hl₀] using hi l₀ (hsub hl₀))
        hcard hM hb₁ hb₂ hupper hwin B₁ t₁ (fun l hl=>hf₁ l (hsub hl))
        seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow
        (fun l hl=>hseed₂ l (hsub hl)) (fun l hl=>hwidth l (hsub hl)) (fun l hl=>hradial l (hsub hl))
        (fun l hl=>by simpa only [heq hl,geometryRowMaximum,geometryRowFamily] using (hinterval l hl).2.2.2.2.2)
        hw hwr hσlo hσhi (fun l hl j=>by simpa only [heq hl] using hheight l (hsub hl) j)
        (fun l hl=>by simpa only [heq hl] using hplainheight l (hsub hl))
        (fun l hl=>hW l (hsub hl)) (fun l hl=>hDs l (hsub hl)) (fun l hl=>hdyad l (hsub hl))
        (fun l hl=>hcontrol l (hsub hl)) hledger t₀ u
        (fun l hl=>hslots l (hsub hl)) (fun l hl=>hinput l (hsub hl))
        (fun l hl=>hKm l (hsub hl)) (fun l hl=>hseedid l (hsub hl))
        (fun l hl=>hψ l (hsub hl)) (fun l hl=>hshift l (hsub hl))
      exact hj
  have hsplit:Z^(-ampExponent)*(∑l∈labels,cost l)=
      ∑q : BufferIndex P.e,Z^(-ampExponent)*(∑l∈labels.filter (select ·=q),cost l) := by
    simp only [Finset.mul_sum,Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    simp
  change Z^(-ampExponent)*(∑l∈labels,cost l)≤(Fintype.card (BufferIndex P.e):ℝ)*rhs
  rw [hsplit]
  calc
    _≤∑_q : BufferIndex P.e,rhs:=Finset.sum_le_sum (fun q _=>hone q)
    _=(Fintype.card (BufferIndex P.e):ℝ)*rhs:=by simp


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_high_widen_zero_bin
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_high_widened_selector

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_high_ordinary_state

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventually_actual_main_high_ordinary_width
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_high_global_shell_bin_le

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventually_actual_main_high_shifted_family

#print axioms OAI.SevenEighths.Cycle61InitialMass.main_high_common_target

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_high_uniform_shell

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_high_buffered_shell

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighFull -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighProjectorPayment; sha256 d30541b1e7e26fcfb9573d8aff3a0bf4488774f3c9d5a9bff29f15c6b0e0a808 -/
section
                                                        
                                                                 
                                                        

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open MeasureTheory
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
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
    (ha : 0≤ a) (hb : 0≤ b) (hc : 0≤ c) (hd : 0≤ d)
    (he : 0≤ e) (hf : 0≤ f) (hg : 0≤ g) (hh : 0≤ h)
    (hs : 0≤ s) (hst : s≤ t) (hε : 0≤ε) :
    a*(b*(c*(2*s)^ε*d*e*(f*(g*(2*s)^(2*ε)*h))))≤
    a*(b*(c*(2*t)^ε*d*e*(f*(g*(2*t)^(2*ε)*h)))) := by
  have ht : 0≤ t:=hs.trans hst
  gcongr

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- All high buffered bins share one projector union. Its shell count is
paid once, preserving the physical side factor and original row weights. -/
theorem actual_geometry_main_high_buffered_projectors {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0< lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Lprojector εprojector : ℝ) (hLprojector : 0≤ Lprojector) (hεprojector : 0<εprojector)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀heightloss : ℝ,∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain → 2*P.τ*(J+1)≤ heightloss →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C Kcolumn : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧ 0< Kcolumn ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0< Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→ FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→ SecondInputDatum α)(first : DataLabel→ FirstSourceLabel)
        (row : κ→ secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→ RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (ampExponent reserveShift bAmpl rawError allowance Kcontrol width Wfiber : ℝ),
      0≤ξ → 0≤ reserveShift → 0 ≤ Kcontrol → 0< width →
      0≤ Wfiber →
      ∀labels : Finset κ,
      (∀k,((Finset.univ.filter (fun r : labels=>key r.val=k)).card:ℝ)≤ Wfiber) →
      ∀select : κ→ BufferIndex P.e,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      (∀l∈labels,x l 2+width≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B → lo≤ s.lower →
      3401/100000≤ bAmpl → bAmpl≤1/25 → 0≤ D → |D|≤ B → |A|≤ B → |ampExponent|≤ B →
      |frequencyLoss Z 32 ξ+reserveShift|≤ B → εfreq≤ B → ξ≤εfreq →
      A≤ D*Cycle61.Arithmetic.totalA bAmpl → ampExponent≤ D*Cycle61.Arithmetic.amp bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤ Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤ Z^B) →
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
      (∀l∈labels,167/200≤ bufferValue P.e (select l)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (∀l∈labels,((select l).1.val:ℝ)≤ Z^P.τ) →
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      s.b₁≤ bs → s.b₂≤ bs → s.upper≤ b →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
      let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
      let χ₁:=fun l=>geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l)
      ∀(B₁ : ∀l,actualAllocations s.pools (C₁ l))(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0) →
      let firstChild:=fun l=>child s (C₁ l) R (B₁ l) (χ₁ l) (t₁ l)
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      ∀(seed₂ : κ→ Ideal O)(t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(Ds : κ→ Finset (Ideal O))(cap : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      pad≤ allowance →
      (∀l∈labels,seed₂ l∣E l) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*(select l).1.val+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,(L.absNorm:ℝ)≤ Z^Lprojector) →
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      ∀(t₀ u : ℝ),
      (∀l∈labels,(datum (row l).val.1).slots=liveIndices (B₁ l).val) →
      (∀l∈labels,HEq (datum (row l).val.1).input (firstChild l)) →
      (∀l∈labels,(datum (row l).val.1).K=firstMainRadius reflected (Z^D) (volume s) Z ξ
        (3*ampExponent) reserveShift (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) →
      (∀l∈labels,seed₂ l=(datum (row l).val.1).seed) →
      (∀l∈labels,ψ l=if second then (row l).val.2.2.1⁻¹ else (row l).val.2.1) →
      (∀l∈labels,t l=(datum (row l).val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀))) →
      Z^(-ampExponent)*(∑l∈labels,∑L∈Ds l,mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)≤
      (Fintype.card (BufferIndex P.e):ℝ)*((1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*Z^εprojector*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*(
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(2*Z^Lprojector)^(2*ε)*
          Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass+heightloss)))))) := by
  obtain ⟨bound,hbound,J,hhigh⟩:=actual_geometry_main_high_buffered_shell (α:=α) M H hH
    η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N lo εmass εfreq εvolume hlo hεmass hεfreq hεvolume
    Cs bs b window pad hCs hbs hb hwindow hpad
  obtain ⟨Cp,hCp,hprojectors⟩:=shared_projector_shell_payment Lprojector εprojector hLprojector hεprojector
  refine ⟨bound,hbound,J,?_⟩
  intro heightloss P hboundeq hslot hplain hdensity
  obtain ⟨F,G,Cprofile,C,Kcolumn,hF,hCprofile,hC,hKcolumn,hjoint⟩:=hhigh heightloss P hboundeq hslot hplain hdensity
  refine ⟨F,G,Cprofile,C,Cp*Kcolumn,hF,hCprofile,hC,by positivity,?_⟩
  filter_upwards [hjoint,hprojectors] with Z he hp
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key ampExponent reserveShift bAmpl rawError allowance Kcontrol width Wfiber
    hξ hreserve hKcontrol hwidthbin hWfiber labels hfiber select A x hq hseed hs₁ hs₂ hsource hlower
    hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm hradius
    st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild E seed₂ t w σ v θ p Ds cap hcap hmatches hscales hpadallow
    hseed₂ hwidth hradial hw hwr hσlo hσhi hheight hplainheight hW hDs hnormL hcontrol hledger
    t₀ u hslots hinput hKm hseedid hψ hshift
  let projectors : labels→ Finset (Ideal O):=fun l=>Ds l.val
  let cost (l : labels) (L : Ideal O):=Z^(-ampExponent)*mainNormalizedPhysicalCost N lo ap second datum
    (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l.val)/
      volume (datum (row l.val).val.1).input) t₀ u (row l.val).val L
  let Ebound:=(Fintype.card (BufferIndex P.e):ℝ)*((1/lowerFactor N lo ap)*(Wfiber*(Kcolumn*(2*Z^Lprojector)^ε*Cs^(2*N)*Z^(B*ε)*(
    geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
    ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
      (C*Cprofile^2*Kcontrol*(2*Z^Lprojector)^(2*ε)*
        Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass+heightloss))))))
  have hZpos : 0< Z:=zero_lt_one.trans hp.1
  have hfactor : 0≤ geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin:=
    (geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
  have hLower:0< lowerFactor N lo ap:=lowerFactor_pos N lo ap hlo hap
  have hEbound : 0≤ Ebound:=by
    dsimp only [Ebound]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply mul_nonneg (one_div_nonneg.mpr hLower.le)
    apply mul_nonneg hWfiber
    apply mul_nonneg (by positivity)
    apply mul_nonneg (mul_nonneg hfactor (Nat.cast_nonneg _))
    positivity
  have hc (l : labels) (L : Ideal O) : 0≤ cost l L := by
    have hm:=geometry_first_high_mass_nonneg reflected s R seed W D Z ξ εmass hK bin (column l.val)
    have hv:0< volume (datum (row l.val).val.1).input:=CenteredMomentAmplificationChildInput.volume_pos _
    have hl:0< lowerFactor N lo ap:=lowerFactor_pos N lo ap hlo hap
    have hk:0<(datum (row l.val).val.1).K:=(datum (row l.val).val.1).K_pos
    have hn:=normalizer_pos _ _ (datum (row l.val).val.1).hC (datum (row l.val).val.1).inactive
    dsimp only [cost,mainNormalizedPhysicalCost]
    apply mul_nonneg (Real.rpow_nonneg hZpos.le _)
    apply mul_nonneg (by positivity)
    split <;> exact sq_nonneg _
  have hnormp : ∀l : labels,∀L∈projectors l,(L.absNorm:ℝ)≤ Z^Lprojector:=
    fun l L hL=>hnormL l.val l.property L hL
  have hpay (n : ℤ) (hn : n∈selectedShells (sharedProjectors projectors)) :
      (∑l : labels,∑L∈shell (sharedProjectors projectors) n,cost l L)≤ Ebound := by
    have hscale:=shared_projector_shell_scale projectors Z Lprojector hnormp n hn
    have hh:=he.2 reflected second s hη R seed W D ξ hK bin column datum first row
      hparent hfirst hR ψ ampExponent reserveShift bAmpl rawError allowance Kcontrol
      (dyadicScale n) width Wfiber hξ hreserve hKcontrol hscale.1 hwidthbin hWfiber labels hfiber select
      hq hseed hs₁ hs₂ hsource hlower hbAmpl hbAmpl' hD hDcap hA hamp homega hεfreqB hξε htotalA hampcap hnorm hradius
      st hQM hQη z hz hchar hpuncture hrow hbin hhigh hsupport hi hcard hM hb₁ hb₂ hupper hwin
      B₁ t₁ hf₁ seed₂ t w σ v θ p (fun _=>shell (sharedProjectors projectors) n) cap
      hcap hmatches hscales hpadallow hseed₂ hwidth hradial hw hwr hσlo hσhi hheight hplainheight hW
      (fun _ _ L hL=>(shared_projector_shell_gates projectors n L hL).1)
      (fun _ _ L hL=>(shared_projector_shell_gates projectors n L hL).2.2)
      hcontrol hledger t₀ u hslots hinput hKm hseedid hψ hshift
    have hleft : (∑l : labels,∑L∈shell (sharedProjectors projectors) n,cost l L)=
        Z^(-ampExponent)*(∑l∈labels,∑L∈shell (sharedProjectors projectors) n,
          mainNormalizedPhysicalCost N lo ap second datum
            (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
              volume (datum (row l).val.1).input) t₀ u (row l).val L) := by
      dsimp only [cost]
      simp only [←Finset.mul_sum]
      congr 1
      exact Finset.sum_coe_sort labels (fun l=>∑L∈shell (sharedProjectors projectors) n,
        mainNormalizedPhysicalCost N lo ap second datum
          (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
            volume (datum (row l).val.1).input) t₀ u (row l).val L)
    rw [hleft]
    apply hh.trans
    dsimp only [Ebound]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply buffered_projector_scale_mono
      (1/lowerFactor N lo ap) Wfiber Kcolumn (Cs^(2*N)) (Z^(B*ε))
      (geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
        ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ))
      (C*Cprofile^2*Kcontrol)
      (Z^(frequencyLoss Z 32 ξ+reserveShift+εfreq+εvolume-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass+heightloss))
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
      (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
        volume (datum (row l).val.1).input) t₀ u (row l).val L)=
      ∑l : labels,∑L∈projectors l,cost l L := by
    dsimp only [cost,projectors]
    simp only [←Finset.mul_sum]
    congr 1
    exact (Finset.sum_coe_sort labels (fun l=>∑L∈Ds l,
      mainNormalizedPhysicalCost N lo ap second datum
        (fun _=>geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)/
          volume (datum (row l).val.1).input) t₀ u (row l).val L)).symm
  rw [hleft]
  apply hpaid.trans_eq
  dsimp only [Ebound]
  ring


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_high_buffered_projectors

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainHighProjectorPayment -/
