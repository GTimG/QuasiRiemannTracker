/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B009
import Submissions.reserve_local_20261013.Bundles.B033
import Submissions.reserve_local_20261013.Bundles.B037
import Submissions.reserve_local_20261013.Bundles.B092
import Submissions.reserve_local_20261013.Bundles.B093
import Submissions.reserve_local_20261013.Bundles.B097
import Submissions.reserve_local_20261013.Bundles.B099
import Submissions.reserve_local_20261013.Bundles.B101
import Submissions.reserve_local_20261013.Bundles.B102
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.CommonProbe
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceFamily

/- BEGIN ORIGINAL MODULE Analytic.JointFirstIndependentErrors ; sha256 28c52c1b2f151fbf275418f0b4ed2acefeb3cf63c4093a8199599a8eca9bfe21 -/
section




/-! Actual extracted error estimates with Ready discharged by source caps.
Dead extracted sources vanish exactly. Every live extracted source receives
its Ready packet from the pinned source theorem before the genuine analytic
estimate is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
local instance actualFirstIndependentErrorsDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance actualFirstIndependentErrorsFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates


open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstLiveAdmission

open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstMixedAllowance
open CenteredMomentFirstPhysicalSource CenteredMomentPrimeElements CenteredMomentPrimePool

open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalFixedWeightSum
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstSectors
open CenteredMomentFirstMixedRightTransport CenteredMomentSupportedCorrelation
open CenteredMomentRankinRadical

theorem actual_first_independent_extracted_errors
    (Wslot:ℝ→ℂ)(aslot bslot Mcap εremove lo hi εchild:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(haUpper:a≤1/4)(hbPlain:1≤ b)
    (L:ℝ)(hL:0≤ L)
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)(hMcap:0< Mcap)
    (hεchild:0<εchild)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (sigma cost:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost) (hsigma_eq : sigma=9/500)
    (Avol Dscale Pmask qmoving εgeo : ℝ) (hεgeo : 0 < εgeo)
    (hbudget : CenteredMomentFirstSecondInputGates.exponent Avol Dscale Pmask qmoving εgeo ξ ≤ Bcap)
    (εalloc : ℝ) (hεalloc : 0 < εalloc)
    (hloss : ∀ j, CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j ≤ 1/10000)
    (hsaving : 0 ≤ saving)
    (Bfirst Lfirst Crfirst : ℝ) (hBfirst : 0 ≤ Bfirst) (hLfirst : 0 ≤ Lfirst)
    (hCrfirst : 0 < Crfirst) (hallocSmall : εalloc*Bfirst ≤ 1/10000)
    (qParent εconductor : ℝ) (hεconductor : 0 < εconductor)
    (hcostSource : CenteredMomentFirstSourceConductorCaps.rayCost ≤ cost)
    (hconductorBudget : qParent+2*Bfirst+sigma/3+εconductor ≤ qmoving)
    (εouter : ℝ) (hεouter : 0 < εouter) (hseedBudget : Bfirst ≤ Bseed):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0< Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤(Cycle25.Energy.commonMesh Mcap 0 L εchild)) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    (src.η.modulus.absNorm : ℝ) ≤ Z^qParent →
    ∀ (R seedOuter : Ideal O), R ≠ 0 →
    Squarefree seedOuter → seedOuter ≠ 0 →
    src.W₁ 0=0 → src.W₂ 0=0 → volume src≤ Z^Avol → (R.absNorm : ℝ)≤ Z^Pmask →
    0 < sourceRadius src → sourceRadius src ≤ Z^Bfirst →
    ∀ profile : Profiles a b, profile.profile 0=src.W₁ → profile.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀ (K delta reserve asource : ℝ),
    0 < K → 0 < asource →
    0 ≤ delta → 0 ≤ reserve → a0 ≤ asource →
    let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
    P.Nonempty →
    ∀ Mdecl Mwidth θclip : ℝ, 0 ≤ θclip →
    length Z src.X₁+length Z src.X₂+6*(3/4)*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap → Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀ Mgeom Mvolume heightCap : ℝ, 1 ≤ Mgeom → 0 ≤ heightCap →
    Z^(Mgeom/4)≤ src.X₁ → Z^(Mgeom/4)≤ src.X₂ → Z^(Mgeom/4)≤ src.Y₁ → Z^(Mgeom/4)≤ src.Y₂ →
    Mgeom≤ Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
    Real.logb Z (volume src)≤(883/1000)*Mgeom → Real.logb Z (volume src)≤ Mvolume →
    Real.logb Z fixedPresentationCost≤1/1000 →
    Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ))≤1/250 →
    (Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh ≤ 1/10000 →
    delta+reserve ≤ 1/1000 → εsrc*Mvolume ≤ 1/1000 →
    ∀ radius : (p : Labels src R seedOuter) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
    (∀ p E, radius p E ≤ Crfirst*Z^Lfirst) →
    let q := firstSourceOuterLabel src R seedOuter K radius
    ∀ (labels : Finset (FirstSourceOuterIndex src R seedOuter K radius)) (p : ℝ),
    (∀ i ∈ labels, ((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^p) →
    ∀ left : (k : (i : FirstSourceOuterIndex src R seedOuter K radius) × (q i).SourceIndex) →
      ExtractedErrorRun src (q k.1).C P,
    ∀ right : (k : (i : FirstSourceOuterIndex src R seedOuter K radius) × (q i).SourceIndex) →
      ExtractedErrorRun src (q k.1).D P,
    (∀ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
      (left k).SourceAdmissible (q k.1).D R (q k.1).E ((q k.1).sourceChild k.2).pair.left
        Z K sigma delta reserve Dscale heightCap) →
    (∀ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
      (right k).SourceAdmissible (q k.1).C R (swapSubset (q k.1).C (q k.1).D (q k.1).E)
        ((q k.1).sourceChild k.2).pair.right Z K sigma delta reserve Dscale heightCap) →
    (∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
      (left k).normalizedValue N (q k.1).D R k.2.1.val (q k.1).E
        ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve) ≤
      Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2*
        Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ) ∧
    (∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
      (right k).normalizedValue N (q k.1).C R k.2.1.val
        (swapSubset (q k.1).C (q k.1).D (q k.1).E)
        ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve) ≤
      Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2*
        Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ) := by
  obtain ⟨Calloc,hCalloc,Uprofile,Jheight,hactual⟩ := actual_allocated_extracted_errors_uniform (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ Sbad hbad sigma cost hsigma hξsmall hcost hsigma_eq
    Avol Dscale Pmask qmoving εgeo hεgeo hbudget εalloc hεalloc hloss hsaving
  obtain ⟨Cmass,hCmass,hmass⟩ := actual_first_source_sector_harmonic_mass
    Bfirst Lfirst Crfirst εouter hBfirst hLfirst hCrfirst hεouter
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Calloc*Cbound*Cmass,mul_pos (mul_pos hCalloc hCbound) hCmass,?_⟩
  filter_upwards [hactualZ,hmass,eventually_fixed_pair_error_source_caps M H Sbad hbad εconductor hεconductor]
    with Z hZ hmass hcaps
  refine ⟨hZ.1,?_⟩
  intro Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max hParent
    R seedOuter hR hseedOuter hseedOuter0
    hzero1 hzero2 hvolumeCap hmaskCap hHsource hHcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hP Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
    Mgeom Mvolume heightCap hgeom hheightCap hplainX₁ hplainX₂ hplainY₁ hplainY₂
    hwidth hvolGeom hvolCap hfixed hdef hpaid hfrequency hepsSmall radius hr
  let q := firstSourceOuterLabel src R seedOuter K radius
  intro labels p hrad left right hleft hright
  let F := Calloc*Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  have hm := hmass.2 Aorig src R seedOuter hseedOuter hseedOuter0 hzero1 hzero2
    hHsource hHcap K hK radius hr labels p hrad
  have hsingle (C D seed : Ideal O) (hC : Supported C) (hD : Supported D)
      (hCD : primeSupport C=primeSupport D) (E : Finset (CommonIndex C D)) (τ : Character)
      (hmod : τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
        Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E*activeConductor C D})
      (hseed : Squarefree seed) (hseed0 : seed ≠ 0) (hseedcap : (seed.absNorm : ℝ) ≤ Z^Bseed)
      (x : ExtractedErrorRun src C (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
      (hx : x.Admissible D R E τ Z K sigma delta reserve cost Dscale qmoving Bfirst heightCap) :
      x.normalizedValue N D R seed E τ upper Z K sigma delta reserve ≤
        F*Z^(-1/2500 : ℝ)/(seed.absNorm : ℝ) := by
    exact hZ.2 Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
      C D R hC hD hCD E τ x.height hmod K delta reserve asource hK hasource hdelta hreserve haSource
      hP hx.slot_coprime x.family hx.radical_cap hx.moving_cap
      hzero1 hzero2 hvolumeCap hmaskCap hR hx.radius_inv hx.conductor_cap
      seed hseed hseed0 hseedcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂
      hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
      Bfirst heightCap hheightCap hx.height_le hx.common_cap hallocSmall hpaid hfrequency hepsSmall
  have hnorm (i : FirstSourceOuterIndex src R seedOuter K radius) :=
    actual_first_label_norm_caps src R seedOuter hseedOuter hzero1 hzero2 Z Bfirst hHcap i.1
  have hleftBound (k : (i : FirstSourceOuterIndex src R seedOuter K radius) × (q i).SourceIndex)
      (hk : k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src)) :
      (left k).normalizedValue N (q k.1).D R k.2.1.val (q k.1).E
        ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve ≤
        F*Z^(-1/2500 : ℝ)/(k.2.1.val.absNorm : ℝ) := by
    obtain ⟨_,hs,hs0,hscap⟩ := firstLeftSourceLabels_gates labels q (fun _ => sourceRadius src)
      Z Bfirst hz.le (fun _ _ => hHcap) k hk
    have hx := hleft k hk
    let v := (q k.1).sourceChild k.2
    have hcs := hcaps.2 src.η v.C v.D v.hC v.E v.leftRay v.rightRay v.pair
      qParent Bfirst sigma cost qmoving hParent (hnorm k.1).1 hcostSource hconductorBudget
    apply hsingle v.C v.D k.2.1.val v.hC v.hD v.hCD v.E v.pair.left v.pair.left_modulus hs hs0
      (hscap.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hseedBudget)) (left k)
    refine ⟨hx.height_le,(hnorm k.1).1,hx.slot_coprime,hx.radical_cap,?_,hx.radius_inv,?_⟩
    · intro B hB prime i χ
      exact (hcs v.pair.left ((left k).family B prime i χ) (Or.inl rfl) χ prime i
        (hx.radical_cap B hB prime i χ)).1
    · intro B hB prime i χ
      exact (hcs v.pair.left ((left k).family B prime i χ) (Or.inl rfl) χ prime i
        (hx.radical_cap B hB prime i χ)).2
  have hrightBound (k : (i : FirstSourceOuterIndex src R seedOuter K radius) × (q i).SourceIndex)
      (hk : k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src)) :
      (right k).normalizedValue N (q k.1).C R k.2.1.val
        (swapSubset (q k.1).C (q k.1).D (q k.1).E)
        ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve ≤
        F*Z^(-1/2500 : ℝ)/(k.2.1.val.absNorm : ℝ) := by
    obtain ⟨_,hs,hs0,hscap⟩ := firstRightSourceLabels_gates labels q (fun _ => sourceRadius src)
      Z Bfirst hz.le (fun _ _ => hHcap) k hk
    have hx := hright k hk
    let v := (q k.1).sourceChild k.2
    have hcs := hcaps.2 src.η v.C v.D v.hC v.E v.leftRay v.rightRay v.pair
      qParent Bfirst sigma cost qmoving hParent (hnorm k.1).1 hcostSource hconductorBudget
    apply hsingle v.D v.C k.2.1.val v.hD v.hC v.hCD.symm (swapSubset v.C v.D v.E) v.pair.right
      (right_modulus src.η v.C v.D v.hC v.E v.leftRay v.rightRay v.pair) hs hs0
      (hscap.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hseedBudget)) (right k)
    refine ⟨hx.height_le,(hnorm k.1).2,hx.slot_coprime,hx.radical_cap,?_,hx.radius_inv,?_⟩
    · intro B hB prime i χ
      exact (hcs v.pair.right ((right k).family B prime i χ) (Or.inr rfl) χ prime i
        (hx.radical_cap B hB prime i χ)).1
    · intro B hB prime i χ
      exact (hcs v.pair.right ((right k).family B prime i χ) (Or.inr rfl) χ prime i
        (hx.radical_cap B hB prime i χ)).2
  have hscalar : (F*Z^(-1/2500 : ℝ))*(Cmass*Z^(p+εouter)/(seedOuter.absNorm : ℝ)) =
      (Calloc*Cbound*Cmass)*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2*
        Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ) := by
    rw [show p-1/2500+εouter = (-1/2500)+(p+εouter) by ring]
    simp only [Real.rpow_add hz]
    dsimp [F]
    ring
  constructor
  · calc
      _ ≤ ∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
          F*Z^(-1/2500 : ℝ)/(k.2.1.val.absNorm : ℝ) := Finset.sum_le_sum hleftBound
      _ = (F*Z^(-1/2500 : ℝ))*(∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
          1/(k.2.1.val.absNorm : ℝ)) := by simp only [Finset.mul_sum,mul_one_div]
      _ ≤ (F*Z^(-1/2500 : ℝ))*(Cmass*Z^(p+εouter)/(seedOuter.absNorm : ℝ)) :=
        mul_le_mul_of_nonneg_left hm.1 (mul_nonneg hF (Real.rpow_nonneg hz.le _))
      _ = _ := hscalar
  · calc
      _ ≤ ∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
          F*Z^(-1/2500 : ℝ)/(k.2.1.val.absNorm : ℝ) := Finset.sum_le_sum hrightBound
      _ = (F*Z^(-1/2500 : ℝ))*(∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
          1/(k.2.1.val.absNorm : ℝ)) := by simp only [Finset.mul_sum,mul_one_div]
      _ ≤ (F*Z^(-1/2500 : ℝ))*(Cmass*Z^(p+εouter)/(seedOuter.absNorm : ℝ)) :=
        mul_le_mul_of_nonneg_left hm.2 (mul_nonneg hF (Real.rpow_nonneg hz.le _))
      _ = _ := hscalar

#print axioms actual_first_independent_extracted_errors
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstIndependentErrors -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighSourceDyadic ; sha256 28d3fd4e85a1907333aa469dc2bb98a0baceebb301a65557322d65bca52649b6 -/
section




/-! The genuine high-source estimate summed over both actual dyadic block
families. Maximization pays their subpower mass without recounting arithmetic rows. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization HeckeDetectorDyadicGeometry
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput RayFourExpansion
open NonzeroJointSourceRow
local notation "O" => HeckeFamily.O

section FixedData
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (η : Character) (η₀ : Slot → Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (hQM : Q ≤ M)
  (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
  (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hβ hH hQM hQη₀ S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

theorem actual_joint_high_source_dyadic
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (ηcommon : Character) (hanchor : ∀ j, η₀ j = ηcommon)
    (Wslot : ℝ → ℂ) (hVslot : ∀ j, V j = Wslot)
    (bslot : ℝ) (hBslot : ∀ j, Bprofile j = bslot)
    (Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 < ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hproductLoss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ productLoss)
    (hpopulationLoss : 0 < populationLoss) (hB : 0 ≤ B)
    (hloss : populationLoss+dmax*productLoss ≤ loss)
    (τdetector dmin heightLoss : ℝ) (I : ℕ)
    (hτdetector : 0 < τdetector) (hdmin : 0 < dmin) (hheightLoss : 0 < heightLoss)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂plain : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂plain) (hW₂ : ContDiff ℝ ∞ W₂)
    (lo hi : Slot → ℝ) (fiberLoss : ℝ) (hfiberLoss : 0 < fiberLoss)
    (aSource Mslot upper : ℝ) (haSource : 0 < aSource) (hMslot : 0 ≤ Mslot)
    (conductorReserve : ℝ) (hconductorReserve : 0 < conductorReserve)
    (Sbad : Finset (Ideal O)) (primeLoss : ℝ) (hprimeLoss : 0 < primeLoss)
    (hprimeReserve : primeLoss ≤ 144011/219600000)
    (Wkernel : 𝓢(ℝ,ℂ))
    (tailA targetLower plainBound₁ plainBound₂ : ℝ)
    (hplainBound₁ : 0 ≤ plainBound₁) (hplainBound₂ : 0 ≤ plainBound₂)
    (hplainNorm₁ : ∀ x, ‖W₁ x‖ ≤ plainBound₁) (hplainNorm₂ : ∀ x, ‖W₂ x‖ ≤ plainBound₂)
    (Bdyad₁ Ldyad₁ Crdyad₁ Bdyad₂ Ldyad₂ Crdyad₂ dyadicLoss : ℝ)
    (hBdyad₁ : 0 ≤ Bdyad₁) (hLdyad₁ : 0 ≤ Ldyad₁) (hCrdyad₁ : 0 < Crdyad₁)
    (hBdyad₂ : 0 ≤ Bdyad₂) (hLdyad₂ : 0 ≤ Ldyad₂) (hCrdyad₂ : 0 < Crdyad₂)
    (hdyadicLoss : 0 < dyadicLoss) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N Nkernel : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (d P W : ℝ), dmin ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (input : Input Slot) (puncture seed : Ideal O)
        (hpuncture : puncture ≠ 0) (hseed : Squarefree seed)
        (hz₁ : input.W₁ 0 = 0) (hz₂ : input.W₂ 0 = 0)
        (side : Bool) (ξ₁ ξ₂ : RayCharacter)
        (fallback : NonzeroJointSourceRow (original input puncture seed) side)
        (qs : Finset (NonzeroJointSourceRow (original input puncture seed) side)),
      let S := qs.image NonzeroJointSourceRow.label
      let unit := sourceUnit fallback η ξ₁ ξ₂
      let w := sourceRow fallback η ξ₁ ξ₂
      let s := sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ 1 1
      let first := sourceFirst fallback η ξ₁ ξ₂
      let z := sourceFrequency fallback
      let Ds := fun v => (s v).physicalProjectors
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ q ∈ qs, Squarefree q.val.L) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ Kfirst Rfirst Hfirst : NonzeroJointSourceRow (original input puncture seed) side → ℝ,
      (∀ q ∈ qs, 0 < Kfirst q ∧ 0 < Hfirst q ∧
        Rfirst q ≤ Crdyad₁*Z^Ldyad₁ ∧ Hfirst q ≤ Z^Bdyad₁) →
      ∀ Ksecond Rsecond Hsecond : (q : NonzeroJointSourceRow (original input puncture seed) side) → q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q) → ℝ,
      (∀ q ∈ qs, ∀ n₁, 0 < Ksecond q n₁ ∧
        Rsecond q n₁ ≤ Crdyad₂*Z^Ldyad₂ ∧ Hsecond q n₁ ≤ Z^Bdyad₂) →
      ∀ (t tbase firstU firstTheta : (q : NonzeroJointSourceRow (original input puncture seed) side) → q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q) → ℝ)
        (good : (q : NonzeroJointSourceRow (original input puncture seed) side) → q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q) → Prop)
        (σ freq : JointReconstructionLabel → Slot → ℝ)
        (θ : JointReconstructionLabel → Slot → RayQuotient.Characters M H)
        (slotWidth : JointReconstructionLabel → Slot → ℝ),
      (∀ v ∈ S, (∀ j, (s v).input.M j ≤ Mslot) ∧ (s v).input.upper ≤ upper ∧
        (s v).input.b₁ ≤ b₁ ∧ (s v).input.b₂ ≤ b₂plain) →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ v ∈ S, (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^(2*B) ∧
        (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, ∀ L ∈ Ds v, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 →
        (L.absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        0 < dyadicScale (b.2 2) ∧ 0 < dyadicScale (b.2 3) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s q.label).input.toData/
          (((s q.label).firstCommon*(s q.label).second.val.1).absNorm : ℝ) ≤ dyadicScale (b.2 2) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s q.label).input.toData/
          (((s q.label).firstCommon*(s q.label).second.val.2).absNorm : ℝ) ≤ dyadicScale (b.2 3)) →
      ∀ Bmask : ℝ, W+Bmask+conductorReserve ≤ d →
      (∀ v ∈ S, (((first v).leftPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask ∧
        (((first v).rightPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask) →
      (∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂) →
      (∀ v ∈ S, CenteredMomentAllocatedRayDictionary.Matches M H hH (s v).input
        ηcommon (θ v) (slotWidth v) (σ v) (freq v) Wslot bslot Z) →
      (∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth) →
      (∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        t q b.1 = tbase q b.1+2*Real.pi*(firstU q b.1-firstTheta q b.1)) →
      (∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        |tbase q b.1| ≤ Z^ν ∧ |firstU q b.1| ≤ Z^ν ∧ |firstTheta q b.1| ≤ Z^ν) →
      (∀ v ∈ S, ∀ j, σmin ≤ σ v j ∧ σ v j ≤ σmax) →
      (∀ v ∈ S, ∀ j, |freq v j| ≤ Z^ν) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      ∀ supportLoss clipLoss commonLoss : ℝ, supportLoss+clipLoss+commonLoss ≤ lengthLoss →
      (∀ v ∈ S, CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData ≤ Z^A) →
      (∀ v ∈ S, Z^(c+c₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ∧
        Z^(c+d₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ)) →
      (∀ v ∈ S, (max 1 (s v).input.upper)^Fintype.card Slot ≤ Z^supportLoss) →
      Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ clipLoss →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss ≤ tailA →

      targetLower ≤ π+A-c+R₁+E+Bc-144011/109800000 →
      ∀ scalarLoss : ℝ,
      (∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        Ksecond q b.1 ≤ Z^(2*A-c-d₁+R₁+E-1+max (d₁-c) 0+6*(3/500)+(omegaLoss-scalarLoss))) →
      (∀ v ∈ S, (s v).secondLogCost Z ≤ g₂-t₂cost-b₂+scalarLoss) →
      ∀ volumeLoss : ℝ,
      Z^(A-volumeLoss) ≤ CenteredMomentExceptionalAmplitudePair.volume input.toData →
      (∑ q ∈ qs, ∑ n₁ : q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q),
        ∑ n₂ : q.val.SecondDyadic (Ksecond q n₁) (Rsecond q n₁) (Hsecond q n₁),
          if good q ⟨n₁,n₂⟩ then
            ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ∑ D ∈ Ds q.label,
              ‖((s q.label).withRays χ ξ).physicalRowTerm
                (CenteredMomentExceptionalAmplitudePair.volume input.toData)
                (actualHighPrimeCount M H Sbad Z)
                (t q n₁) q.val.z Wkernel (Ksecond q n₁) (Rsecond q n₁) (fun j => n₂ j) D‖
          else 0) ≤ C*Z^(π+A-2*c+R₁+E+Bc+volumeLoss-144011/219600000+dyadicLoss) := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_source_original_volume η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV ηcommon hanchor Wslot hVslot bslot hBslot
      Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B
      hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget hproductLoss hpopulationLoss hB hloss
      τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi fiberLoss hfiberLoss
      aSource Mslot upper haSource hMslot conductorReserve hconductorReserve
      Sbad primeLoss hprimeLoss hprimeReserve Wkernel tailA targetLower plainBound₁ plainBound₂
      hplainBound₁ hplainBound₂ hplainNorm₁ hplainNorm₂
  obtain ⟨Cdyad,hCdyad,hdyad⟩ := actual_source_live_dyadic_sum_bound
    Bdyad₁ Ldyad₁ Crdyad₁ Bdyad₂ Ldyad₂ Crdyad₂ dyadicLoss
    hBdyad₁ hLdyad₁ hCrdyad₁ hBdyad₂ hLdyad₂ hCrdyad₂ hdyadicLoss
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,Cdyad*C,hν,hντ,hτdet,hheight,horders,
    mul_pos hCdyad hC,?_⟩
  filter_upwards [hhigh,hdyad] with Z hZ hdyadZ
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
    input puncture seed hpuncture hseed hz₁ hz₂ side ξ₁ ξ₂ fallback qs
  dsimp only
  let S := qs.image NonzeroJointSourceRow.label
  let w := sourceRow fallback η ξ₁ ξ₂
  let s := sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ 1 1
  let first := sourceFirst fallback η ξ₁ ξ₂
  let Ds := fun v => (s v).physicalProjectors
  intro R hR hprojSource hbin hnorm hNw hNr
    Kfirst Rfirst Hfirst hfirstDyadic Ksecond Rsecond Hsecond hsecondDyadic
    t tbase firstU firstTheta good σ freq θ slotWidth
    hprofileCaps hsourceIntervals hsourceNorm hprojectorNorm hphysical
    Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hKactual hcost volumeLoss hVolumeLower
  let value (q : NonzeroJointSourceRow (original input puncture seed) side)
      (b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q)) : ℝ :=
    ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ∑ D ∈ Ds q.label,
      ‖((s q.label).withRays χ ξ).physicalRowTerm
        (CenteredMomentExceptionalAmplitudePair.volume input.toData)
        (actualHighPrimeCount M H Sbad Z)
        (t q b.1) q.val.z Wkernel (Ksecond q b.1) (Rsecond q b.1) (fun j => b.2 j) D‖
  have hchoice (Qrows : Finset (NonzeroJointSourceRow (original input puncture seed) side))
      (hQrows : Qrows ⊆ qs)
      (pick : (q : Qrows) → q.val.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q)
        (Ksecond q) (Rsecond q) (Hsecond q))
      (hpick : ∀ q : Qrows, good q (pick q)) :
      (∑ q : Qrows, value q (pick q)) ≤
        C*Z^(π+A-2*c+R₁+E+Bc+volumeLoss-144011/219600000) := by
    let t' := extendFiniteData Qrows (fun q => t q (pick q).1)
    let K' := extendFiniteData Qrows (fun q => Ksecond q (pick q).1)
    let Radius' := extendFiniteData Qrows (fun q => Rsecond q (pick q).1)
    let tbase' := extendFiniteData Qrows (fun q => tbase q (pick q).1)
    let firstU' := extendFiniteData Qrows (fun q => firstU q (pick q).1)
    let firstTheta' := extendFiniteData Qrows (fun q => firstTheta q (pick q).1)
    let n' := extendFiniteData Qrows (fun q j => ((pick q).2 j : ℤ))
    have hsub : Qrows.image NonzeroJointSourceRow.label ⊆ S := Finset.image_subset_image hQrows
    have hphysical' : ∀ v ∈ Qrows.image NonzeroJointSourceRow.label,
        0 < dyadicScale (n' v 2) ∧ 0 < dyadicScale (n' v 3) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ dyadicScale (n' v 2) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ dyadicScale (n' v 3) := by
      intro v hv
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
      simpa only [n',extendFiniteData_of_mem Qrows q hq] using
        hphysical q (hQrows hq) (pick ⟨q,hq⟩) (hpick ⟨q,hq⟩)
    have hteq' : ∀ v ∈ Qrows.image NonzeroJointSourceRow.label,
        t' v = tbase' v+2*Real.pi*(firstU' v-firstTheta' v) := by
      intro v hv
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
      simpa only [t',tbase',firstU',firstTheta',extendFiniteData_of_mem Qrows q hq] using
        hteq q (hQrows hq) (pick ⟨q,hq⟩) (hpick ⟨q,hq⟩)
    have hinputfreq' : ∀ v ∈ Qrows.image NonzeroJointSourceRow.label,
        |tbase' v| ≤ Z^ν ∧ |firstU' v| ≤ Z^ν ∧ |firstTheta' v| ≤ Z^ν := by
      intro v hv
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
      simpa only [tbase',firstU',firstTheta',extendFiniteData_of_mem Qrows q hq] using
        hinputfreq q (hQrows hq) (pick ⟨q,hq⟩) (hpick ⟨q,hq⟩)
    have hK' : ∀ v ∈ Qrows.image NonzeroJointSourceRow.label, 0 < K' v ∧
        K' v ≤ Z^(2*A-c-d₁+R₁+E-1+max (d₁-c) 0+6*(3/500)+(omegaLoss-scalarLoss)) := by
      intro v hv
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
      simpa only [K',extendFiniteData_of_mem Qrows q hq] using
        And.intro (hsecondDyadic q (hQrows hq) (pick ⟨q,hq⟩).1).1
          (hKactual q (hQrows hq) (pick ⟨q,hq⟩) (hpick ⟨q,hq⟩))
    have hh := hZ.2 d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
      input puncture seed hpuncture hseed hz₁ hz₂ side ξ₁ ξ₂ fallback Qrows
      R hR (fun q hq => hprojSource q (hQrows hq))
      (fun v hv => hbin v (hsub hv)) (fun v hv => hnorm v (hsub hv))
      (fun v hv => hNw v (hsub hv)) (fun v hv => hNr v (hsub hv))
      t' K' Radius' tbase' firstU' firstTheta' n' σ freq θ slotWidth
      (fun v hv => hprofileCaps v (hsub hv)) (fun v hv => hsourceIntervals v (hsub hv))
      (fun v hv => hsourceNorm v (hsub hv)) (fun v hv => hprojectorNorm v (hsub hv)) hphysical'
      Bmask hconductorBalance (fun v hv => hmaskNorm v (hsub hv))
      (fun v hv => hplain v (hsub hv)) (fun v hv => hmatch v (hsub hv))
      (fun v hv => hscale v (hsub hv)) (fun v hv => hprimeScale v (hsub hv))
      hteq' hinputfreq' (fun v hv => hσrange v (hsub hv)) (fun v hv => hslotfreq v (hsub hv))
      A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
      supportLoss clipLoss commonLoss hlengthLossSplit (fun v hv => hvolume v (hsub hv))
      (fun v hv => hcommonDyads v (hsub hv)) (fun v hv => hsupport v (hsub hv)) hclip
      hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
      hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hK'
      (fun v hv => hcost v (hsub hv)) volumeLoss hVolumeLower
    have heq : (∑ q : Qrows, value q (pick q)) =
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ∑ q ∈ Qrows, ∑ D ∈ Ds q.label,
          ‖((s q.label).withRays χ ξ).physicalRowTerm
            (CenteredMomentExceptionalAmplitudePair.volume input.toData)
            (actualHighPrimeCount M H Sbad Z)
            (t' q.label) (sourceFrequency fallback q.label) Wkernel
            (K' q.label) (Radius' q.label) (n' q.label) D‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [←Finset.sum_coe_sort Qrows]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [value,t',K',Radius',n',extendFiniteData_apply,sourceFrequency,recover_label]
    exact heq.trans_le hh
  have hs := hdyadZ.2 (original input puncture seed) side qs Subtype.val
    Kfirst Rfirst Hfirst hfirstDyadic Ksecond Rsecond Hsecond hsecondDyadic
    good value (fun _ _ _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))))
    (C*Z^(π+A-2*c+R₁+E+Bc+volumeLoss-144011/219600000)) hchoice
  change _ ≤ (Cdyad*C)*Z^(π+A-2*c+R₁+E+Bc+volumeLoss-144011/219600000+dyadicLoss)
  apply hs.trans_eq
  rw [Real.rpow_add (zero_lt_one.trans hZ.1)
    (π+A-2*c+R₁+E+Bc+volumeLoss-144011/219600000) dyadicLoss]
  ring

end FixedData
#print axioms actual_joint_high_source_dyadic
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighSourceDyadic -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowCommonAggregate ; sha256 b2bbba2f76b42e52dc82327c1e272e5afed63783fc94f411effe5e00f7bab963 -/
section


/-! Harmonic aggregation of the literal low physical bins for one first
common label. The pointwise input is exactly the actual prime-normalized
kernel estimate supplied by JointLowPhysicalKernel; this step uses no
moment estimate or population count. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentMobiusRegroup CenteredMomentFixedRay RayFourExpansion
open CenteredMomentSecondSectorColumns CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O

def actualCommonBlockKernelLabel {ι : Type*} [Fintype ι]
    (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁) (hseed : seed ∣ C₁)
    (η : Character) (K Radius Hsource : ℝ)
    (q : ActiveBlocks (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁) K Radius Hsource)
    (D : Ideal O) (χ ξ : RayCharacter) : CommonSecondKernelLabel ι :=
  ⟨src,R,seed,C₁,L₁,hC₁,hseed,η,q.1.1,q.1.2,D,χ,ξ⟩

theorem actual_common_second_low_rows
    (B Bproj L Cr ε : ℝ) (hB : 0 ≤ B) (hBproj : 0 ≤ Bproj) (hL : 0 ≤ L)
    (hCr : 0 < Cr) (hε : 0 < ε) (hBBproj : B ≤ Bproj) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁) (hseed : seed ∣ C₁),
      src.W₁ 0 = 0 → src.W₂ 0 = 0 → sourceRadius src/(C₁.absNorm : ℝ) ≤ Z^B →
      ∀ (η : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K Radius Hsource V P E F saving target : ℝ),
      0 < K → Radius ≤ Cr*Z^L → Hsource ≤ Z^B → 0 < V → 0 < P → 0 ≤ E → 0 ≤ F → Bproj ≤ saving →
      let columns := commonSecondColumns (original src R seed) C₁ hC₁
      let β := commonSecondBeta (original src R seed) C₁ L₁
      let Ds := actualSecondProjectors columns β K Radius Hsource
      ∀ rows : ActiveBlocks columns β K Radius Hsource → Finset O,
      (∀ q, ∀ z ∈ rows q,z ≠ 0) →
      (∀ q, activePhysicalRows η t columns β W K Radius Hsource q (rows q) ≠ 0 →
        ∀ D ∈ Ds q, (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 → ∀ χ ξ : RayCharacter,
        secondPrecountFactor V P q.1.1.val.1 q.1.1.val.2 q.1.2 K (fun i => (q.2 i : ℤ))*
          (∑ z ∈ rows q,‖(actualCommonBlockKernelLabel src R seed C₁ L₁ hC₁ hseed η K Radius Hsource q D χ ξ).toKernelLabel.kernelRow
            t z W K Radius (fun i => (q.2 i : ℤ))‖) ≤
          pairWeight q.1.1.val.1 q.1.1.val.2*(E/(D.absNorm : ℝ)+F*Z^(-saving))*Z^target) →
      ‖actualSecondRowBlocks η t columns β W K Radius Hsource rows‖/(V*P) ≤
        Cbound*(E+F)*Z^(target+ε) := by
  obtain ⟨C,hC,hmain⟩ := actual_common_second_mixed_harmonic_mass B Bproj L Cr ε hB hBproj hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hmain] with Z hmain
  refine ⟨hmain.1,?_⟩
  intro ι instF instD src R seed C₁ L₁ hC₁ hseed hz₁ hz₂ hsource η t W K Radius Hsource V P E F saving target
    hK hRadius hH hV hP hE hF hsaving columns β Ds rows hrows hlocal
  have hZ0 : 0 < Z := zero_lt_one.trans hmain.1
  have hnorm : ∀ I ∈ columns,β I ≠ 0 → (I.absNorm : ℝ) ≤ Z^B := by
    intro I hI hβ
    exact (commonSecond_source_norm_cap (original src R seed) C₁ L₁ hC₁ (sourceRadius src)
      (fun J _ hJ => (original_column_norm src R seed J hz₁ hz₂ hJ).2) I hI hβ).trans hsource
  have hDs : ∀ q, ∀ D ∈ Ds q, (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 →
      (D.absNorm : ℝ) ≤ Z^Bproj := by
    intro q D hD hμ
    exact (actualSecondProjectors_norm_cap columns β K Radius Hsource (Z^B) hnorm q D hD).trans
      (Real.rpow_le_rpow_of_exponent_le hmain.1.le hBBproj)
  let budget := fun q : ActiveBlocks columns β K Radius Hsource =>
    ∑ D ∈ Ds q, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
      ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖*
        ‖pairCoeff (phaseTable (primaryGenerator q.1.1.val.1) (primaryGenerator q.1.1.val.2)) χ ξ‖*
        pairWeight q.1.1.val.1 q.1.1.val.2*(E/(D.absNorm : ℝ)+F*Z^(-saving))
  have hm : (∑ q,budget q) ≤ C*(E+F)*Z^ε :=
    hmain.2 src R seed C₁ L₁ hC₁ hz₁ hz₂ hsource K Radius Hsource hK hRadius hH Ds hDs E F saving hE hF hsaving
  have hb (q : ActiveBlocks columns β K Radius Hsource) :
      ‖activePhysicalRows η t columns β W K Radius Hsource q (rows q)‖/(V*P) ≤ budget q*Z^target := by
    by_cases hzero : activePhysicalRows η t columns β W K Radius Hsource q (rows q) = 0
    · rw [hzero,norm_zero,zero_div]
      have hpw := pairWeight_nonneg q.1.1.val.1 q.1.1.val.2
      dsimp [budget]
      positivity
    apply (activePhysicalRows_projected_majorant η t columns β W K Radius Hsource V P hK hV hP q (rows q) (hrows q)).trans
    dsimp [budget]
    simp only [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro D hD
    apply Finset.sum_le_sum
    intro χ hχ
    apply Finset.sum_le_sum
    intro ξ hξ
    by_cases hμ : (UniqueFactorizationMonoid.moebius D : ℂ) = 0
    · simp [hμ]
    have hl := hlocal q hzero D hD hμ χ ξ
    rw [CommonSecondKernelLabel.toKernelLabel_eq_projected] at hl
    have hh := mul_le_mul_of_nonneg_left hl
      (mul_nonneg (norm_nonneg (UniqueFactorizationMonoid.moebius D : ℂ))
        (norm_nonneg (pairCoeff (phaseTable (primaryGenerator q.1.1.val.1) (primaryGenerator q.1.1.val.2)) χ ξ)))
    convert hh using 1 <;> (try dsimp [actualCommonBlockKernelLabel]) <;> ring
  calc
    _ ≤ (∑ q,‖activePhysicalRows η t columns β W K Radius Hsource q (rows q)‖)/(V*P) :=
      div_le_div_of_nonneg_right (actualSecondRowBlocks_norm_le η t columns β W K Radius Hsource rows) (mul_pos hV hP).le
    _ ≤ ∑ q,budget q*Z^target := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun q _ => hb q)
    _ = (∑ q,budget q)*Z^target := by rw [Finset.sum_mul]
    _ ≤ (C*(E+F)*Z^ε)*Z^target := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hZ0.le _)
    _ = _ := by rw [Real.rpow_add hZ0]; ring

/-- The direct coherent amplifier is normalized by the original volume.
The common-volume estimate therefore keeps its inverse first-common norm. -/
lemma low_rows_original_volume (value : ℂ) (V P N E : ℝ)
    (hV : 0 < V) (hP : 0 < P) (hN : 0 < N)
    (h : ‖value‖/(V*P) ≤ E) : ‖value‖/((N*V)*P) ≤ E/N := by
  have hh := div_le_div_of_nonneg_right h hN.le
  convert hh using 1 <;> ring


/-- Exact conversion of the internally obtained low endpoint to the
harmonic aggregate's two coefficients. The arbitrary tail saving absorbs
the same fixed profile loss that is present in the main exponent. -/
lemma low_physical_harmonic_form (C Elow a N pair Eabs Z base small primeLoss tailSaving : ℝ)
    (hZ : 0 < Z) :
    C*((Elow/(a*N))*pair*Z^(base+small+primeLoss)+
      (128/a)*Eabs^2*pair*Z^(base-tailSaving+primeLoss)) =
      pair*((C*Elow/a)/N+(C*(128/a)*Eabs^2)*Z^(-(tailSaving+small)))*
        Z^((base+small+primeLoss)) := by
  have he : Z^(base-tailSaving+primeLoss) =
      Z^(-(tailSaving+small))*Z^(base+small+primeLoss) := by
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  rw [he]
  ring

#print axioms actual_common_second_low_rows
#print axioms low_rows_original_volume
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowCommonAggregate -/

/- BEGIN ORIGINAL MODULE Global.Low.SourceProbe ; sha256 4f13cbaac1b5f15846fa91f557a892d2bf3721a2ddc0cf2524b7b0a29de41d2b -/
section






namespace Submission20261012.Global

noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
namespace ProbeAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

def normalizedProbe {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j=> Z^(ell j)
  let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=> canonicalSlotSupport (T j)) (fun j y=>(W j y:ℂ)) Yp
    (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell) (slotMass T (residueWeights W Yp)) : ℂ))

lemma isBigO_rpow_of_eventual_norm_bound (f : ℝ→ℂ) (r : ℝ)
    (h : ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,‖f Z‖≤ C*Z^r) :
    f=O[atTop](fun Z : ℝ=> Z^r) := by
  obtain ⟨C,hC,hb⟩ := h
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with Z hb hZ
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hZ r)] using hb

theorem normalizedProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=Submission20261012.Global.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,normalizedProbe M H S hmax ell a b W W0 W1 η=O[atTop](fun Z : ℝ=> Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := LowProbe.original_normalized_compensatedPhysicalProbe_low M H hH S hS hmax
    a b B loss ha hab hloss ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  apply isBigO_rpow_of_eventual_norm_bound
  exact ⟨C,hC,hb.mono (fun Z h=> h.2)⟩

theorem actual_source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) :
    (∀I,idealCoeff (η.excludePrimes S hS.prime) I=
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ|Submission20261012.Global.theta < s.re} ∧
    (∀s : ℂ,Submission20261012.Global.theta < s.re→‖sourceCorrection η S s-1‖≤1/2) := by
  exact ⟨excludePrimes_mask η S hS.prime,
    (Submission20261012.Global.LowCorrection.weighted_globalClosedCorrection_analytic_x η S hS.tail 1 (1/6) (by norm_num) (by norm_num)),
    fun s hs => Submission20261012.Global.LowCorrection.weighted_globalClosedCorrection_bound η S hS.tail s 1 (1/6) hs.le (by norm_num) (by norm_num)⟩

def sourceProbe {Δ : ℝ} (D : Submission20261012.Global.HighParameters.HighData Δ)
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D.toMomentData) (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  normalizedProbe F.modulus ⊤ F.S F.maximal D.ell 1 2 (fun _=> F.w) F.W F.W η

theorem sourceProbe_low {Δ : ℝ} (D : Submission20261012.Global.HighParameters.HighData Δ)
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D.toMomentData)
    (loss : ℝ) (hloss : 0 < loss) (η : Character) :
    sourceProbe D F η =O[atTop](fun Z : ℝ=> Z^(Submission20261012.Global.signal Submission20261012.Global.theta+loss)) := by
  have hh := normalizedProbe_low F.modulus ⊤ le_top F.S F.exclusions F.maximal 1 2 1 loss
    (by norm_num) (by norm_num) hloss D.ell (fun j=>(D.slots_bounds j).1) D.slots_injective D.slots_sum
    (fun _=> F.w) (fun _=> F.smooth) (fun _=> F.compact) (fun _=> F.support)
    (fun _=> F.bounded) (fun _=> F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero η
  exact hh

end ProbeAssembly
end

end Submission20261012.Global

/- Adapted from weighted upstream 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

#print axioms Submission20261012.Global.ProbeAssembly.actual_source_analytic
#print axioms Submission20261012.Global.ProbeAssembly.sourceProbe_low
end
/- END ORIGINAL MODULE Global.Low.SourceProbe -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalGates ; sha256 0f3730e91b7dba6afc1745ef01227d13a39a2d9d8001565399ced4edf05c2c72 -/
section



/-! Literal coherent source support discharges the exceptional projector
and expanded-conductor gates, including the cumulative first extraction. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondBlockAggregate
open CenteredMomentSecondSectorColumns CenteredMomentActiveSource CenteredMomentFirstSectors
open CenteredMomentMobiusRegroup CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondHeightFamily CenteredMomentReflectedSource
open CenteredMomentSecondPhysicalBlock CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondLiveBlock
open RayFourExpansion CompletedGauss
local notation "O" => HeckeFamily.O

theorem actual_common_second_projector_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁)
    (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0)
    (p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁))
    (L : Ideal O)
    (hL : L ∈ divisorPool Finset.univ (fun I : sectorPool p.val.2 (lowActiveRightSupported p).1
      (activeSource (commonSecondColumns (original src R seed) C₁ hC₁)
        (commonSecondBeta (original src R seed) C₁ L₁)) => (I : Ideal O))) :
    (L.absNorm : ℝ) ≤ sourceRadius src := by
  obtain ⟨I,hI,hLI⟩ := Finset.mem_biUnion.mp hL
  have hI0 := (sectorPool_supported p.val.2 (lowActiveRightSupported p).1 _ I).1
  have hd := (IdealMobiusDivisorSum.mem_idealDivisors hI0).mp hLI
  have hnorm := commonSecond_source_norm_cap (original src R seed) C₁ L₁ hC₁ (sourceRadius src)
    (fun J _ hJ => (original_column_norm src R seed J hz₁ hz₂ hJ).2)
  have hi := residualPool_data _ _ _ hnorm p.val.2 (lowActiveRightSupported p).1 I
    (Finset.mem_filter.mp I.property).1
  have hl : (L.absNorm : ℝ) ≤ (I.val.absNorm : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI0))
      (map_dvd Ideal.absNorm hd)
  have hN : 1 ≤ ((C₁*p.val.2).absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (mul_ne_zero hC₁.1 (lowActiveRightSupported p).1))
  have hsrc : 0 ≤ sourceRadius src := (zero_le_one.trans hN).trans
    (actual_common_cumulative_norm src R seed C₁ L₁ hC₁ hz₁ hz₂ p).2
  apply hl.trans
  apply hi.2.2.2.2.2.trans
  rw [div_div]
  simpa only [map_mul,Nat.cast_mul] using div_le_self hsrc hN

theorem actual_common_exceptional_conductor_caps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁)
    (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0)
    (p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁))
    (η : Character) (U : Finset (CommonIndex p.val.1 p.val.2))
    (family : RayCharacter → Character)
    (hf : Family η p.val.1 p.val.2 (lowActiveLeftSupported p) (lowActiveRightSupported p) U family)
    (t Radius : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) (n : Fin 4 → ℤ)
    (hne : physicalBlock η t
      (activeSource (commonSecondColumns (original src R seed) C₁ hC₁)
        (commonSecondBeta (original src R seed) C₁ L₁))
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.1 p.val.2
      (lowActiveLeftSupported p) (lowActiveRightSupported p) U Radius rows W K n ≠ 0)
    (Z B : ℝ)
    (hcap : (expandedFactor η : ℝ)*R.absNorm*(sourceRadius src)^2*(4*Radius) ≤ Z^B)
    (z : O) (hrow : (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ 4*Radius)
    (χ ξ : RayCharacter) :
    ((family χ).modulus.absNorm*(Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*(C₁*p.val.1).absNorm)*(Ideal.span {z}).absNorm : ℝ) ≤ Z^B ∧
    ((reflected (family ξ)).modulus.absNorm*(Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*(C₁*p.val.2).absNorm)*(Ideal.span {z}).absNorm : ℝ) ≤ Z^B := by
  have he := expanded_conductor_bounds hf (commonLabels_data _ _ _ _ p.property).2.2 t _ _ Radius rows W K hK n hne
    χ ξ (R*C₁) z
  have hn := actual_common_cumulative_norm src R seed C₁ L₁ hC₁ hz₁ hz₂ p
  have hN : 1 ≤ (C₁.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC₁.1)
  have hprod : (C₁.absNorm : ℝ)*p.val.1.absNorm*p.val.2.absNorm ≤ (sourceRadius src)^2 := by
    have hl : 0 ≤ (p.val.1.absNorm : ℝ) := Nat.cast_nonneg _
    have hr : 0 ≤ (p.val.2.absNorm : ℝ) := Nat.cast_nonneg _
    simp only [map_mul,Nat.cast_mul] at hn
    calc
      _ ≤ ((C₁.absNorm : ℝ)*p.val.1.absNorm)*((C₁.absNorm : ℝ)*p.val.2.absNorm) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hr hN) (by positivity)
      _ ≤ sourceRadius src*sourceRadius src := mul_le_mul hn.1 hn.2 (by positivity)
        ((by positivity : (0:ℝ) ≤ (C₁.absNorm : ℝ)*p.val.1.absNorm).trans hn.1)
      _ = _ := by ring
  have hbound : (expandedFactor η : ℝ)*(R*C₁).absNorm*p.val.1.absNorm*p.val.2.absNorm*(Ideal.span {z}).absNorm ≤ Z^B := by
    apply le_trans _ hcap
    simp only [map_mul,Nat.cast_mul]
    calc
      _ = (expandedFactor η : ℝ)*R.absNorm*((C₁.absNorm : ℝ)*p.val.1.absNorm*p.val.2.absNorm)*(Ideal.span {z}).absNorm := by ring
      _ ≤ (expandedFactor η : ℝ)*R.absNorm*(sourceRadius src)^2*(4*Radius) := by gcongr
  constructor
  · have hle : (expandedConductor (family χ) (R*C₁) p.val.1 z : ℝ) ≤
        (expandedFactor η : ℝ)*(R*C₁).absNorm*p.val.1.absNorm*p.val.2.absNorm*(Ideal.span {z}).absNorm := by exact_mod_cast he.1
    apply le_trans _ (hle.trans hbound)
    simp only [expandedConductor,map_mul,Nat.cast_mul]
    ring_nf
    exact le_rfl
  · have hle : (expandedConductor (reflected (family ξ)) (R*C₁) p.val.2 z : ℝ) ≤
        (expandedFactor η : ℝ)*(R*C₁).absNorm*p.val.1.absNorm*p.val.2.absNorm*(Ideal.span {z}).absNorm := by exact_mod_cast he.2
    apply le_trans _ (hle.trans hbound)
    simp only [expandedConductor,map_mul,Nat.cast_mul]
    ring_nf
    exact le_rfl

#print axioms actual_common_second_projector_norm
#print axioms actual_common_exceptional_conductor_caps
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentSourceTailSum ; sha256 1e01e1eebb8c422155e1073a355ed87b69447b8b4419f7841244136b2383c14e -/
section



/-! The arbitrary-saving discarded tail is summed on the same actual
first source domain as the coherent main and extracted errors, at the
actual source-radius nominal scale. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentSupportedTailAggregate
open CenteredMomentExceptionalAmplitudePair EisensteinSchwartzPoisson
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_first_coherent_source_tail_sum (Csource B Lrad Cr ξ saving εsum : ℝ)
    (hB : 0 ≤ B) (hLrad : 0 ≤ Lrad) (hCr : 0 < Cr) (hξ : 0 < ξ) (hεsum : 0 < εsum) :
    ∃ SΦ : Finset (ℕ×ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (s : Input ι) (R seed : Ideal O), Squarefree seed → seed ≠ 0 →
      s.W₁ 0 = 0 → s.W₂ 0 = 0 → 0 < sourceRadius s → sourceRadius s ≤ Z^B →
      sourceRadius s ≤ Csource*volume s.toData → volume s.toData ≤ Z^B →
    ∀ (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ → (∀ x,‖s.W₁ x‖ ≤ B₁) → (∀ x,‖s.W₂ x‖ ≤ B₂) →
    ∀ Kfirst : ℝ, 0 < Kfirst →
    ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
      (∀ p E,radius p E ≤ Cr*Z^Lrad) →
    let q := firstSourceOuterLabel s R seed Kfirst radius
    ∀ (labels : Finset (FirstSourceOuterIndex s R seed Kfirst radius)) (left : Bool)
      (p : ℝ) (Φ : 𝓢(ℝ,ℂ)),
      (∀ i ∈ labels, ((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^p) →
    let domain := firstSideSourceLabels labels q (fun _ => sourceRadius s) left
    ∀ (η : ((i : FirstSourceOuterIndex s R seed Kfirst radius) × (q i).SourceIndex) → Character)
      (t K Tsec P : ((i : FirstSourceOuterIndex s R seed Kfirst radius) × (q i).SourceIndex) → ℝ),
      (∀ k ∈ domain, 0 < K k ∧ K k ≤ Z^B ∧ 1 ≤ P k ∧ Tsec k ≤ Z^B ∧
        (sourceRadius s/(((q k.1).sideCommon left).absNorm : ℝ))^2/K k ≤ Tsec k) →
      (∑ k ∈ domain,
        ‖secondDiscardedEnergy (η k) (t k)
          (commonSecondColumns (original s R seed) ((q k.1).sideCommon left)
            ((q k.1).sideCommon_supported left))
          (commonSecondBeta (original s R seed) ((q k.1).sideCommon left) k.2.1.val)
          Φ (K k) (Tsec k) Z ξ‖/(volume s.toData*P k)) ≤
      (Cbound*(originalAbsoluteProfile s B₁ B₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        Z^(p+εsum-saving)/(seed.absNorm : ℝ) := by
  obtain ⟨SΦ,Ctail,hCtail,htail⟩ := actual_common_source_tail_normalized (ι := ι) Csource B ξ saving hB hξ
  obtain ⟨Csum,hCsum,hsum⟩ := actual_first_source_sector_harmonic_mass B Lrad Cr εsum hB hLrad hCr hεsum
  refine ⟨SΦ,Ctail*Csum,mul_pos hCtail hCsum,?_⟩
  filter_upwards [hsum,htail] with Z hZ hZt
  refine ⟨hZ.1,?_⟩
  intro s R seed hs hs0 hz₁ hz₂ hsource₀ hsource hsourceFactor hVcap B₁ B₂ hB₁ hB₂ hb₁ hb₂
    Kfirst hKfirst radius hr q labels left p Φ hrad domain η t K Tsec P hKP
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  have hmass := hZ.2 ι s R seed hs hs0 hz₁ hz₂ hsource₀ hsource Kfirst hKfirst radius hr labels p hrad
  have hmass' : (∑ k ∈ domain,1/((k.2.1.val).absNorm : ℝ)) ≤ Csum*Z^(p+εsum)/(seed.absNorm : ℝ) := by
    cases left
    · exact hmass.2
    · exact hmass.1
  have hpoint (k) (hk : k ∈ domain) := by
    have hg : k.1 ∈ labels ∧ Squarefree k.2.1.val ∧ k.2.1.val ≠ 0 ∧ ((k.2.1.val).absNorm : ℝ) ≤ Z^B := by
      cases left
      · exact firstRightSourceLabels_gates labels q _ Z B hz.le (fun _ _ => hsource) k hk
      · exact firstLeftSourceLabels_gates labels q _ Z B hz.le (fun _ _ => hsource) k hk
    exact hZt.2 s R seed ((q k.1).sideCommon left) k.2.1.val ((q k.1).sideCommon_supported left)
      hg.2.2.1 B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂ hsource₀ hsourceFactor hVcap hg.2.2.2
      (η k) (t k) Φ (K k) (Tsec k) (P k) (hKP k hk).1 (hKP k hk).2.1
      (hKP k hk).2.2.1 (hKP k hk).2.2.2.1 (hKP k hk).2.2.2.2
  apply (Finset.sum_le_sum hpoint).trans
  rw [show (∑ k ∈ domain,
      (Ctail*(originalAbsoluteProfile s B₁ B₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        Z^(-saving)/((k.2.1.val).absNorm : ℝ)) =
      (Ctail*(originalAbsoluteProfile s B₁ B₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        Z^(-saving)*(∑ k ∈ domain,1/((k.2.1.val).absNorm : ℝ)) by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro k hk;ring]
  apply (mul_le_mul_of_nonneg_left hmass' (by positivity)).trans_eq
  simp only [Real.rpow_add hz,Real.rpow_sub hz,Real.rpow_neg hz.le]
  ring

#print axioms actual_first_coherent_source_tail_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentSourceTailSum -/
