/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.affine_local_20261013.Bundles.B034
import Submissions.affine_local_20261013.Bundles.B040
import Submissions.affine_local_20261013.Bundles.B047
import Submissions.affine_local_20261013.Bundles.B050
import Submissions.affine_local_20261013.Bundles.B065
import Submissions.affine_local_20261013.Bundles.B067
import Submissions.affine_local_20261013.Bundles.B071
import Submissions.affine_local_20261013.Bundles.B075
import Submissions.affine_local_20261013.Bundles.B081
import Submissions.affine_local_20261013.Bundles.B082
import Submissions.affine_local_20261013.Bundles.B083
import Submissions.affine_local_20261013.Bundles.B085
import Submissions.affine_local_20261013.Bundles.B087
import Submissions.affine_local_20261013.Bundles.B089
import Submissions.affine_local_20261013.Bundles.B092
import Submissions.affine_local_20261013.Bundles.B094
import Submissions.affine_local_20261013.Bundles.B096
import Submissions.affine_local_20261013.Bundles.B099
import Submissions.affine_local_20261013.Bundles.B102
import Submissions.affine_local_20261013.Bundles.B104
import Submissions.affine_local_20261013.Bundles.B105
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass

/- BEGIN ORIGINAL MODULE Analytic.JointFirstRawErrors ; sha256 6e9759eb196d39c09f075aa38b54da9cc28de0e20652732d47c4fb23338c981b -/
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
local instance actualFirstRawErrorsDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance actualFirstRawErrorsFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem actual_first_independent_raw_errors
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
    Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ))≤37/10000 →
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
    ∀ (qref : FirstJointLabel Aorig) (A δref δrad : ℝ),
    qref.parent = src.η → volume src = Z^A → p ≤ qref.radicalWidth Z+δrad →
    (∀ i ∈ labels, (q i).activeWidth Z+(q i).punctureWidth Z+(q i).leftAllowance Z-2*(q i).leftWidth Z ≤
      qref.activeWidth Z+qref.punctureWidth Z+qref.leftAllowance Z-2*qref.leftWidth Z+δref) →
    (∀ i ∈ labels, (q i).activeWidth Z+(q i).punctureWidth Z+(q i).rightAllowance Z-2*(q i).rightWidth Z ≤
      qref.activeWidth Z+qref.punctureWidth Z+qref.rightAllowance Z-2*qref.rightWidth Z+δref) →
    volume src*(∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
      (left k).value N (q k.1).D R k.2.1.val (q k.1).E
        ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve) ≤
      (volume src/(qref.C.absNorm : ℝ))*qref.parentCost*
        (Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2)*
        Z^(qref.leftTargetWidth Z A-1/2500+εouter+δref+δrad)/(seedOuter.absNorm : ℝ) ∧
    volume src*(∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
      (right k).value N (q k.1).C R k.2.1.val
        (swapSubset (q k.1).C (q k.1).D (q k.1).E)
        ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve) ≤
      (volume src/(qref.D.absNorm : ℝ))*qref.parentCost*
        (Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2)*
        Z^(qref.rightTargetWidth Z A-1/2500+εouter+δref+δrad)/(seedOuter.absNorm : ℝ) := by
  obtain ⟨Uprofile,Jheight,hactual⟩ := actual_first_independent_extracted_errors (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ Sbad hbad sigma cost hsigma hξsmall hcost hsigma_eq
    Avol Dscale Pmask qmoving εgeo hεgeo hbudget εalloc hεalloc hloss hsaving
    Bfirst Lfirst Crfirst hBfirst hLfirst hCrfirst hallocSmall qParent εconductor hεconductor
    hcostSource hconductorBudget εouter hεouter hseedBudget
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hactualZ] with Z hZ
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
  intro labels p hrad left right hleft hright qref A δref δrad hqparent hvolume hprad
    hleftWidth hrightWidth
  have he := hZ.2 Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max hParent
    R seedOuter hR hseedOuter hseedOuter0 hzero1 hzero2 hvolumeCap hmaskCap hHsource hHcap
    profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ K delta reserve asource hK hasource hdelta hreserve haSource
    hP Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
    Mgeom Mvolume heightCap hgeom hheightCap hplainX₁ hplainX₂ hplainY₁ hplainY₂
    hwidth hvolGeom hvolCap hfixed hdef hpaid hfrequency hepsSmall radius hr
    labels p hrad left right hleft hright
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  have hvol := volume_pos src
  let F := Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hpow : Z^(p-1/2500+εouter) ≤ Z^(qref.radicalWidth Z+δrad-1/2500+εouter) :=
    Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith)
  have hcommon (k : (i : FirstSourceOuterIndex src R seedOuter K radius) × (q i).SourceIndex)
      (hi : k.1 ∈ labels) := ((q k.1).sourceChild k.2).error_reference_combined_sector_cap qref Z A δref hZ.1
        (show ((q k.1).sourceChild k.2).parent = qref.parent from hqparent.symm)
        (hleftWidth k.1 hi) (hrightWidth k.1 hi)
  constructor
  · have hsum : (∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
        (left k).value N (q k.1).D R k.2.1.val (q k.1).E
          ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve) ≤
        (qref.leftErrorReference Z A*Z^δref)*(F*Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ)) := by
      calc
        _ ≤ ∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
            (qref.leftErrorReference Z A*Z^δref)*
              (left k).normalizedValue N (q k.1).D R k.2.1.val (q k.1).E
          ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve := by
          apply Finset.sum_le_sum
          intro k hk
          have hi := (firstLeftSourceLabels_gates labels q (fun _ => sourceRadius src)
            Z Bfirst hz.le (fun _ _ => hHcap) k hk).1
          have hn := (left k).normalizedValue_nonneg N (q k.1).D R k.2.1.val (q k.1).E
            ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve hz
          have hid := (left k).value_eq_normalized_reference N (q k.1).D R k.2.1.val (q k.1).E
            ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve hz (q k.1).hC.1
          rw [hvolume] at hid
          exact hid.le.trans (mul_le_mul_of_nonneg_right (hcommon k hi).1 hn)
        _ = (qref.leftErrorReference Z A*Z^δref)*
            (∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
              (left k).normalizedValue N (q k.1).D R k.2.1.val (q k.1).E
          ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left he.1
          (mul_nonneg (qref.error_reference_pos Z A hz).1.le (Real.rpow_nonneg hz.le _))
    have hstep := mul_le_mul_of_nonneg_left hsum hvol.le
    have href := (qref.error_reference_pos Z A hz).1
    calc
      _ ≤ volume src*((qref.leftErrorReference Z A*Z^δref)*
          (F*Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ))) := hstep
      _ ≤ volume src*((qref.leftErrorReference Z A*Z^δref)*
          (F*Z^(qref.radicalWidth Z+δrad-1/2500+εouter)/(seedOuter.absNorm : ℝ))) := by
        gcongr
      _ = (Z^A*qref.leftErrorReference Z A*Z^(qref.radicalWidth Z))*F*
          Z^(-1/2500+εouter+δref+δrad)/(seedOuter.absNorm : ℝ) := by
        rw [hvolume]
        have hp : qref.radicalWidth Z+δrad-1/2500+εouter =
            qref.radicalWidth Z+(-1/2500+εouter+δrad) := by ring
        rw [hp]
        simp only [Real.rpow_add hz]
        ring
      _ = _ := by
        rw [(qref.raw_error_reference_target Z A hZ.1).1,hvolume]
        rw [show qref.leftTargetWidth Z A-1/2500+εouter+δref+δrad =
          qref.leftTargetWidth Z A+(-1/2500+εouter+δref+δrad) by ring]
        simp only [Real.rpow_add hz]
        dsimp [F]
        ring
  · have hsum : (∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
        (right k).value N (q k.1).C R k.2.1.val (swapSubset (q k.1).C (q k.1).D (q k.1).E)
          ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve) ≤
        (qref.rightErrorReference Z A*Z^δref)*(F*Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ)) := by
      calc
        _ ≤ ∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
            (qref.rightErrorReference Z A*Z^δref)*
              (right k).normalizedValue N (q k.1).C R k.2.1.val (swapSubset (q k.1).C (q k.1).D (q k.1).E)
          ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve := by
          apply Finset.sum_le_sum
          intro k hk
          have hi := (firstRightSourceLabels_gates labels q (fun _ => sourceRadius src)
            Z Bfirst hz.le (fun _ _ => hHcap) k hk).1
          have hn := (right k).normalizedValue_nonneg N (q k.1).C R k.2.1.val (swapSubset (q k.1).C (q k.1).D (q k.1).E)
            ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve hz
          have hid := (right k).value_eq_normalized_reference N (q k.1).C R k.2.1.val (swapSubset (q k.1).C (q k.1).D (q k.1).E)
            ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve hz (q k.1).hD.1
          rw [hvolume] at hid
          exact hid.le.trans (mul_le_mul_of_nonneg_right (hcommon k hi).2 hn)
        _ = (qref.rightErrorReference Z A*Z^δref)*
            (∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
              (right k).normalizedValue N (q k.1).C R k.2.1.val (swapSubset (q k.1).C (q k.1).D (q k.1).E)
          ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left he.2
          (mul_nonneg (qref.error_reference_pos Z A hz).2.le (Real.rpow_nonneg hz.le _))
    have hstep := mul_le_mul_of_nonneg_left hsum hvol.le
    have href := (qref.error_reference_pos Z A hz).2
    calc
      _ ≤ volume src*((qref.rightErrorReference Z A*Z^δref)*
          (F*Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ))) := hstep
      _ ≤ volume src*((qref.rightErrorReference Z A*Z^δref)*
          (F*Z^(qref.radicalWidth Z+δrad-1/2500+εouter)/(seedOuter.absNorm : ℝ))) := by
        gcongr
      _ = (Z^A*qref.rightErrorReference Z A*Z^(qref.radicalWidth Z))*F*
          Z^(-1/2500+εouter+δref+δrad)/(seedOuter.absNorm : ℝ) := by
        rw [hvolume]
        have hp : qref.radicalWidth Z+δrad-1/2500+εouter =
            qref.radicalWidth Z+(-1/2500+εouter+δrad) := by ring
        rw [hp]
        simp only [Real.rpow_add hz]
        ring
      _ = _ := by
        rw [(qref.raw_error_reference_target Z A hZ.1).2,hvolume]
        rw [show qref.rightTargetWidth Z A-1/2500+εouter+δref+δrad =
          qref.rightTargetWidth Z A+(-1/2500+εouter+δref+δrad) by ring]
        simp only [Real.rpow_add hz]
        dsimp [F]
        ring

#print axioms actual_first_independent_raw_errors
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstRawErrors -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstSecondMajorant ; sha256 811d1d75bccdd656db50d11d21bb91b789ca3cde0dc9b6915654208f69ed727f -/
section


/-! A direct majorant for the literal first-domain sum of coherent second
physical blocks. All first and second arithmetic labels are kept in one
finite packet domain; only unit phases are discarded. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentCanonicalFirst CenteredMomentSecondPhysicalBlock
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualFirstSecondSource
variable (src : Input ι) (R seed : Ideal O) (Kfirst : ℝ)
  (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
  (side : Bool) (K Radius H : First src R seed Kfirst radius → ℝ)

def packets (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (rows : (k : First src R seed Kfirst radius) → Blocks src R seed Kfirst radius side K Radius H k → Finset O) :
    Finset (Packet src R seed Kfirst radius side K Radius H) :=
  (firstSideSourceLabels labels (firstSourceOuterLabel src R seed Kfirst radius)
    (fun _ => sourceRadius src) side).sigma fun k => Finset.univ.sigma (rows k)

theorem sum_packets {A : Type*} [AddCommMonoid A]
    (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (rows : (k : First src R seed Kfirst radius) → Blocks src R seed Kfirst radius side K Radius H k → Finset O)
    (f : Packet src R seed Kfirst radius side K Radius H → A) :
    (∑ x ∈ packets src R seed Kfirst radius side K Radius H labels rows,f x) =
      ∑ k ∈ firstSideSourceLabels labels (firstSourceOuterLabel src R seed Kfirst radius)
        (fun _ => sourceRadius src) side,
        ∑ b : Blocks src R seed Kfirst radius side K Radius H k, ∑ z ∈ rows k b,f ⟨k,b,z⟩ := by
  simp only [packets,Finset.sum_sigma]

def parent (k : First src R seed Kfirst radius) : Character :=
  let q := (firstSourceOuterLabel src R seed Kfirst radius k.1).sourceChild k.2
  if side then q.pair.left else q.pair.right

variable {src R seed Kfirst radius side K Radius H}

theorem row_parent (x : Packet src R seed Kfirst radius side K Radius H) :
    ((row x).firstPresentation src.η x.1.2.2.1 x.1.2.2.2⁻¹).sourceParent =
      parent src R seed Kfirst radius side x.1 := by rfl

def packetLabel (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (x : Packet src R seed Kfirst radius side K Radius H) : CommonSecondKernelLabel ι :=
  (row x).kernelLabel src R seed src.η x.1.2.2.1 x.1.2.2.2⁻¹ 1 1 1
    ((row x).seed_dvd_first src R seed hs hz₁ hz₂)

def packetValue (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (V P : ℝ) (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
    (x : Packet src R seed Kfirst radius side K Radius H) : ℝ :=
  ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ∑ D ∈ (packetLabel hs hz₁ hz₂ x).physicalProjectors,
    ‖((packetLabel hs hz₁ hz₂ x).withRays χ ξ).physicalRowTerm V P (t x.1) x.2.2 W
      (K x.1) (Radius x.1) (fun j => (x.2.1.2 j : ℤ)) D‖

theorem packetValue_nonneg (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (V P : ℝ) (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
    (x : Packet src R seed Kfirst radius side K Radius H) : 0 ≤ packetValue hs hz₁ hz₂ V P t W x := by
  unfold packetValue
  positivity

theorem block_majorant (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (V P : ℝ) (hV : 0< V) (hP : 0< P)
    (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
    (k : First src R seed Kfirst radius) (b : Blocks src R seed Kfirst radius side K Radius H k)
    (rows : Finset O) (hrows : ∀ z∈rows,z≠0) (hK : 0< K k) :
    ‖activePhysicalRows (parent src R seed Kfirst radius side k) (t k)
      (columns src R seed Kfirst radius side k) (beta src R seed Kfirst radius side k)
      W (K k) (Radius k) (H k) b rows‖/(V*P) ≤
      ∑ z∈rows,packetValue hs hz₁ hz₂ V P t W ⟨k,b,z⟩ := by
  let s := packetLabel hs hz₁ hz₂ (⟨k,b,0⟩ : Packet src R seed Kfirst radius side K Radius H)
  have hh := s.physicalBlock_bin_majorant (κ := Unit) (t k) (Radius k) rows (fun _ => ())
    hrows W (K k) hK (fun j => (b.2 j : ℤ)) V P hV hP
  simp only [Fintype.sum_unique,Finset.filter_true] at hh
  apply hh.trans_eq
  simp_rw [Finset.sum_comm (s := s.physicalProjectors) (t := Finset.univ)]
  simp_rw [Finset.sum_comm (s := s.physicalProjectors) (t := rows)]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := rows)]
  rfl

/-- The actual supported first source domain, including both first rays,
is majorized by one finite joint packet sum. No first-label count is taken. -/
theorem first_domain_majorant (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (V P : ℝ) (hV : 0< V) (hP : 0< P)
    (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
    (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (rows : (k : First src R seed Kfirst radius) → Blocks src R seed Kfirst radius side K Radius H k → Finset O)
    (hK : ∀ k∈firstSideSourceLabels labels (firstSourceOuterLabel src R seed Kfirst radius)
      (fun _ => sourceRadius src) side,0< K k)
    (hrows : ∀ k∈firstSideSourceLabels labels (firstSourceOuterLabel src R seed Kfirst radius)
      (fun _ => sourceRadius src) side,∀ b z,z∈rows k b → z≠0) :
    (∑ k∈firstSideSourceLabels labels (firstSourceOuterLabel src R seed Kfirst radius)
      (fun _ => sourceRadius src) side,
      ‖actualSecondRowBlocks (parent src R seed Kfirst radius side k) (t k)
        (columns src R seed Kfirst radius side k) (beta src R seed Kfirst radius side k)
        W (K k) (Radius k) (H k) (rows k)‖/(V*P)) ≤
      ∑ x∈packets src R seed Kfirst radius side K Radius H labels rows,
        packetValue hs hz₁ hz₂ V P t W x := by
  rw [sum_packets]
  apply Finset.sum_le_sum
  intro k hk
  apply (div_le_div_of_nonneg_right
    (actualSecondRowBlocks_norm_le (parent src R seed Kfirst radius side k) (t k)
      (columns src R seed Kfirst radius side k) (beta src R seed Kfirst radius side k)
      W (K k) (Radius k) (H k) (rows k)) (mul_pos hV hP).le).trans
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun b _ => block_majorant hs hz₁ hz₂ V P hV hP t W k b
    (rows k b) (hrows k hk b) (hK k hk))

end ActualFirstSecondSource
#print axioms ActualFirstSecondSource.block_majorant
#print axioms ActualFirstSecondSource.first_domain_majorant
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstSecondMajorant -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSelectedSeededAggregate ; sha256 ff2c28997daa747c3dacedc6549f7ea0c487eb7cd08951da374b025b1f0b3396 -/
section



























/-! The genuine low source endpoint bounds the coherent shared-bin part of
all actual second physical blocks. Both lower dyads follow from original
profile support, and all projectors are summed with their harmonic weights. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeDetectorZeros HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot ConcretePrimeRowBridge LocalMoment LocalMomentSourceAudit
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyPaidBands
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
open CenteredMomentEnergyCapacityRemoval
open CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentAllocatedRayDictionary
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedChildren
open CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedZero
open CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentAllocatedNaturalSource
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance selectedLowSeededAggregateFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

open CenteredMomentOriginalCommonHarmonic
open CanonicalQuadraticSieve CenteredMomentSourceLiveColumn
open CenteredMomentCommonRadialSource CenteredMomentSourceProfileMass CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialCost CenteredMomentCommonLinearNormalization

open ActualEisensteinCubic RayFourExpansion CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentEnergyChildState
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit CenteredMomentExceptionalAmplitudePair

open CenteredMomentActiveSource CenteredMomentCompleteCommon CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate
open CenteredMomentSecondBlockHarmonicMass
theorem actual_selected_common_low_bin_bound
    (W : ℝ → ℂ) (aslot bslot a b Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hL : 0 ≤ L) (hεmoment : 0 < εmoment)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Rwidth d τ εslot e κ ηheight loss : ℝ)
    (hRw : 0 < Rwidth) (hd : 0 < d) (hτ : 0 < τ) (hεslot : 0 < εslot)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ ηheight)
    (hbudget : 8*e*Rwidth+κ ≤ εslot)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hmeshInc : mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εmoment)
    (hmeshWidth : mesh ≤ d*Rwidth)
    (hmeshLoss : εmoment+(67/100)*mesh+2*d*εslot*(Fintype.card α) ≤ loss)
    (Mslot εmask : ℝ) (hMslot : 0 ≤ Mslot) (hεmask : 0 < εmask)
    (loInput hiInput : α → ℝ) (Bcommon δcommon : ℝ) (hBcommon : 0 ≤ Bcommon) (hδcommon : 0 < δcommon)
    (ηfirst : Character) (parentLoss : ℝ) (hparentLoss : 0 < parentLoss)
    (ξconductor : ℝ) (hξconductor : 0 < ξconductor) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
    ∀ (Wkernel : 𝓢(ℝ,ℂ)) (ν tailRows tailV lower tailSaving upper bplain₁ bplain₂ BRmask : ℝ)
      (Sbad : Finset (Ideal O)) (primeLoss Bsource Lrad Cr εsum : ℝ),
      0 < ν → 0 ≤ tailRows → 0 < primeLoss → 0 ≤ Bsource → Bsource ≤ Bcommon →
      0 ≤ Lrad → 0 < Cr → 0 < εsum → Lrad+1 ≤ tailRows →
    ∃ (Nkernel : ℕ) (Ckernel Csum : ℝ), 0 ≤ Ckernel ∧ 0 < Csum ∧
    ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      ∀ hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)},
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) → (∀ i,lo ≤ σ i) → (∀ i,σ i ≤ hi) →
      0 ≤ height → (∀ i,|freq i| ≤ height) →
      ∀ (p : Profiles a b) (src : Input α), Matches M H hH src η₀ θ w σ freq W bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      p.profile 0 = src.W₁ → p.profile 1 = src.W₂ →
      (∀ i,src.lo i = loInput i) → (∀ i,src.hi i = hiInput i) →
      src.X₁ ≤ Z^L → src.X₂ ≤ Z^L → src.Y₁ ≤ Z^L → src.Y₂ ≤ Z^L →
      ∀ (P₁ Q₁ : Ideal O) (hP₁ : Supported P₁),
      ∀ (C₁ D₁ Rmask seed Lfirst : Ideal O) (hC₁ : Supported C₁) (hD₁ : D₁ ≠ 0)
        (E₁ : Finset (CommonIndex P₁ Q₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂) (left : Bool),
      Rmask ≠ 0 → Squarefree Lfirst → ∀ hseed : seed ∣ C₁,
      ∀ (t Hsource A volumeLoss Mparent g omegaLoss ξ sourceLoss profileLoss clip : ℝ),
      0 < Hsource → sourceRadius src ≤ Hsource → Real.logb Z Hsource ≤ A+sourceLoss →
      A+(7/2)*(∑ i,w i) ≤ Mparent+g → Real.logb Z (volume src.toData) ≤ A →
      A-volumeLoss ≤ Real.logb Z (volume src.toData) →
      (Fintype.card α : ℝ)*Real.logb Z (max 1 src.upper) ≤ profileLoss →
      0 ≤ g → g ≤ 37/10000 → 0 ≤ omegaLoss → 0 ≤ profileLoss → 0 ≤ clip →
      Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      let c := Real.logb Z (C₁.absNorm : ℝ)
      let d₁ := Real.logb Z (D₁.absNorm : ℝ)
      let r₁ := Real.logb Z (normValue (activeConductor P₁ Q₁))
      let e₁ := Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex P₁ Q₁ => P.val) E₁))
      let Kmain := Z^(2*A-c-d₁+r₁+e₁-Mparent+max (d₁-c) 0+6*(3/500)+omegaLoss)
      let Radius := frequencyRadius (jointSecondNominal C₁ Hsource Z A c d₁ r₁ e₁ Mparent (3/500) omegaLoss) Z ξ
      let pad := 2*sourceLoss+parentLoss+ξ/2+Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))
      0 ≤ pad → pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 401/9000000 →
      Mparent+pad ≤ Mcap → Mparent+pad+Bmask+ξconductor ≤ d → A+sourceLoss ≤ Bcommon →
      lower ≤ δcommon+(Mparent-max (c-d₁) 0-6*(3/500)-omegaLoss-Bsource)+(3/500)-401/9000000 →
      sourceRadius src/(C₁.absNorm : ℝ) ≤ Z^Bsource → Hsource/(C₁.absNorm : ℝ) ≤ Z^Bsource →
      Radius ≤ Cr*Z^Lrad →
      let columns := commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁
      let β := commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst
      let parent := firstSideCharacter F left
      let first : FirstSidePresentation ηfirst := ⟨P₁,Q₁,hP₁,E₁,ξ₁,ξ₂,F,left⟩
      let labels := fun q : ActiveBlocks columns β Kmain Radius (Hsource/(C₁.absNorm : ℝ)) =>
        actualCommonBlockKernelLabel src Rmask seed C₁ Lfirst hC₁ hseed parent Kmain Radius (Hsource/(C₁.absNorm : ℝ)) q 1 1 1
      ∀ (I : ℕ) (bin : HeckeInverseAmplification.NonzeroElement → Option (Fin (I+1) × Fin (I+1))),
      (∀ w,bin w = none ↔ CenteredExceptionalProfile.FixedInducingRow ηfirst (internalQ Q η₀) fixedBadMask 1 w.val) →
      (∀ w bidx,bin w = some bidx →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (fun _ => 1) (fun _ => one_ne_zero)
          (51/100+(e/2)*(bidx.2.val : ℝ)) (51/100+(e/2)*(bidx.2.val : ℝ)+e)
          (3*(bidx.1.val+1 : ℕ)*Z^τ) w) →
      ∀ bidx : Fin (I+1) × Fin (I+1),
      let abin := 51/100+(e/2)*(bidx.2.val : ℝ)
      let k := bidx.1.val
      abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ θ u v : ℝ, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → ‖v‖ ≤ Z^ν → ∀ i,
        |(t+2*Real.pi*(u-θ))+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ ∧
        |(t+2*Real.pi*(v-(-θ)))+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ (vBound B₁ B₂ : ℝ), 0 ≤ vBound → 0 ≤ B₁ → 0 ≤ B₂ →
      let aSource := (∏ i,loInput i)*a*a
      (∀ θ u v : ℝ, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → ‖v‖ ≤ Z^ν →
        |t+2*Real.pi*(u-θ)| ≤ vBound ∧ |t+2*Real.pi*(v-(-θ))| ≤ vBound) →
      src.W₁ 0 = 0 → src.W₂ 0 = 0 →
      (∀ x,‖src.W₁ x‖ ≤ B₁) → (∀ x,‖src.W₂ x‖ ≤ B₂) → A ≤ tailV →
      src.upper ≤ upper → src.b₁ ≤ bplain₁ → src.b₂ ≤ bplain₂ →
      (Rmask.absNorm : ℝ) ≤ Z^BRmask → vBound ≤ (1+4*Real.pi)*Z^ν → height ≤ Z^ν →
      let smallLoss := (BRmask+Bcommon)*εmask+ν*(degree : ℝ)
      Bsource ≤ tailSaving+smallLoss →
      let Elow := lowFixedCoefficient (ι := α) Cbound Mslot upper bplain₁ bplain₂ p S degree
      let Eabs := 2*128^(Fintype.card α+2)*Mslot^Fintype.card α*B₁*B₂*
        (max 1 upper)^Fintype.card α*max 1 bplain₁*max 1 bplain₂
      ‖actualSecondRowBlocks parent t columns β Wkernel Kmain Radius (Hsource/(C₁.absNorm : ℝ))
        (fun q => (CenteredMomentSecondEnergySplit.sourceRows q.1.1.val.1 q.1.1.val.2 q.1.2 Radius).filter
          (fun z => first.sourceBin (labels q) bin z = some bidx))‖ /
          (volume src.toData*actualHighPrimeCount M H Sbad Z) ≤
        (Csum*(Ckernel*Elow/aSource+Ckernel*(128/aSource)*Eabs^2)/(Lfirst.absNorm : ℝ))*
          Z^(A-2*c+r₁+e₁+δcommon-401/9000000+smallLoss+primeLoss+εsum+volumeLoss) := by
  obtain ⟨degree,S,hphysical⟩ := actual_selected_second_low_physical_kernel_of_common_bin M H hH W
    aslot bslot a b Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon ηfirst parentLoss hparentLoss ξconductor hξconductor
  refine ⟨degree,S,?_⟩
  intro Wkernel ν tailRows tailV lower tailSaving upper bplain₁ bplain₂ BRmask Sbad primeLoss Bsource Lrad Cr εsum
    hν htailRows hprimeLoss hBsource hBcommonSource hLrad hCr hεsum htailRowsCap
  obtain ⟨Nkernel,Ckernel,hCkernel,hphysical⟩ := hphysical Wkernel 0 ν tailRows tailV lower tailSaving
    upper bplain₁ bplain₂ BRmask Sbad primeLoss hν htailRows hprimeLoss
  obtain ⟨Csum,hCsum,hsum⟩ := actual_seeded_second_low_rows Bsource Bsource Lrad Cr εsum
    hBsource hBsource hLrad hCr hεsum le_rfl
  refine ⟨Nkernel,Ckernel,Csum,hCkernel,hCsum,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hphysical⟩ := hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hphysical,hsum,eventually_actual_high_prime_ratio M H hH Sbad primeLoss hprimeLoss,
    eventually_source_block_row_power Lrad Cr tailRows hLrad hCr htailRowsCap] with Z hphysical hsum hprime hrowcap
  intro hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ Rmask seed Lfirst hC₁ hD₁ E₁ ξ₁ ξ₂ F left hR hLfirst hseed
    t Hsource A volumeLoss Mparent g omegaLoss ξ sourceLoss profileLoss clip hHsource hsourceH hsource hcapacity hvolume hvolumeLower hprofile
    hg hgCap homega hprofile0 hclip hclipCost c d₁ r₁ e₁ Kmain Radius pad hpad hbudgetSource
    hMparentCap hMparentConductor hcommonBudget htargetLower
    hsourceB hHcap hRadius columns β parent first labels I bin hbinNone hbins bidx abin k habinTop hbaseScale hT
    hfreqGate hheightSource vBound B₁ B₂ hvBound hB₁ hB₂ aSource hvCube hz₁ hz₂ hW₁ hW₂ hAtail
    hupper hbplain₁ hbplain₂ hRN hvSmall hhSmall smallLoss htailSaving Elow Eabs
  let rows := fun q : ActiveBlocks columns β Kmain Radius (Hsource/(C₁.absNorm : ℝ)) =>
    ((CenteredMomentSecondEnergySplit.sourceRows q.1.1.val.1 q.1.1.val.2 q.1.2 Radius).filter
      (fun z => first.sourceBin (labels q) bin z = some bidx)).filter
        (fun z => normValue z ≤ dyadicScale (q.2 1 : ℤ))
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have haSourceEq : originalLowerProfile src a a = aSource := by
    simp only [originalLowerProfile,hloInput,aSource]
  have haSource : 0 < aSource := haSourceEq ▸ originalLowerProfile_pos src a a ha ha
  have hKmain : 0 < Kmain := Real.rpow_pos_of_pos hZ0 _
  have hRadius0 : 0 ≤ Radius := by
    dsimp only [Radius,frequencyRadius,jointSecondNominal,jointSecondBall]
    positivity
  have hSourceUpper : sourceRadius src ≤ Z^Bcommon := hsourceH.trans (by
    calc
      Hsource = Z^(Real.logb Z Hsource) := (Real.rpow_logb hZ0 hZ.ne' hHsource).symm
      _ ≤ Z^Bcommon := Real.rpow_le_rpow_of_exponent_le hZ.le (hsource.trans hcommonBudget))
  have hElow : 0 ≤ Elow := low_fixed_coefficient_nonneg Cbound Mslot upper bplain₁ bplain₂ p S degree hCbound.le
  have hEabs : 0 ≤ Eabs := by dsimp [Eabs]; positivity
  have hnorm : ∀ J ∈ columns,β J ≠ 0 → (J.absNorm : ℝ) ≤ Z^Bsource := by
    intro J hJ hβ
    exact (commonSecond_source_norm_cap (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst hC₁ (sourceRadius src)
      (fun J _ hJ => (CenteredMomentOriginalCommonHarmonic.original_column_norm src Rmask seed J hz₁ hz₂ hJ).2) J hJ hβ).trans hsourceB
  have habin : 51/100 ≤ abin := by
    dsimp [abin]
    exact le_add_of_nonneg_right (by positivity)
  have hrows : ∀ q,∀ z ∈ rows q,z ≠ 0 := by
    intro q z hz
    exact CenteredMomentSecondEnergySplit.sourceRows_nonzero _ _ _ _ _
      (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
  suffices hsector :
      ‖actualSecondRowBlocks parent t columns β Wkernel Kmain Radius (Hsource/(C₁.absNorm : ℝ))
        (fun q => (CenteredMomentSecondEnergySplit.sourceRows q.1.1.val.1 q.1.1.val.2 q.1.2 Radius).filter
          (fun z => first.sourceBin (labels q) bin z = some bidx))‖ /
        (Z^(A-c)*actualHighPrimeCount M H Sbad Z) ≤
      (Csum*(Ckernel*Elow/aSource+Ckernel*(128/aSource)*Eabs^2)/(Lfirst.absNorm : ℝ))*
        Z^(A-c+r₁+e₁+δcommon-401/9000000+smallLoss+primeLoss+εsum) by
    have hv : Z^(A-volumeLoss) ≤ volume src.toData := by
      calc
        _ ≤ Z^(Real.logb Z (volume src.toData)) :=
          Real.rpow_le_rpow_of_exponent_le hZ.le hvolumeLower
        _ = _ := Real.rpow_logb hZ0 hZ.ne' (CenteredMomentExceptionalAmplitudePair.volume_pos src.toData)
    have hnormal := low_sector_to_original_volume _ (volume src.toData)
      (actualHighPrimeCount M H Sbad Z)
      (Csum*(Ckernel*Elow/aSource+Ckernel*(128/aSource)*Eabs^2)/(Lfirst.absNorm : ℝ)) Z A c
      (A-c+r₁+e₁+δcommon-401/9000000+smallLoss+primeLoss+εsum) volumeLoss
      hZ hprime.2.1 (by positivity) hv hsector
    exact hnormal.trans_eq (by congr 2; ring)
  rw [actualSecondRowBlocks_eq_dyadic_filter]
  apply hsum.2 src Rmask seed C₁ Lfirst hC₁ hseed hLfirst hz₁ hz₂ hsourceB parent t Wkernel Kmain Radius
    (Hsource/(C₁.absNorm : ℝ)) (Z^(A-c)) (actualHighPrimeCount M H Sbad Z)
    (Ckernel*Elow/aSource) (Ckernel*(128/aSource)*Eabs^2) (tailSaving+smallLoss)
    (A-c+r₁+e₁+δcommon-401/9000000+smallLoss+primeLoss)
    hKmain hRadius hHcap (Real.rpow_pos_of_pos hZ0 _) hprime.2.1 (by positivity) (by positivity)
    htailSaving rows hrows
  intro q hne D hD hμ χL χR
  let C₂ := q.1.1.val.1
  let D₂ := q.1.1.val.2
  let hC₂ := lowActiveLeftSupported q.1.1
  let hD₂ := lowActiveRightSupported q.1.1
  have hCD : primeSupport C₂ = primeSupport D₂ :=
    (CenteredMomentFirstSectors.commonLabels_data _ _ _ _ q.1.1.property).2.2
  obtain ⟨family,hfamily⟩ := exists_exceptional_family parent C₂ D₂ hC₂ hD₂ hCD q.1.2
  have hnominalUpper := joint_low_nominal_le_parent C₂ D₂ hC₂ q.1.2 Z Mparent c d₁
    (3/500) omegaLoss hZ (by norm_num) homega
  let nominal := jointLowNominal Mparent c d₁ (3/500) omegaLoss
    (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
    (Real.logb Z ((∏ P ∈ q.1.2,P.val).absNorm : ℝ))
  have hMcapSource : nominal+pad ≤ Mcap := by dsimp only [nominal]; linarith
  have hconductorSource : nominal+pad+Bmask+ξconductor ≤ d := by dsimp only [nominal]; linarith
  have hcum := actual_common_cumulative_norm src Rmask seed C₁ Lfirst hC₁ hz₁ hz₂ q.1.1
  have hCcap := hcum.1.trans hSourceUpper
  have hDcap := hcum.2.trans hSourceUpper
  have hdyadRows := hrowcap C₂ D₂ hC₂ q.1.2 Kmain Radius (Hsource/(C₁.absNorm : ℝ))
    hZ.le hRadius0 hRadius q.2
  have hsecondCap := commonLabel_norm_bounds columns β (Z^Bsource) hnorm _ _ q.1.1.property
  have hnominalLower := joint_low_nominal_lower_of_common_cap C₂ D₂ hC₂ hD₂ hCD q.1.2
    Z Bsource Mparent c d₁ (3/500) omegaLoss hZ hsecondCap.1
  have htarget : lower ≤ δcommon+nominal+(3/500)-401/9000000 := by
    dsimp only [nominal]
    linarith
  have hphysicalDyads := actual_common_physical_lower_dyads src Rmask seed C₁ Lfirst hC₁.1 a b ha p hp₁ hp₂
    parent t (activeSource columns β) C₂ D₂ hC₂ hD₂ q.1.2 Radius (rows q) Wkernel Kmain
    (fun i => (q.2 i : ℤ)) hne
  rw [haSourceEq] at hphysicalDyads
  obtain ⟨hphysicalL,hphysicalR⟩ := hphysicalDyads
  have hLproj := CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero D hμ
  have hLcap : (D.absNorm : ℝ) ≤ Z^Bcommon :=
    (actualSecondProjectors_norm_cap columns β Kmain Radius (Hsource/(C₁.absNorm : ℝ)) (Z^Bsource)
      hnorm q D hD).trans (Real.rpow_le_rpow_of_exponent_le hZ.le hBcommonSource)
  obtain ⟨_,hphysicalq⟩ := hphysical hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq
    p src hmatch hhi hMs hp₁ hp₂ hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ Rmask seed D Lfirst hC₁ hD₁
    q.1.1 hCD E₁ ξ₁ ξ₂ F
  let low := fun z => first.sourceBin (labels q) bin z = some bidx
  have hbAt (z : O) (hz : z ≠ 0) (hlow : low z) :=
    hbins (first.row (labels q) z hz) bidx (by
      simpa only [low,FirstSidePresentation.sourceBin,dif_pos hz] using hlow)
  have hsupp (z : O) (hz : z ∈ rows q) :
      (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial
        (family χL) (internalQ Q η₀) (fun i => (q.2 i : ℤ))).keep z ∧
      (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial
        (family (χR⁻¹)) (internalQ Q η₀) (fun i => (q.2 i : ℤ))).keep (-z) ∧
      first.sourceBin (labels q) bin z = some bidx ∧
      normValue z ≤ dyadicScale (q.2 1 : ℤ) := by
    obtain ⟨hz,hn⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz,hb⟩ := Finset.mem_filter.mp hz
    have hz0 := CenteredMomentSecondEnergySplit.sourceRows_nonzero _ _ _ _ _ hz
    have hk := canonical_low_keep_pair_of_source_bin first (labels q) rfl bin
      (internalQ Q η₀) hQ72 hbinNone family hfamily z hz0 bidx hb χL (χR⁻¹)
      (fun i => (q.2 i : ℤ))
    exact ⟨hk.1,hk.2,hb,hn⟩
  have hresult := hphysicalq left q.1.2 family hfamily hR hseed hLproj hCcap hDcap hLcap
    t (activeSource columns β) β (rows q) Wkernel Kmain (fun i => (q.2 i : ℤ)) Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss (3/500) clip
    hKmain hHsource hsource hcapacity hvolume hprofile hg hgCap homega (by norm_num) hprofile0 hclip hclipCost
    hpad hMcapSource hconductorSource hbudgetSource rfl hne χL χR low abin k
    (fun _ _ => 1) (fun _ _ => one_ne_zero) habin habinTop hbaseScale hT
    (fun z hz hl => hbAt z (hz.1.1) hl)
    (fun z hz hl => hbAt (-z) (neg_ne_zero.mpr hz.1.1) hl)
    hfreqGate hheightSource (rows q)
    (fun z hz => ⟨(hsupp z hz).1,(hsupp z hz).2.2.1⟩)
    (fun z hz => ⟨(hsupp z hz).2.1,(hsupp z hz).2.2.1⟩)
    (fun z hz => (hsupp z hz).2.2.2)
    vBound B₁ B₂ aSource hvBound hB₁ hB₂ haSource hvCube hz₁ hz₂ hW₁ hW₂ hdyadRows hAtail hphysicalL hphysicalR
    hupper hbplain₁ hbplain₂ hRN hvSmall hhSmall htarget
  simp only [pow_zero,Complex.ofReal_one,one_mul] at hresult
  change secondPrecountFactor (Z^(A-c)) (actualHighPrimeCount M H Sbad Z) C₂ D₂ q.1.2 Kmain
      (fun i => (q.2 i : ℤ))*_ ≤
    Ckernel*((Elow/(aSource*(D.absNorm : ℝ)))*pairWeight C₂ D₂*
      Z^(A-c+r₁+e₁+δcommon+(3/500)-(3/500)-401/9000000+smallLoss+primeLoss)+
      (128/aSource)*Eabs^2*pairWeight C₂ D₂*
      Z^(A-c+r₁+e₁+δcommon+(3/500)-(3/500)-401/9000000-tailSaving+primeLoss)) at hresult
  rw [show A-c+r₁+e₁+δcommon+(3/500)-(3/500)-401/9000000 =
    A-c+r₁+e₁+δcommon-401/9000000 by ring] at hresult
  exact hresult.trans_eq (low_physical_harmonic_form Ckernel Elow aSource (D.absNorm : ℝ)
    (pairWeight C₂ D₂) Eabs Z (A-c+r₁+e₁+δcommon-401/9000000) smallLoss primeLoss tailSaving hZ0)


#print axioms actual_selected_common_low_bin_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSelectedSeededAggregate -/

/- BEGIN ORIGINAL MODULE Global.Final.Geometry ; sha256 ac3b07e15b5ea5177ce051a297131cfc6f82f73a92dcccc443a949698475921b -/
section



namespace Submission20261012.Global.FinalAssembly
open OAI.SevenEighths

theorem weighted_target_identity :
    weightedTarget = signal theta+(HeckeZeroSupremum.beta-theta)/2 := by
  dsimp [weightedTarget,signal]
  ring

theorem weighted_target_lower (hβ : theta ≤ HeckeZeroSupremum.beta) :
    signal theta ≤ weightedTarget := by rw [weighted_target_identity]; linarith

theorem weighted_target_gap :
    HeckeZeroSupremum.beta-(4+b)/6-weightedTarget =
      (HeckeZeroSupremum.beta-theta)/2 := by
  dsimp [weightedTarget,signal]
  ring

theorem weighted_target_saving
    (D : HighParameters.HighData (HeckeZeroSupremum.beta-theta))
    (hβ : theta < HeckeZeroSupremum.beta) :
    D.sigma+D.t/8+D.t/8 ≤ HeckeZeroSupremum.beta-(4+b)/6-weightedTarget := by
  rw [weighted_target_gap]
  linarith [D.high_saving]
end Submission20261012.Global.FinalAssembly
end
/- END ORIGINAL MODULE Global.Final.Geometry -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalNormalized ; sha256 306f42bc774b2fd5c53523d8203395b24eb7fd9cd56970b7049311296cb9a52d -/
section



/-! The original coherent exceptional partEnergy. Source support, actual
inducing rows, all second projectors and the first-projector radical seed
are discharged internally after the transformed exceptional split. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondSectorColumns CenteredMomentActiveSource CenteredMomentFirstSectors
open CenteredMomentMobiusRegroup CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondHeightFamily CenteredMomentReflectedSource
open CenteredMomentSecondPhysicalBlock CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondExceptionalSourceFamily CenteredMomentSecondExceptionalAggregate
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentSecondDyadicRowSupport
open CenteredMomentFiniteProfileExceptional CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
open CenteredMomentRankinRadical CenteredMomentChildRows RayFourExpansion CompletedGauss
local notation "O" => HeckeFamily.O
local instance coherentExceptionalNormalizedDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstMixedAllowance CenteredMomentFirstPhysicalSource
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstScale

theorem actual_common_coherent_exceptional_normalized
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi) (lo hi : ι → ℝ)
    (ε δ θ B Bsource L Cr εmass : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ) (hB : 0 ≤ B) (hBsource : 0 ≤ Bsource)
    (hL : 0 ≤ L) (hCr : 0 < Cr) (hεmass : 0 < εmass) (W : 𝓢(ℝ,ℂ)) :
    ∃ J : ℕ, ∃ Sprofile : Finset (ℕ×ℕ), (0,0) ∈ Sprofile ∧
    ∃ Cbound : ℝ, 0 ≤ Cbound ∧
    ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} →
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (src : Input ι) (profile : Profiles wlo whi),
    (∀ i, src.lo i = lo i) → (∀ i, src.hi i = hi i) → (∀ i, 1 ≤ src.P i) →
    src.W₁ = profile.profile 0 → src.W₂ = profile.profile 1 → sourceRadius src ≤ Z^Bsource →
    ∀ (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁), R ≠ 0 → seed ∣ C₁ →
    Squarefree L₁ → L₁ ≠ 0 →
    ∀ (η : Character) (χ₀ : RayCharacter) (m : O), m ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m →
    ∀ t Kphys Tsec ξ Hsource P M Kfirst omega primeLoss : ℝ, 0 < Kphys → 0 < P →
    frequencyRadius Tsec Z ξ ≤ Cr*Z^L → Hsource ≤ Z^Bsource →
    (expandedFactor η : ℝ)*R.absNorm*(sourceRadius src)^2*(4*frequencyRadius Tsec Z ξ) ≤ Z^B →
    Z^(M/4) ≤ src.X₁ → Z^(M/4) ≤ src.X₂ → Z^(M/4) ≤ src.Y₁ → Z^(M/4) ≤ src.Y₂ →
    ∀ (ηparent : Character) (D₁ E₁ : Ideal O), Supported D₁ →
    primeSupport C₁ = primeSupport D₁ →
    ∀ (U₁ : Finset (CommonIndex C₁ D₁)),
    E₁ = Ideal.span {primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) U₁} →
    η.modulus = ηparent.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) U₁*activeConductor C₁ D₁} →
    0 < Kfirst → 1 ≤ M →
    M ≤ Real.logb Z Kfirst+Real.logb Z (ηparent.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
    Real.logb Z (volume src.toData) ≤ (883/1000)*M →
    1/P ≤ Z^(-(3/500 : ℝ)+primeLoss) →
    Kphys ≤ mainCommonRadius Z (Real.logb Z (D₁.absNorm : ℝ))
      (nominalLog C₁ D₁ E₁ Kfirst (volume src.toData) Z)
      (Real.logb Z (C₁.absNorm : ℝ)) (9/500) omega 0 →
    ‖partEnergy true η χ₀ Q m t (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁) W Kphys Tsec Z ξ Hsource‖/(volume src.toData*P) ≤
    Cbound*coherentExceptionalProfile Sprofile src profile J Q K t*
      (originalLowerProfile src wlo wlo)^(-2/3:ℝ)*
      ((η.modulus.absNorm : ℝ)*(volume src.toData/(C₁.absNorm : ℝ)^2)*Z^(allowance C₁ D₁ Z))*
      Z^(-93/1000+5*omega/6+primeLoss+2*ε+δ+2*Bsource*θ+εmass)/(L₁.absNorm : ℝ) := by
  obtain ⟨J,Sprofile,hSprofile,Cbound,hCbound,hbound⟩ := actual_common_coherent_exceptional_energy
    wlo whi hwlo hwhi lo hi ε δ θ B Bsource L Cr εmass hε hδ hθ hB hBsource hL hCr hεmass W
  refine ⟨J,Sprofile,hSprofile,Cbound,hCbound,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩ := hbound Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro src profile hlo hhi hP hW₁ hW₂ hsource R seed C₁ L₁ hC₁ hR hseed hL₁ hL₁0
    η χ₀ m hm hml hm2 t Kphys Tsec ξ Hsource P M Kfirst omega primeLoss hKphys hPcount
    hRadius hHsource hcond hX₁ hX₂ hY₁ hY₂ ηparent D₁ E₁ hD₁ hCD₁ U₁ hE₁ hmod
    hKfirst hM hwidth hvolume hprime hradius
  have hz := zero_lt_one.trans hZ.1
  have hv := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  have ha := originalLowerProfile_pos src wlo wlo hwlo hwlo
  have hprofile := coherentExceptionalProfile_nonneg Sprofile src profile J Q K t hK.le
  have hb := hZ.2 src profile hlo hhi hP hW₁ hW₂ hsource R seed C₁ L₁ hC₁ hR hseed hL₁ hL₁0
    η χ₀ m hm hml hm2 t Kphys Tsec ξ Hsource P (M/4) hKphys hPcount
    hRadius hHsource hcond hX₁ hX₂ hY₁ hY₂
  have hs := actual_coherent_main_exceptional_scalar ηparent η C₁ D₁ E₁ hC₁ hD₁ hCD₁ U₁ hE₁
    Kfirst (volume src.toData) Z omega M P Kphys primeLoss (2*ε+δ+2*Bsource*θ+εmass)
    hZ.1 hKfirst hv hPcount hKphys.le hmod hM hwidth hvolume hprime hradius
  apply hb.trans
  calc
    _ = (Cbound*coherentExceptionalProfile Sprofile src profile J Q K t*
        (originalLowerProfile src wlo wlo)^(-2/3:ℝ))*
      ((((C₁.absNorm : ℝ)*P)⁻¹*(volume src.toData/(C₁.absNorm : ℝ))^(1/3:ℝ)*Kphys^(5/6:ℝ))*
        Z^((2*ε+δ+2*Bsource*θ+εmass)-2*max (M/4-Real.logb Z (C₁.absNorm : ℝ)) 0/3)) /
      (L₁.absNorm : ℝ) := by ring
    _ ≤ (Cbound*coherentExceptionalProfile Sprofile src profile J Q K t*
        (originalLowerProfile src wlo wlo)^(-2/3:ℝ))*
      (((η.modulus.absNorm : ℝ)*(volume src.toData/(C₁.absNorm : ℝ)^2)*Z^(allowance C₁ D₁ Z))*
        Z^(-93/1000+5*omega/6+primeLoss+(2*ε+δ+2*Bsource*θ+εmass))) /
      (L₁.absNorm : ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity)) (Nat.cast_nonneg _)
    _ = _ := by
      rw [show -93/1000+5*omega/6+primeLoss+(2*ε+δ+2*Bsource*θ+εmass) =
        -93/1000+5*omega/6+primeLoss+2*ε+δ+2*Bsource*θ+εmass by ring]
      ring

#print axioms actual_common_coherent_exceptional_normalized
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalNormalized -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstRawErrorsFull ; sha256 284dafaf746650cca2d45337c5639381254ce729d8639793c7e3eb16f468f631 -/
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
local instance actualFirstRawErrorsDecEqFull {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance actualFirstRawErrorsFiniteFull : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem actual_first_independent_raw_errors_full
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
    ∀θ:α→RayQuotient.Characters M H,
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤(Cycle25.Energy.commonMesh Mcap 0 L εchild)) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤ N → lower≤ src.lower → src.upper≤ upper →
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
    Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ))≤37/10000 →
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
    ∀ (qref : FirstJointLabel α) (A δref δrad : ℝ),
    qref.parent = src.η → volume src = Z^A → p ≤ qref.radicalWidth Z+δrad →
    (∀ i ∈ labels, (q i).activeWidth Z+(q i).punctureWidth Z+(q i).leftAllowance Z-2*(q i).leftWidth Z ≤
      qref.activeWidth Z+qref.punctureWidth Z+qref.leftAllowance Z-2*qref.leftWidth Z+δref) →
    (∀ i ∈ labels, (q i).activeWidth Z+(q i).punctureWidth Z+(q i).rightAllowance Z-2*(q i).rightWidth Z ≤
      qref.activeWidth Z+qref.punctureWidth Z+qref.rightAllowance Z-2*qref.rightWidth Z+δref) →
    volume src*(∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
      (left k).value N (q k.1).D R k.2.1.val (q k.1).E
        ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve) ≤
      (volume src/(qref.C.absNorm : ℝ))*qref.parentCost*
        (Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2)*
        Z^(qref.leftTargetWidth Z A-1/2500+εouter+δref+δrad)/(seedOuter.absNorm : ℝ) ∧
    volume src*(∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
      (right k).value N (q k.1).C R k.2.1.val
        (swapSubset (q k.1).C (q k.1).D (q k.1).E)
        ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve) ≤
      (volume src/(qref.D.absNorm : ℝ))*qref.parentCost*
        (Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2)*
        Z^(qref.rightTargetWidth Z A-1/2500+εouter+δref+δrad)/(seedOuter.absNorm : ℝ) := by
  obtain ⟨Uprofile,Jheight,hactual⟩ := actual_first_independent_extracted_errors_full (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ Sbad hbad sigma cost hsigma hξsmall hcost hsigma_eq
    Avol Dscale Pmask qmoving εgeo hεgeo hbudget εalloc hεalloc hloss hsaving
    Bfirst Lfirst Crfirst hBfirst hLfirst hCrfirst hallocSmall qParent εconductor hεconductor
    hcostSource hconductorBudget εouter hεouter hseedBudget
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hactualZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max hParent
    R seedOuter hR hseedOuter hseedOuter0
    hzero1 hzero2 hvolumeCap hmaskCap hHsource hHcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hP Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
    Mgeom Mvolume heightCap hgeom hheightCap hplainX₁ hplainX₂ hplainY₁ hplainY₂
    hwidth hvolGeom hvolCap hfixed hdef hpaid hfrequency hepsSmall radius hr
  let q := firstSourceOuterLabel src R seedOuter K radius
  intro labels p hrad left right hleft hright qref A δref δrad hqparent hvolume hprad
    hleftWidth hrightWidth
  have he := hZ.2 θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max hParent
    R seedOuter hR hseedOuter hseedOuter0 hzero1 hzero2 hvolumeCap hmaskCap hHsource hHcap
    profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ K delta reserve asource hK hasource hdelta hreserve haSource
    hP Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
    Mgeom Mvolume heightCap hgeom hheightCap hplainX₁ hplainX₂ hplainY₁ hplainY₂
    hwidth hvolGeom hvolCap hfixed hdef hpaid hfrequency hepsSmall radius hr
    labels p hrad left right hleft hright
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  have hvol := volume_pos src
  let F := Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hpow : Z^(p-1/2500+εouter) ≤ Z^(qref.radicalWidth Z+δrad-1/2500+εouter) :=
    Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith)
  have hcommon (k : (i : FirstSourceOuterIndex src R seedOuter K radius) × (q i).SourceIndex)
      (hi : k.1 ∈ labels) := ((q k.1).sourceChild k.2).error_reference_combined_sector_cap qref Z A δref hZ.1
        (show ((q k.1).sourceChild k.2).parent = qref.parent from hqparent.symm)
        (hleftWidth k.1 hi) (hrightWidth k.1 hi)
  constructor
  · have hsum : (∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
        (left k).value N (q k.1).D R k.2.1.val (q k.1).E
          ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve) ≤
        (qref.leftErrorReference Z A*Z^δref)*(F*Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ)) := by
      calc
        _ ≤ ∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
            (qref.leftErrorReference Z A*Z^δref)*
              (left k).normalizedValue N (q k.1).D R k.2.1.val (q k.1).E
          ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve := by
          apply Finset.sum_le_sum
          intro k hk
          have hi := (firstLeftSourceLabels_gates labels q (fun _ => sourceRadius src)
            Z Bfirst hz.le (fun _ _ => hHcap) k hk).1
          have hn := (left k).normalizedValue_nonneg N (q k.1).D R k.2.1.val (q k.1).E
            ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve hz
          have hid := (left k).value_eq_normalized_reference N (q k.1).D R k.2.1.val (q k.1).E
            ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve hz (q k.1).hC.1
          rw [hvolume] at hid
          exact hid.le.trans (mul_le_mul_of_nonneg_right (hcommon k hi).1 hn)
        _ = (qref.leftErrorReference Z A*Z^δref)*
            (∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
              (left k).normalizedValue N (q k.1).D R k.2.1.val (q k.1).E
          ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left he.1
          (mul_nonneg (qref.error_reference_pos Z A hz).1.le (Real.rpow_nonneg hz.le _))
    have hstep := mul_le_mul_of_nonneg_left hsum hvol.le
    have href := (qref.error_reference_pos Z A hz).1
    calc
      _ ≤ volume src*((qref.leftErrorReference Z A*Z^δref)*
          (F*Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ))) := hstep
      _ ≤ volume src*((qref.leftErrorReference Z A*Z^δref)*
          (F*Z^(qref.radicalWidth Z+δrad-1/2500+εouter)/(seedOuter.absNorm : ℝ))) := by
        gcongr
      _ = (Z^A*qref.leftErrorReference Z A*Z^(qref.radicalWidth Z))*F*
          Z^(-1/2500+εouter+δref+δrad)/(seedOuter.absNorm : ℝ) := by
        rw [hvolume]
        have hp : qref.radicalWidth Z+δrad-1/2500+εouter =
            qref.radicalWidth Z+(-1/2500+εouter+δrad) := by ring
        rw [hp]
        simp only [Real.rpow_add hz]
        ring
      _ = _ := by
        rw [(qref.raw_error_reference_target Z A hZ.1).1,hvolume]
        rw [show qref.leftTargetWidth Z A-1/2500+εouter+δref+δrad =
          qref.leftTargetWidth Z A+(-1/2500+εouter+δref+δrad) by ring]
        simp only [Real.rpow_add hz]
        dsimp [F]
        ring
  · have hsum : (∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
        (right k).value N (q k.1).C R k.2.1.val (swapSubset (q k.1).C (q k.1).D (q k.1).E)
          ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve) ≤
        (qref.rightErrorReference Z A*Z^δref)*(F*Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ)) := by
      calc
        _ ≤ ∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
            (qref.rightErrorReference Z A*Z^δref)*
              (right k).normalizedValue N (q k.1).C R k.2.1.val (swapSubset (q k.1).C (q k.1).D (q k.1).E)
          ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve := by
          apply Finset.sum_le_sum
          intro k hk
          have hi := (firstRightSourceLabels_gates labels q (fun _ => sourceRadius src)
            Z Bfirst hz.le (fun _ _ => hHcap) k hk).1
          have hn := (right k).normalizedValue_nonneg N (q k.1).C R k.2.1.val (swapSubset (q k.1).C (q k.1).D (q k.1).E)
            ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve hz
          have hid := (right k).value_eq_normalized_reference N (q k.1).C R k.2.1.val (swapSubset (q k.1).C (q k.1).D (q k.1).E)
            ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve hz (q k.1).hD.1
          rw [hvolume] at hid
          exact hid.le.trans (mul_le_mul_of_nonneg_right (hcommon k hi).2 hn)
        _ = (qref.rightErrorReference Z A*Z^δref)*
            (∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
              (right k).normalizedValue N (q k.1).C R k.2.1.val (swapSubset (q k.1).C (q k.1).D (q k.1).E)
          ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left he.2
          (mul_nonneg (qref.error_reference_pos Z A hz).2.le (Real.rpow_nonneg hz.le _))
    have hstep := mul_le_mul_of_nonneg_left hsum hvol.le
    have href := (qref.error_reference_pos Z A hz).2
    calc
      _ ≤ volume src*((qref.rightErrorReference Z A*Z^δref)*
          (F*Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ))) := hstep
      _ ≤ volume src*((qref.rightErrorReference Z A*Z^δref)*
          (F*Z^(qref.radicalWidth Z+δrad-1/2500+εouter)/(seedOuter.absNorm : ℝ))) := by
        gcongr
      _ = (Z^A*qref.rightErrorReference Z A*Z^(qref.radicalWidth Z))*F*
          Z^(-1/2500+εouter+δref+δrad)/(seedOuter.absNorm : ℝ) := by
        rw [hvolume]
        have hp : qref.radicalWidth Z+δrad-1/2500+εouter =
            qref.radicalWidth Z+(-1/2500+εouter+δrad) := by ring
        rw [hp]
        simp only [Real.rpow_add hz]
        ring
      _ = _ := by
        rw [(qref.raw_error_reference_target Z A hZ.1).2,hvolume]
        rw [show qref.rightTargetWidth Z A-1/2500+εouter+δref+δrad =
          qref.rightTargetWidth Z A+(-1/2500+εouter+δref+δrad) by ring]
        simp only [Real.rpow_add hz]
        dsimp [F]
        ring

#print axioms actual_first_independent_raw_errors_full
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstRawErrorsFull -/
