/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B000
import Submissions.reserve_local_20261013.Bundles.B088
import Submissions.reserve_local_20261013.Bundles.B090
import Submissions.reserve_local_20261013.Bundles.B091
import Submissions.reserve_local_20261013.Bundles.B092
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonSectorColumn
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonSymmetry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectedSource

/- BEGIN ORIGINAL MODULE Analytic.ActualAllocatedErrorsFull ; sha256 1e778aa7430b29f686faac1c43aa2b8fad0315102738dd0cd69db2a60ba59815 -/
section


/-! Actual extracted error estimates with Ready discharged by source caps.
Dead extracted sources vanish exactly. Every live extracted source receives
its Ready packet from the pinned source theorem before the genuine analytic
estimate is used. -/
set_option autoImplicit false
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
local instance actualAllocatedErrorsDecEqFull {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance actualAllocatedErrorsFiniteFull : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem actual_allocated_extracted_errors_full
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
    (εalloc : ℝ) (hεalloc : 0 < εalloc):
    ∃ Calloc : ℝ, 0 < Calloc ∧
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
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(τ:Character)(t:ℝ),
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
    P.Nonempty →
    (∀ (B : actualAllocations src.pools C), frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      ∀ (prime : elementPool P) i, ∀ I∈(activeInput (child src C R0 B τ t)).slots i,
      IsCoprime (Ideal.span {prime.val}) I) →
    ∀ family : actualAllocations src.pools C → elementPool P → Fin 3 → RayCharacter → Character,
    (∀ B, frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      ∀ prime i χ, (family B prime i χ).modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))) →
    (∀ B, frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      ∀ prime i χ, ((family B prime i χ).modulus.absNorm:ℝ)≤
      cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (errorIndex i+1))) →
    let radius := fun (prime : elementPool P) (i : Fin 3) => errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (errorIndex i+1)
    src.W₁ 0=0 → src.W₂ 0=0 → volume src≤ Z^Avol →
    (R0.absNorm : ℝ)≤ Z^Pmask → R0≠0 →
    (∀ prime i, (radius prime i)⁻¹≤ Z^Dscale) →
    (∀ B, frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      ∀ prime i χ, ((family B prime i χ).modulus.absNorm : ℝ)≤ Z^qmoving) →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀profile:Profiles a b,profile.profile 0=src.W₁ → profile.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*(3/4)*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀ Mgeom Mvolume : ℝ, 1≤ Mgeom →
    Z^(Mgeom/4)≤ src.X₁ → Z^(Mgeom/4)≤ src.X₂ →
    Z^(Mgeom/4)≤ src.Y₁ → Z^(Mgeom/4)≤ src.Y₂ →
    Mgeom≤ Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
    Real.logb Z (volume src)≤(883/1000)*Mgeom →
    Real.logb Z (volume src)≤ Mvolume →
    Real.logb Z fixedPresentationCost≤1/1000 →
    Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ))≤1/250 →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh
    allocatedExtractedErrors N src C R0 seed τ t upper Z
      (Real.logb Z (D.absNorm : ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve P family/
      ((τ.modulus.absNorm : ℝ)*(volume src/(C.absNorm : ℝ)^2)*Z^(allowance C D Z)) ≤
      Calloc*(C.absNorm : ℝ)^εalloc*mass src^2*
        (56*1872*(Fintype.card RayCharacter : ℝ))*
          ∑ j : Fin 4,
            (Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight*
              Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm : ℝ))*
            (upper^N)^(powers εsrc j)*
            Z^(localErrorExponents paid εsrc Mvolume saving delta reserve j) := by
  obtain ⟨Calloc,hCalloc,halloc⟩ := allocated_error_reference_bound N upper εalloc hupper hεalloc
  obtain ⟨Uprofile,Jheight,hactual⟩ := actual_firstExtractedErrors_local_average_full (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ Sbad hbad sigma cost hsigma hξsmall hcost hsigma_eq
    Avol Dscale Pmask qmoving εgeo hεgeo hbudget
  refine ⟨Calloc,hCalloc,Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hactualZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    C D R0 hC hD hCD E τ t hmod K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hP hslot family hrad hfamily
  intro hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv hconductorCap seed hseed hseed0 hseedcap
    profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip
    hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂ hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
  let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
  let paid := (Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh
  let budget := (56*1872*(Fintype.card RayCharacter : ℝ))*∑ j : Fin 4,
    (Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight*
      Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm : ℝ))*
    (upper^N)^(powers εsrc j)*Z^(localErrorExponents paid εsrc Mvolume saving delta reserve j)
  have hz := zero_lt_one.trans hZ.1
  have hbudget0 : 0 ≤ budget := by
    dsimp [budget]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro j hj
    positivity
  have hh := halloc src hcard C R0 seed hC.1 τ t Z (Real.logb Z (D.absNorm : ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve (allowance C D Z) budget hz hbudget0 P family ?_
  · simpa only [budget,mul_assoc] using hh
  · intro B hB
    have hb := hZ.2 θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
      C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
      hP (hslot B hB) (family B) (hrad B hB) (hfamily B hB)
      hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv (hconductorCap B hB) seed hseed hseed0 hseedcap
      profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip
      hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂ hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
    simpa only [budget,paid,mul_assoc] using hb

#print axioms actual_allocated_extracted_errors_full
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualAllocatedErrorsFull -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalValues ; sha256 5e1e19ddca3a6e72373d221e01196c7c02026e1b4e5ed861debf8437043c00ad -/
section





/-! Coherent common-second exceptional amplitudes. Allocation is paid by
the original-source bilinear theorem only after selecting the inducing
rows; no positivity of a transformed exceptional part is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource CenteredMomentCommonSectorColumn
open CenteredMomentCommonLinearSource CenteredMomentCommonHeightEnvelope CenteredMomentReflectedSource
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentActiveSource CenteredMomentSecondRetainedAggregate CenteredMomentSourceRow
open CenteredMomentSecondBlockAggregate
open CenteredMomentSecondSectorColumns CenteredMomentRowNorm CenteredMomentChildAssembly
open CenteredMomentHeckeColumnWindow CenteredMomentSecondScaled CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFiniteProfileExceptionalCommon CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonExceptionalCost CenteredMomentExceptionalAmplitudePair
open RayFourExpansion UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local instance coherentExceptionalValuesDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma secondChildValue_eq_normalizedColumn
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed C L : Ideal O) (hC : Supported C)
    (η ψ : Character) (χ : RayCharacter) (A : O)
    (hψ : ∀ I : Ideal O, Supported I → IsCoprime C I → ∀ t : ℝ,
      heightCoeff ψ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (CompletedGauss.primaryGenerator I))
    (v H : ℝ) (z : O) :
    secondChildValue η v (original src R seed).columns (original src R seed).beta
      C hC A L χ z H =
      ((Real.sqrt (volume src.toData) : ℂ)/(Real.sqrt H : ℂ))*
        normalizedColumn (withHeight src ψ v) C hC R seed L z := by
  have hV := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  have hs : (Real.sqrt (volume src.toData) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hV).ne'
  rw [secondChildValue_eq_sector_row]
  have hc := actual_sector_column src η ψ χ A C hC R seed L v z hψ
  dsimp only at hc
  have hc' : rowPolynomial Finset.univ (sectorElement C hC.1 (original src R seed).columns)
      (divisorCoefficient L (sectorElement C hC.1 (original src R seed).columns)
        (movingCoefficient A (sectorElement C hC.1 (original src R seed).columns)
          (fun I => (original src R seed).beta (C*I)*heightCoeff η v I)) χ) z =
      sourceColumn (withHeight src ψ v) C hC R seed L z := hc
  rw [hc']
  unfold normalizedColumn
  change (Real.sqrt H : ℂ)⁻¹ * sourceColumn (withHeight src ψ v) C hC R seed L z =
    ((Real.sqrt (volume src.toData) : ℂ)/(Real.sqrt H : ℂ))*
      ((Real.sqrt (volume src.toData) : ℂ)⁻¹*sourceColumn (withHeight src ψ v) C hC R seed L z)
  field_simp

/-- Exact pairing of the actual coherent second children with cumulative
common ideals. The right source is reflected, with the same original row. -/
theorem actual_common_second_pair_eq_normalized
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁)
    (p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁))
    (η : Character) (U : Finset (CommonIndex p.val.1 p.val.2))
    (family : RayCharacter → Character)
    (hfamily : Family η p.val.1 p.val.2 (lowActiveLeftSupported p) (lowActiveRightSupported p) U family)
    (χL χR : RayCharacter) (vL vR HL HR : ℝ) (hHL : 0 < HL) (hHR : 0 < HR)
    (Ds : Finset (Ideal O)) (rows : Finset O) :
    (∑ L ∈ Ds, ‖(moebius L : ℂ)‖*∑ z ∈ rows,
      ‖secondChildValue η vL
        (commonSecondColumns (original src R seed) C₁ hC₁)
        (commonSecondBeta (original src R seed) C₁ L₁) p.val.1 (lowActiveLeftSupported p)
        (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)
        L χL z HL‖ *
      ‖secondChildValue η vR
        (commonSecondColumns (original src R seed) C₁ hC₁)
        (commonSecondBeta (original src R seed) C₁ L₁) p.val.2 (lowActiveRightSupported p)
        (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)
        L χR (-z) HR‖) =
      (volume src.toData/Real.sqrt (HL*HR))*(∑ L ∈ Ds, ‖(moebius L : ℂ)‖*∑ z ∈ rows,
        ‖normalizedColumn (withHeight src (family χL) vL) (C₁*p.val.1)
          ((supported_mul_iff _ _).mpr ⟨hC₁,lowActiveLeftSupported p⟩) R seed L z‖ *
        ‖normalizedColumn (withHeight src (reflected (family χR)) vR) (C₁*p.val.2)
          ((supported_mul_iff _ _).mpr ⟨hC₁,lowActiveRightSupported p⟩) R seed L z‖) := by
  have hg := actual_second_common_first_projector (original src R seed) C₁ L₁ hC₁ p
  have hV := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  have hvs := Real.sqrt_pos.mpr hV
  have hls := Real.sqrt_pos.mpr hHL
  have hrs := Real.sqrt_pos.mpr hHR
  have heL (L : Ideal O) (z : O) := common_second_child_eq_complete_source (original src R seed)
    C₁ p.val.1 L₁ hC₁ (lowActiveLeftSupported p) hg.2.2.1 hg.1 η
    (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) z vL L χL
  have heR (L : Ideal O) (z : O) := common_second_child_eq_complete_source (original src R seed)
    C₁ p.val.2 L₁ hC₁ (lowActiveRightSupported p) hg.2.2.2 hg.2.1 η
    (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) (-z) vR L χR
  have hvalL (L : Ideal O) (z : O) := secondChildValue_eq_normalizedColumn src R seed (C₁*p.val.1) L
    ((supported_mul_iff _ _).mpr ⟨hC₁,lowActiveLeftSupported p⟩) η (family χL) χL
    (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)
    (fun I hI hcop t => hfamily.height_eq χL I hI (Or.inl hcop.of_mul_left_right) t) vL HL z
  have hvalR (L : Ideal O) (z : O) := secondChildValue_eq_normalizedColumn src R seed (C₁*p.val.2) L
    ((supported_mul_iff _ _).mpr ⟨hC₁,lowActiveRightSupported p⟩) η (family χR) χR
    (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)
    (fun I hI hcop t => hfamily.height_eq χR I hI (Or.inr hcop.of_mul_left_right) t) vR HR (-z)
  have hnR (L : Ideal O) (z : O) := normalizedColumn_neg (withHeight src (family χR) vR)
    (C₁*p.val.2) ((supported_mul_iff _ _).mpr ⟨hC₁,lowActiveRightSupported p⟩) R seed L z
  have hroot : (Real.sqrt (volume src.toData)/Real.sqrt HL)*
      (Real.sqrt (volume src.toData)/Real.sqrt HR) = volume src.toData/Real.sqrt (HL*HR) := by
    rw [Real.sqrt_mul hHL.le]
    field_simp
    rw [Real.sq_sqrt hV.le]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  rw [mul_left_comm _ ‖(moebius L : ℂ)‖]
  apply congrArg (fun x : ℝ => ‖(moebius L : ℂ)‖*x)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hl : secondChildValue η vL (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.1 (lowActiveLeftSupported p)
      (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) L χL z HL =
      ((Real.sqrt (volume src.toData) : ℂ)/(Real.sqrt HL : ℂ))*
        normalizedColumn (withHeight src (family χL) vL) (C₁*p.val.1)
          ((supported_mul_iff _ _).mpr ⟨hC₁,lowActiveLeftSupported p⟩) R seed L z := by
    change (Real.sqrt HL : ℂ)⁻¹ * _ = _
    rw [heL]
    exact hvalL L z
  have hr : secondChildValue η vR (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.2 (lowActiveRightSupported p)
      (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) L χR (-z) HR =
      ((Real.sqrt (volume src.toData) : ℂ)/(Real.sqrt HR : ℂ))*
        normalizedColumn (withHeight src (reflected (family χR)) vR) (C₁*p.val.2)
          ((supported_mul_iff _ _).mpr ⟨hC₁,lowActiveRightSupported p⟩) R seed L z := by
    change (Real.sqrt HR : ℂ)⁻¹ * _ = _
    rw [heR]
    exact (hvalR L z).trans (congrArg
      (fun c : ℂ => ((Real.sqrt (volume src.toData) : ℂ)/(Real.sqrt HR : ℂ))*c) (hnR L z))
  rw [hl,hr]
  simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hvs,abs_of_pos hls,abs_of_pos hrs]
  rw [←hroot]
  ring

def commonSecondValuePair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁)
    (p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁))
    (η : Character) (U : Finset (CommonIndex p.val.1 p.val.2))
    (χL χR : RayCharacter) (vL vR HL HR : ℝ) (Ds : Finset (Ideal O)) (rows : Finset O) : ℝ :=
  ∑ L ∈ Ds, ‖(moebius L : ℂ)‖*∑ z ∈ rows,
    ‖secondChildValue η vL (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.1 (lowActiveLeftSupported p)
      (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) L χL z HL‖ *
    ‖secondChildValue η vR (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.2 (lowActiveRightSupported p)
      (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) L χR (-z) HR‖

/-- The genuine finite-profile exceptional theorem for the coherent
common source. Allocation mass is internal to the original-source
amplitude theorem and the literal projector sum remains intact. -/
theorem actual_coherent_exceptional_values
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi) (lo hi : ι → ℝ)
    (ε δ θ B Lbound : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ)
    (hB : 0 ≤ B) (hL : 0 ≤ Lbound) :
    ∃ J : ℕ, ∃ Sprofile : Finset (ℕ×ℕ), (0,0) ∈ Sprofile ∧
    ∀ Q : Ideal O, Q ≠ 0 → ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (src : Input ι) (profile : Profiles wlo whi),
    (∀ i, src.lo i = lo i) → (∀ i, src.hi i = hi i) → (∀ i, 1 ≤ src.P i) →
    src.W₁ = profile.profile 0 → src.W₂ = profile.profile 1 →
    ∀ (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁), R ≠ 0 → seed ∣ C₁ →
    ∀ p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁),
    ∀ (η : Character) (U : Finset (CommonIndex p.val.1 p.val.2))
      (family : RayCharacter → Character),
    Family η p.val.1 p.val.2 (lowActiveLeftSupported p) (lowActiveRightSupported p) U family →
    ∀ (χL χR : RayCharacter) (vL vR HL HR r : ℝ), 0 < HL → 0 < HR →
    Z^r ≤ src.X₁ → Z^r ≤ src.X₂ → Z^r ≤ src.Y₁ → Z^r ≤ src.Y₂ →
    ∀ rows : Finset O, (∀ z ∈ rows, z ≠ 0) →
    (∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow (family χL) Q fixedBadMask 1 z) →
    (∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow (family χR) Q fixedBadMask 1 (-z)) →
    (∀ z ∈ rows, ((family χL).modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*(C₁*p.val.1).absNorm)*(Ideal.span {z}).absNorm : ℝ) ≤ Z^B) →
    (∀ z ∈ rows, ((reflected (family χR)).modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*(C₁*p.val.2).absNorm)*(Ideal.span {z}).absNorm : ℝ) ≤ Z^B) →
    ∀ Ds : Finset (Ideal O),
    (∀ L ∈ Ds, (moebius L : ℂ) ≠ 0 → (L.absNorm : ℝ) ≤ Z^Lbound) →
    commonSecondValuePair src R seed C₁ L₁ hC₁ p η U χL χR vL vR HL HR Ds rows ≤
      (volume src.toData/Real.sqrt (HL*HR))*
        (K*(rows.card : ℝ)*Z^(2*ε+δ-max (max (r-Real.logb Z ((C₁*p.val.1).absNorm : ℝ)) 0)
          (max (r-Real.logb Z ((C₁*p.val.2).absNorm : ℝ)) 0))*
          (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)^θ*
          (profileMass Sprofile (withHeight src (family χL) vL).toData
            (withHeight src (reflected (family χR)) vR).toData profile profile J*
              frozenProfile src*frozenProfile src/
                (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm))) := by
  obtain ⟨J,Sprofile,hSprofile,hbound⟩ := actual_common_better_side
    wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ
  obtain ⟨K,hK,hbound⟩ := hbound Q hQ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro src profile hlo hhi hP hW₁ hW₂ R seed C₁ L₁ hC₁ hR hseed
    p η U family hfamily χL χR vL vR HL HR r hHL hHR hX₁ hX₂ hY₁ hY₂
    rows hn hexL hexR hcondL hcondR Ds hDs
  have hsr : seed ∣ C₁*p.val.2 := hseed.trans (dvd_mul_right _ _)
  have hsl : seed ∣ C₁*p.val.1 := hseed.trans (dvd_mul_right _ _)
  have hexR' : ∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow
      (reflected (family χR)) Q fixedBadMask 1 z := by
    intro z hz
    exact (reflected_inducing (family χR) Q fixedBadMask 1 z
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hexR z hz)
  have hh := hZ.2 (withHeight src (family χL) vL) (withHeight src (reflected (family χR)) vR)
    profile profile hlo hhi hlo hhi hP hP hW₁ hW₂ hW₁ hW₂
    (C₁*p.val.1) (C₁*p.val.2)
    ((supported_mul_iff _ _).mpr ⟨hC₁,lowActiveLeftSupported p⟩)
    ((supported_mul_iff _ _).mpr ⟨hC₁,lowActiveRightSupported p⟩)
    R seed hR hsl hsr r r hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂
    rows hn hexL hexR' hcondL hcondR Ds hDs
  rw [commonSecondValuePair,actual_common_second_pair_eq_normalized src R seed C₁ L₁ hC₁ p
    η U family hfamily χL χR vL vR HL HR hHL hHR Ds rows]
  exact mul_le_mul_of_nonneg_left hh
    (div_nonneg (CenteredMomentExceptionalAmplitudePair.volume_pos src.toData).le (Real.sqrt_nonneg _))

#print axioms secondChildValue_eq_normalizedColumn
#print axioms actual_common_second_pair_eq_normalized
#print axioms actual_coherent_exceptional_values
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalValues -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentSourceTail ; sha256 f1428b45601d2a8ec4b5dea07180e186bec0eca566c9e019a66852bb940f93f4 -/
section


/-! The discarded tail at the actual source-radius nominal scale.
The fixed support factor can be smaller than one; no lower comparison
between source radius and original volume is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceSecondZeroEnergy
open CenteredMomentExceptionalAmplitudePair CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_common_source_tail_arbitrary_saving (Csource B ξ saving : ℝ)
    (hB : 0 ≤ B) (hξ : 0 < ξ) :
    ∃ SΦ : Finset (ℕ×ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (s : Input ι) (R seed C L : Ideal O) (hC : Supported C)
      (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ → s.W₁ 0 = 0 → s.W₂ 0 = 0 →
      (∀ x, ‖s.W₁ x‖ ≤ B₁) → (∀ x, ‖s.W₂ x‖ ≤ B₂) →
      0 < sourceRadius s → sourceRadius s ≤ Csource*volume s.toData → volume s.toData ≤ Z^B →
    ∀ (η : Character) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K Tsec : ℝ),
      0 < K → Tsec ≤ Z^B → (sourceRadius s/(C.absNorm : ℝ))^2/K ≤ Tsec →
      ‖secondDiscardedEnergy η t (commonSecondColumns (original s R seed) C hC)
        (commonSecondBeta (original s R seed) C L) Φ K Tsec Z ξ‖ / volume s.toData ≤
      Cbound*(originalAbsoluteProfile s B₁ B₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  obtain ⟨Adec,hdecay⟩ := choose_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,D,hD,htail⟩ := second_discarded_energy_bound Adec
  let Cs := max 1 Csource
  have hCs : 0 < Cs := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨SΦ,D*Cs^2*(1+Real.exp (2*0))^2,by positivity,?_⟩
  filter_upwards [eventually_tail_threshold 0 ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s R seed C L hC B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂ hsource₀ hsource hVcap
    η t Φ K Tsec hK hTcap hnom
  let V := volume s.toData
  let Eabs := originalAbsoluteProfile s B₁ B₂
  have hV : 0 < V := CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
  have hNC : 0 < (C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hNC1 : (1 : ℝ) ≤ C.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hX : 0 < sourceRadius s/(C.absNorm : ℝ) := div_pos hsource₀ hNC
  have hXcap : Real.exp 0*(sourceRadius s/(C.absNorm : ℝ)) ≤ Cs*V := by
    rw [Real.exp_zero,one_mul]
    exact (div_le_self hsource₀.le hNC1).trans
      (hsource.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hV.le))
  have hT : 0 < Tsec := (div_pos (sq_pos_of_pos hX) hK).trans_le hnom
  have hmass : sourceAbsoluteMass (commonSecondColumns (original s R seed) C hC)
      (commonSecondBeta (original s R seed) C L) ≤ Eabs*V := by
    have hh := (common_second_absolute_mass (original s R seed) C L hC).trans
      (original_absolute_mass s R seed B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂)
    rwa [sourceAbsoluteMass_active] at hh
  have hN := commonSecond_source_norm_cap (original s R seed) C L hC (sourceRadius s)
    (fun I _ hI => (original_column_norm s R seed I hz₁ hz₂ hI).2)
  have ht := htail η t (commonSecondColumns (original s R seed) C hC)
    (commonSecondBeta (original s R seed) C L) Φ K (sourceRadius s/(C.absNorm : ℝ)) 0 Tsec Z 1 ξ
    hK hX hZ.1 le_rfl (by
      intro I hI hβ
      simpa only [Real.exp_zero,one_mul] using hN I hI hβ) hnom (by simpa using hZ.2)
  have hnormsum : 0 ≤ sourceAbsoluteMass (commonSecondColumns (original s R seed) C hC)
      (commonSecondBeta (original s R seed) C L) := sourceAbsoluteMass_nonneg _ _
  have hE : 0 ≤ Eabs := by
    dsimp [Eabs,originalAbsoluteProfile]
    have hm : 0 ≤ ∏ j,s.M j := Finset.prod_nonneg (fun j _ => zero_le_one.trans (s.M_ge_one j))
    positivity
  have hdec := hdecay 0 Z V Tsec hZ.1.le hV hVcap hT hTcap
  have hmin : 0 < min 1 (kernelReference Tsec 0) := lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  calc
    _ ≤ ((Eabs*V)^2*K*(Cs*V)^2*(D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec 0))^2*(1+Z^(ξ/4))^Adec))/V := by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      change (sourceAbsoluteMass _ _)^2 * _ * _ * _ / _ ≤ _
      gcongr
    _ = (D*Cs^2*Eabs^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^3*((min 1 (kernelReference Tsec 0))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹) := by
      field_simp [ne_of_gt hV,ne_of_gt hmin]
    _ ≤ (D*Cs^2*Eabs^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*0))^2*Z^(-saving)) :=
      mul_le_mul_of_nonneg_left hdec (by positivity)
    _ = _ := by ring

theorem actual_common_source_tail_normalized (Csource B ξ saving : ℝ)
    (hB : 0 ≤ B) (hξ : 0 < ξ) :
    ∃ SΦ : Finset (ℕ×ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (s : Input ι) (R seed C L : Ideal O) (hC : Supported C), L ≠ 0 →
    ∀ (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ → s.W₁ 0 = 0 → s.W₂ 0 = 0 →
      (∀ x, ‖s.W₁ x‖ ≤ B₁) → (∀ x, ‖s.W₂ x‖ ≤ B₂) →
      0 < sourceRadius s → sourceRadius s ≤ Csource*volume s.toData → volume s.toData ≤ Z^B →
      (L.absNorm : ℝ) ≤ Z^B →
    ∀ (η : Character) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K Tsec P : ℝ),
      0 < K → K ≤ Z^B → 1 ≤ P → Tsec ≤ Z^B →
      (sourceRadius s/(C.absNorm : ℝ))^2/K ≤ Tsec →
      ‖secondDiscardedEnergy η t (commonSecondColumns (original s R seed) C hC)
        (commonSecondBeta (original s R seed) C L) Φ K Tsec Z ξ‖ / (volume s.toData*P) ≤
      (Cbound*(originalAbsoluteProfile s B₁ B₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*Z^(-saving)/(L.absNorm : ℝ) := by
  obtain ⟨SΦ,Cbound,hCbound,hh⟩ := actual_common_source_tail_arbitrary_saving (ι := ι)
    Csource B ξ (saving+2*B) hB hξ
  refine ⟨SΦ,Cbound,hCbound,?_⟩
  filter_upwards [hh] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s R seed C L hC hL B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂ hsource₀ hsource hVcap hLcap
    η t Φ K Tsec P hK hKcap hP hTcap hnom
  have hNL : 0 < (L.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL)
  have hb := hZ.2 s R seed C L hC B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂ hsource₀ hsource hVcap
    η t Φ K Tsec hK hTcap hnom
  rw [←div_div]
  exact tail_prime_projector_absorption Z B saving K P (L.absNorm : ℝ)
    _ _ hZ.1.le hK.le hP hNL (by positivity) hKcap hLcap hb

#print axioms actual_common_source_tail_normalized
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentSourceTail -/

/- BEGIN ORIGINAL MODULE Analytic.JointDirectCommonLiteralSum ; sha256 8f9e024fd88470bc7b3e0309bb35a2d16afd08eec6628e3063ea06ec193260f5 -/
section


/-! The coherent common main term keeps its literal prime denominator.
This matches the second physical source precount without spending the
reciprocal prime count twice. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentFirstScale
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance directCommonLiteralSumDecEq : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

/-- One genuine amplifier family precedes the labels and all heights.
The literal prime denominator in the coherent main matches the physical
second-source normalization; extracted errors are unchanged. -/
theorem joint_direct_common_annular_amplification_literal
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (N : ℕ) (a b sigma loss BR Bs Mmax eta Csec xi reserve : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hsigma : 0 < sigma) (hloss : 0 < loss)
    (hM : 0 ≤ Mmax) (hgap : eta < sigma/6) (hCsec : 1 ≤ Csec)
    (hxi : 0 ≤ xi) (hreserve : 0 < reserve) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss) ≤ (P.card : ℝ) ∧
      ∃ τ : (J : Finset ι) → Character → elementPool P → Fin 3 → RayCharacter → Character,
        (∀ J η (p : elementPool P) i χ, ((τ J η p i χ).modulus.absNorm : ℝ) ≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ {Λ : Type*} (labels : Finset Λ) (s : Λ → Input ι) (weight : Λ → ℝ), Fintype.card ι ≤ N →
        ∀ (C R seed L I J E : Λ → Ideal O) (hC : ∀ l, Supported (C l))
          (parent : Λ → Character) (t K X Tsec H₀ d c : Λ → ℝ) (z : Λ → ι → ℝ),
        (∀ l ∈ labels, 0 ≤ weight l) →
        (∀ l ∈ labels, a ≤ (s l).lower) → (∀ l ∈ labels, (s l).upper ≤ b) →
        (∀ l ∈ labels, seed l ∣ C l) →
        (∀ l ∈ labels, ∀ j, z l j ≤ eta) → (∀ l ∈ labels, ∀ j, (s l).P j = Z^(z l j)) →
        (∀ l ∈ labels, R l ≠ 0) → (∀ l ∈ labels, L l ≠ 0) →
        (∀ l ∈ labels, ((R l*C l).absNorm : ℝ) ≤ Z^BR) →
        (∀ l ∈ labels, ((L l).absNorm : ℝ) ≤ Z^Bs) →
        (∀ l ∈ labels, E l ≠ 0) → (∀ l ∈ labels, 0 < K l) → (∀ l ∈ labels, 0 < X l) →
        (∀ l ∈ labels, Tsec l ≤ Csec*firstNominalScale (I l) (J l) (E l) (K l) (X l)) →
        (∀ l ∈ labels, 0 < H₀ l) → (∀ l ∈ labels, H₀ l ≤ 4*frequencyRadius (Tsec l) Z xi) →
        (∀ l ∈ labels, 8*H₀ l ≤ Z^Mmax) →
        (∑ l ∈ labels, weight l*
          ((commonEnergy (original (s l) (R l) (seed l)) (C l) (hC l) (parent l) (t l) (L l)
            CenteredMomentFirstAnnularMajorant.profile (H₀ l)).re / volume (s l))) ≤
          (56*((Mmax+2*sigma)/(sigma/6)))*
            (∑ l ∈ labels, weight l*
              ((commonEnergy (original (s l) (R l) (seed l)) (C l) (hC l) (parent l) (t l) (L l) ballProfile
                (mainCommonRadius Z (d l) (nominalLog (I l) (J l) (E l) (K l) (X l) Z) (c l) sigma
                  (frequencyLoss Z (32*Csec) xi) reserve)).re / (volume (s l)*(P.card : ℝ)))) +
          ∑ l ∈ labels, weight l*
            allocatedExtractedErrors N (s l) (C l) (R l) (L l) (parent l) (t l) b Z (d l)
              (nominalLog (I l) (J l) (E l) (K l) (X l) Z) (c l) sigma
              (frequencyLoss Z (32*Csec) xi) reserve P (fun B => τ (liveIndices B.val) (parent l)) := by
  filter_upwards [eventually_direct_common_annular_amplification (ι := ι) M H hH Sbad hbad
    N a b sigma loss BR Bs Mmax eta Csec xi reserve ha hb hsigma hloss hM hgap hCsec hxi hreserve]
    with Z hsource
  obtain ⟨hZ,hP,hcard,τ,hτ,hpoint⟩ := hsource
  refine ⟨hZ,hP,hcard,τ,hτ,?_⟩
  intro Λ labels s weight hn C R seed L I J E hC parent t K X Tsec H₀ d c z
    hw hlo hhi hseed hz hlen hR hL hRCcap hLcap hE hK hX hsec hH₀ houter hcap
  let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
  let F := (Mmax+2*sigma)/(sigma/6)
  let Main (l : Λ) :=
    (commonEnergy (original (s l) (R l) (seed l)) (C l) (hC l) (parent l) (t l) (L l) ballProfile
      (mainCommonRadius Z (d l) (nominalLog (I l) (J l) (E l) (K l) (X l) Z) (c l) sigma
        (frequencyLoss Z (32*Csec) xi) reserve)).re / (volume (s l)*(P.card : ℝ))
  let Err (l : Λ) := allocatedExtractedErrors N (s l) (C l) (R l) (L l) (parent l) (t l) b Z (d l)
    (nominalLog (I l) (J l) (E l) (K l) (X l) Z) (c l) sigma
    (frequencyLoss Z (32*Csec) xi) reserve P (fun B => τ (liveIndices B.val) (parent l))
  change _ ≤ (56*F)*(∑ l ∈ labels, weight l*Main l)+
    ∑ l ∈ labels, weight l*Err l
  calc
    _ ≤ ∑ l ∈ labels, weight l*((56*F)*Main l+Err l) := by
      apply Finset.sum_le_sum
      intro l hl
      apply mul_le_mul_of_nonneg_left _ (hw l hl)
      apply (hpoint (s l) hn (hlo l hl) (hhi l hl) (C l) (R l) (seed l) (L l) (hC l) (hseed l hl)
          (parent l) (t l) (z l) (hz l hl) (hlen l hl) (hR l hl) (hL l hl) (hRCcap l hl) (hLcap l hl)
          (I l) (J l) (E l) (hE l hl) (K l) (X l) (Tsec l) (H₀ l) (d l) (c l)
          (hK l hl) (hX l hl) (hsec l hl) (hH₀ l hl) (houter l hl) (hcap l hl)).trans_eq
      dsimp only [Main,Err,F,P]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      ring

#print axioms joint_direct_common_annular_amplification_literal
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointDirectCommonLiteralSum -/

/- BEGIN ORIGINAL MODULE Analytic.JointErrorUniformBudget ; sha256 d262c2176bebcdcf0090278b6d1a28b30fa4ba117df3a8b1cd49d57e6dd11bcf -/
section


/-! The genuine Gaussian losses and four local error powers have a
uniform reserve after the actual allocation subpower is paid. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
namespace SevenEighths.Local44.Analytic

theorem local_error_allocation_reserve
    (Z C Bfirst εalloc paid eps Mcap saving delta reserve : ℝ)
    (loss weight : Fin 4 → ℝ)
    (hZ : 1 < Z) (hC : 0 ≤ C) (hCcap : C ≤ Z^Bfirst) (hεalloc : 0 ≤ εalloc)
    (halloc : εalloc*Bfirst ≤ 1/10000)
    (hpaid : paid ≤ 1/10000) (hloss : ∀ j, loss j ≤ 1/10000)
    (hfrequency : delta+reserve ≤ 1/1000) (heps : eps*Mcap ≤ 1/1000)
    (hsaving : 0 ≤ saving) (hweight : ∀ j, 0 ≤ weight j) :
    C^εalloc*(∑ j, weight j*Z^(loss j)*Z^(localErrorExponents paid eps Mcap saving delta reserve j)) ≤
      (∑ j, weight j)*Z^(-1/2500 : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc : C^εalloc ≤ Z^(εalloc*Bfirst) := by
    calc
      _ ≤ (Z^Bfirst)^εalloc := Real.rpow_le_rpow hC hCcap hεalloc
      _ = _ := by rw [← Real.rpow_mul hz.le]; congr 1; ring
  have hlocal := local_error_source_reserve paid eps Mcap saving delta reserve loss
    hpaid hloss hfrequency heps hsaving
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hp : C^εalloc*(Z^(loss j)*Z^(localErrorExponents paid eps Mcap saving delta reserve j)) ≤
      Z^(-1/2500 : ℝ) := by
    calc
      _ ≤ Z^(εalloc*Bfirst)*(Z^(loss j)*Z^(localErrorExponents paid eps Mcap saving delta reserve j)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = Z^(εalloc*Bfirst+loss j+localErrorExponents paid eps Mcap saving delta reserve j) := by
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [hlocal j])
  convert mul_le_mul_of_nonneg_left hp (hweight j) using 1 <;> ring

#print axioms local_error_allocation_reserve
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointErrorUniformBudget -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstSourceOuter ; sha256 0cf0f442b07e4354e872479a005d819938d9f6c95634227c7890263967915c36 -/
section



/-! Actual first outer labels and their coarse polynomial count. Only
nonzero original columns are counted, and the dyadic bands are the
literal source `Blocks`. This count is used solely for Fourier tails. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstDiscardedEnergy
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondDiagonal
local notation "O" => HeckeFamily.O
local instance firstSourceOuterDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

abbrev FirstSourceOuterIndex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (K : ℝ)
    (radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ) :=
  (p : Labels s R seed) ×
    (E : ↥(inactiveSubsets p.val.1 p.val.2)) ×
      Blocks (effectiveScale p.val.1 p.val.2 E.val K) (radius p E.val)
        (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)

def firstSourceOuterLabel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (K : ℝ)
    (radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (i : FirstSourceOuterIndex s R seed K radius) : FirstJointLabel ι where
  data := original s R seed
  parent := s.η
  C := i.1.val.1
  D := i.1.val.2
  hC := (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ i.1.property).1
  hD := (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ i.1.property).2
  hCD := first_label_equal_support s R seed i.1
  E := i.2.1.val
  leftRay := 1
  rightRay := 1
  projector := 1

lemma actual_first_common_labels_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed : Ideal O) (H : ℝ) (hH : 0 ≤ H)
    (hz₁ : s.W₁ 0 = 0) (hz₂ : s.W₂ 0 = 0) (hsource : sourceRadius s ≤ H) :
    (Fintype.card (Labels s R seed) : ℝ) ≤ (128*H)^2 := by
  let S := finiteColumns (Fintype.piFinset s.pools)
  let β := CenteredMomentOriginalCommonHarmonic.coefficient s R seed
  let Q := supportedColumns (activeSource S β)
  have hcard := divisible_ideal_card Q 1 one_ne_zero
    (fun I hI => (Finset.mem_filter.mp hI).2.1) (fun _ _ => one_dvd _) H hH
    (fun I hI => (original_column_norm s R seed I hz₁ hz₂
      (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2).2.trans hsource)
  simp only [map_one,Nat.cast_one,div_one] at hcard
  have hp : Fintype.card (Labels s R seed) ≤ Q.card^2 := by
    change Fintype.card ↥(commonLabels Q Q) ≤ Q.card^2
    rw [Fintype.card_coe]
    apply Finset.card_image_le.trans_eq
    change (Q ×ˢ Q).card = Q.card^2
    simp only [Finset.card_product,pow_two]
  exact (Nat.cast_le.mpr hp).trans (by
    simpa only [Nat.cast_pow] using pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2)

theorem eventually_firstSourceOuter_card (B L Cr : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hCr : 0 < Cr) :
    ∀ᶠ Z : ℝ in atTop,
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (s : Input ι) (R seed : Ideal O),
    s.W₁ 0 = 0 → s.W₂ 0 = 0 → 0 < sourceRadius s → sourceRadius s ≤ Z^B →
    ∀ (K : ℝ), 0 < K →
    ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
    (∀ p E, radius p E ≤ Cr*Z^L) →
    (Fintype.card (FirstSourceOuterIndex s R seed K radius) : ℝ) ≤ Z^(3*B+2) := by
  obtain ⟨Cs,hCs,hs⟩ := SquarefreeDivisorBound.prime_support_subsets_bound 1 (by norm_num)
  obtain ⟨Cd,hCd,hd⟩ := original_blocks_subpower B L Cr 1 hB hL hCr (by norm_num)
  filter_upwards [hd,eventually_ge_atTop (1:ℝ),eventually_ge_atTop (128^2*Cs*Cd)] with Z hd hZ hconst
  intro ι _ _ s R seed hz₁ hz₂ hH hsource K hK radius hr
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hp (p : Labels s R seed) := commonLabels_supported
    (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
  have hn (p : Labels s R seed) := commonLabel_norm_bounds
    (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) (Z^B)
    (fun I _ hI => (original_column_norm s R seed I hz₁ hz₂ hI).2.trans hsource)
    p.val.1 p.val.2 p.property
  have he (p : Labels s R seed) :
      ((inactiveSubsets p.val.1 p.val.2).card : ℝ) ≤ Cs*Z^B := by
    apply le_trans (Nat.cast_le.mpr (inactiveSubsets_card p.val.1 p.val.2))
    push_cast
    apply (hs p.val.1 (hp p).1.1).trans
    simpa only [Real.rpow_one] using mul_le_mul_of_nonneg_left (hn p).1 hCs.le
  have hb (p : Labels s R seed) (E : ↥(inactiveSubsets p.val.1 p.val.2)) :
      (Fintype.card (Blocks (effectiveScale p.val.1 p.val.2 E.val K) (radius p E.val)
        (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)) : ℝ) ≤ Cd*Z := by
    simpa only [Real.rpow_one] using hd p.val.1 p.val.2 (hp p).1.1 (hp p).2.1
      E.val K (radius p E.val) (sourceRadius s) hK hH (hr p E.val) hsource
  have hc := actual_first_common_labels_card s R seed (Z^B) (by positivity) hz₁ hz₂ hsource
  change (Fintype.card ((p : Labels s R seed) ×
    (E : ↥(inactiveSubsets p.val.1 p.val.2)) ×
      Blocks (effectiveScale p.val.1 p.val.2 E.val K) (radius p E.val)
        (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)) : ℝ) ≤ _
  simp only [Fintype.card_sigma,Nat.cast_sum]
  calc
    _ ≤ ∑ p : Labels s R seed, (Cs*Z^B)*(Cd*Z) := by
      apply Finset.sum_le_sum
      intro p hp'
      calc
        _ ≤ ∑ _E : ↥(inactiveSubsets p.val.1 p.val.2), Cd*Z := Finset.sum_le_sum (fun E _ => hb p E)
        _ = ((inactiveSubsets p.val.1 p.val.2).card : ℝ)*(Cd*Z) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (he p) (by positivity)
    _ = (Fintype.card (Labels s R seed) : ℝ)*((Cs*Z^B)*(Cd*Z)) := by simp
    _ ≤ (128*Z^B)^2*((Cs*Z^B)*(Cd*Z)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (128^2*Cs*Cd)*Z^(3*B+1) := by
      rw [show 3*B+1 = B+B+B+1 by ring]
      simp only [Real.rpow_add hz,Real.rpow_one]
      ring
    _ ≤ Z*Z^(3*B+1) := mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = Z^(3*B+2) := by
      rw [show 3*B+2 = 1+(3*B+1) by ring]
      simp only [Real.rpow_add hz,Real.rpow_one]

#print axioms eventually_firstSourceOuter_card
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstSourceOuter -/
