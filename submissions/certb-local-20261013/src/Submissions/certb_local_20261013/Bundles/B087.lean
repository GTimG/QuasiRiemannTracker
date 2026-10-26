/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.certb_local_20261013.Bundles.B060
import Submissions.certb_local_20261013.Bundles.B077
import Submissions.certb_local_20261013.Bundles.B081
import Submissions.certb_local_20261013.Bundles.B085
import Submissions.certb_local_20261013.Bundles.B086
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport

/- BEGIN ORIGINAL MODULE Analytic.ActualExtractedLocalErrorsFull ; sha256 98c609daf78900e9f8db7dc4d8759b10d49641748a1240f1a40144421733a5e2 -/
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
local instance actualExtractedLocalErrorsDecEqFull {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance actualExtractedLocalErrorsFiniteFull : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem actual_firstExtractedErrors_local_bound_full
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
    (hbudget : CenteredMomentFirstSecondInputGates.exponent Avol Dscale Pmask qmoving εgeo ξ ≤ Bcap):
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
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    ∀ prime : O, Prime (Ideal.span {prime}) →
    sigma/6≤ Real.logb Z (normValue prime) →
    prime ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))) →
    9/2000≤ Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀ family : Fin 3 → RayCharacter → Character,
    (∀ i χ, (family i χ).modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))) →
    (∀ i χ, ((family i χ).modulus.absNorm:ℝ)≤
      cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (errorIndex i+1))) →
    let radius := fun i : Fin 3 => errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (errorIndex i+1)
    src.W₁ 0=0 → src.W₂ 0=0 → volume src≤ Z^Avol →
    (R0.absNorm : ℝ)≤ Z^Pmask → R0≠0 →
    (∀ i, (radius i)⁻¹≤ Z^Dscale) →
    (∀ i χ, ((family i χ).modulus.absNorm : ℝ)≤ Z^qmoving) →
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
    Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ))≤429/100000 →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh
    firstExtractedErrors (child src C R0 B τ t) (R0*C) seed Z
      (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime family ≤
      mass (child src C R0 B τ t)^2*
        (reference (τ.modulus.absNorm : ℝ) (volume src) (C.absNorm : ℝ) Z
          (allowance C D Z)/(volume src/(C.absNorm : ℝ)))*
        (1872*(Fintype.card RayCharacter : ℝ))*
          ∑ j : Fin 4,
            (Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight*
              Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm : ℝ))*
            (upper^N)^(powers εsrc j)*
            Z^(localErrorExponents paid εsrc Mvolume saving delta reserve j) := by
  subst sigma
  obtain ⟨Uprofile,Jheight,hactual⟩ := actual_firstExtractedErrors_power_from_caps_full (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ (9/500) cost hsigma hξsmall hcost
    Avol Dscale Pmask qmoving εgeo hεgeo hbudget
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hactualZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime hprimeScale hpool hlog hslot family hrad hfamily
  dsimp only
  intro hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv hconductorCap seed hseed hseed0 hseedcap
    profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip
    hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂ hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
  let r : Fin 3 → RayCharacter → ℝ := fun i _ =>
    Mgeom/4-Real.logb Z (C.absNorm : ℝ)-errorRemoval prime Z (errorIndex i+1)
  have hp0 : prime≠0 := fun h => hprime.ne_zero (by simp [h])
  have hr : ∀ (i : Fin 3) (χ : RayCharacter)
      (Bp : actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(errorIndex i+1))),
      let input := errorInput src C R0 B τ t (Ideal.span {prime}) (errorIndex i+1) Bp (family i χ) t
      Z^(r i χ)≤ input.X₁ ∧ Z^(r i χ)≤ input.X₂ ∧ Z^(r i χ)≤ input.Y₁ ∧ Z^(r i χ)≤ input.Y₂ := by
    intro i χ Bp
    exact actual_errorInput_plain_lower src C R0 hC.1 B τ t prime hp0 (errorIndex i+1) Bp
      (family i χ) t Z Mgeom hZ.1 hplainX₁ hplainX₂ hplainY₁ hplainY₂
  have hbound := hZ.2 θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime hprimeScale hslot family hrad hfamily
    hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv hconductorCap seed hseed hseed0 hseedcap
    profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip
    hsourceLower r hr
  have hz := zero_lt_one.trans hZ.1
  have hq := norm_pos τ.modulus τ.modulus_ne_bot
  have hv := volume_pos src
  have hc := norm_pos C hC.1
  have hHcoef : ∀ j : Fin 4, 0≤ Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight*
      Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm : ℝ) := by
    intro j
    positivity
  have hvol := common_volume_le N upper hupper src hcard hupperSrc C R0 B τ t hB
  rw [show upper^N*volume src/(C.absNorm : ℝ)=upper^N*(volume src/(C.absNorm : ℝ)) by ring] at hvol
  apply firstExtractedErrors_of_core_sum (child src C R0 B τ t) (R0*C) seed Z
    (Real.logb Z (D.absNorm : ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm : ℝ)) delta reserve prime family
    (τ.modulus.absNorm : ℝ) (volume src) (C.absNorm : ℝ) (allowance C D Z)
    (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ)))
    _ εsrc saving (upper^N) r _ _ hq hv hc hz (pow_nonneg (zero_le_one.trans hupper) N) hHcoef
  · exact firstExtractedErrors_core_normalization (child src C R0 B τ t) (R0*C) seed Z
      (Real.logb Z (D.absNorm : ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm : ℝ)) delta reserve prime hp0 family
      (τ.modulus.absNorm : ℝ) (volume src) (C.absNorm : ℝ) (allowance C D Z)
      (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ)))
      _ εsrc saving (upper^N) r _ hq hv hc hz hεsrc.le
      (pow_nonneg (zero_le_one.trans hupper) N) hHcoef hvol hbound
  · intro i χ j
    exact actual_refined_local_error_cores src.η τ C D hC hD hCD E K (volume src) Z
      delta reserve _ εsrc saving Mgeom Mdecl Mvolume hK hv hZ.1 hεsrc.le hdef hgeom hwidth
      hvolGeom hvolCap hfixed hmod M H Sbad hbad prime hpool (errorIndex i+1)
      (first_extracted_error_indices i) hlog j

#print axioms actual_firstExtractedErrors_local_bound_full
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualExtractedLocalErrorsFull -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstCoarseSum ; sha256 c643d29b18bec24ecd720aee77b1a86bfcdb20b95c5fd15f2ec3bc9e8745cb5c -/
section



/-! First coarse projector sums are controlled by actual nonzero columns,
even when the supplied divisor pool contains arbitrarily large inactive ideals. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstDivisorCommonBound CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstPhysicalSource CenteredMomentFirstSectors
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondDivisorSupport CenteredMomentSecondDiagonal QuadraticInitialBound
local notation "O" => HeckeFamily.O
local instance firstCoarseSumDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma common_coarse_zero_of_inactive {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C : Ideal O) (hC : Supported C) (L : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K H : ℝ)
    (hsource : ∀ I, s.beta I ≠ 0 → (I.absNorm : ℝ) ≤ H)
    (hL : ¬(L ≠ 0 ∧ (L.absNorm : ℝ) ≤ H/(C.absNorm : ℝ))) :
    coarse s C hC L W K = 0 := by
  have hz (I : supportedColumns (residualPool C hC.1 s.columns)) :
      (if IsCoprime C (I:Ideal O) ∧ L ∣ (I:Ideal O) then s.beta (C*I) else 0) = 0 := by
    split_ifs with hd
    · by_contra hb
      exact hL ⟨ne_zero_of_dvd_ne_zero (Finset.mem_filter.mp I.property).2.1 hd.2,
        live_right_divisor_norm C I L hC.1 (Finset.mem_filter.mp I.property).2.1
          s.beta H hsource hb hd.2⟩
    · rfl
  simp only [coarse,pairMajorant,hz,norm_zero,zero_mul,Finset.sum_const_zero]

/-- The bound does not depend on the cardinality of the supplied pool. -/
theorem common_coarse_projector_sum {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C : Ideal O) (hC : Supported C) (Ds : Finset (Ideal O))
    (W : Ideal O → 𝓢(ℝ,ℂ)) (K : Ideal O → ℝ) (H D : ℝ)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hK : ∀ L ∈ Ds, 0 < K L)
    (hW : ∀ L ∈ Ds, diagonalControl (W L)*max 1 (K L) ≤ D)
    (hsource : ∀ I, s.beta I ≠ 0 → (I.absNorm : ℝ) ≤ H) :
    (∑ L ∈ Ds, coarse s C hC L (W L) (K L)) ≤
      128*D*(H/(C.absNorm : ℝ))^2*(sourceAbsoluteMass s.columns s.beta)^2 := by
  let S := Ds.filter (fun L => L ≠ 0 ∧ (L.absNorm : ℝ) ≤ H/(C.absNorm : ℝ))
  have hc := CenteredMomentFirstScale.norm_pos C hC.1
  have hcard := divisible_ideal_card S 1 one_ne_zero
    (fun L hL => (Finset.mem_filter.mp hL).2.1) (fun _ _ => one_dvd _)
    (H/(C.absNorm : ℝ)) (div_nonneg hH hc.le)
    (fun L hL => (Finset.mem_filter.mp hL).2.2)
  simp only [map_one,Nat.cast_one,div_one] at hcard
  have he : (∑ L ∈ Ds, coarse s C hC L (W L) (K L)) =
      ∑ L ∈ S, coarse s C hC L (W L) (K L) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L hL
    split_ifs with h
    · rfl
    · exact common_coarse_zero_of_inactive s C hC L (W L) (K L) H hsource h
  rw [he]
  calc
    _ ≤ ∑ L ∈ S, D*(H/(C.absNorm : ℝ))*(sourceAbsoluteMass s.columns s.beta)^2 := by
      apply Finset.sum_le_sum
      intro L hL
      have hl := (Finset.mem_filter.mp hL).1
      apply (common_coarse_absolute s C hC L (W L) (K L) H (hK L hl) hH hsource).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hW L hl)
        (div_nonneg hH hc.le)) (sq_nonneg _)
    _ = (S.card : ℝ)*(D*(H/(C.absNorm : ℝ))*(sourceAbsoluteMass s.columns s.beta)^2) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (128*(H/(C.absNorm : ℝ)))*(D*(H/(C.absNorm : ℝ))*(sourceAbsoluteMass s.columns s.beta)^2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem original_common_coarse_projector_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed C : Ideal O) (hC : Supported C) (Ds : Finset (Ideal O))
    (W : Ideal O → 𝓢(ℝ,ℂ)) (K : Ideal O → ℝ) (H D B₁ B₂ : ℝ)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hK : ∀ L ∈ Ds, 0 < K L)
    (hW : ∀ L ∈ Ds, diagonalControl (W L)*max 1 (K L) ≤ D)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hz₁ : s.W₁ 0 = 0) (hz₂ : s.W₂ 0 = 0)
    (hb₁ : ∀ x, ‖s.W₁ x‖ ≤ B₁) (hb₂ : ∀ x, ‖s.W₂ x‖ ≤ B₂)
    (hsource : sourceRadius s ≤ H) :
    (∑ L ∈ Ds, coarse (original s R seed) C hC L (W L) (K L)) ≤
      (volume s.toData/(C.absNorm : ℝ))*
        (128*D*(originalAbsoluteProfile s B₁ B₂)^2*H^2*volume s.toData/(C.absNorm : ℝ)) := by
  have hc := CenteredMomentFirstScale.norm_pos C hC.1
  have hh := common_coarse_projector_sum (original s R seed) C hC Ds W K H D hH hD hK hW
    (fun I hI => (original_column_norm s R seed I hz₁ hz₂ hI).2.trans hsource)
  have hm := original_absolute_mass s R seed B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sourceAbsoluteMass_nonneg _ _) hm 2) (by positivity)).trans_eq
  ring

#print axioms original_common_coarse_projector_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstCoarseSum -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighSecondRows ; sha256 a6e6a16d15d4ca1118b9a9621f5dcb60e8cb19c9f8dd6bcb61203e92d0dfce0a -/
section



/-! The literal two physical children use the same second family and the
same canonical first-label unit. Their opposite row signs are absorbed by
the fixed reflected parent dictionary before any high-bin estimate. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open ActualEisensteinCubic CompletedGauss RayFourExpansion
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSourceRectangleMask CenteredMomentNaturalRowSource
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFixedRay CenteredMomentChildRows
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
local notation "O" => HeckeFamily.O

theorem actual_second_side_family_row
    (η : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
    (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C₁ D₁ hC₁ E₁ ξ₁ ξ₂)
    (left : Bool) (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD : primeSupport C₂ = primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character)
    (hfamily : Family (firstSideCharacter F left) C₂ D₂ hC₂ hD₂ U family)
    (T : Ideal O) (hT : T ≠ 0) (hCT : C₂ ∣ T ∨ D₂ ∣ T)
    (χ : RayCharacter) (z : O) (hz : z ≠ 0) :
    let w := secondReconstructedRow C₁ D₁ hC₁ E₁
      (firstSideDictionaryUnit η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F) C₂ D₂ hC₂ U left z hz
    ∃ parent : JointParentLabel η, ∃ N : NaturalRow parent.val w.val,
      ∀ (t : ℝ) (I : Ideal O),
        rowWeight (family χ) (fixedBadMask*idealGenerator T) 1 z t I =
        rowWeight parent.val (fixedBadMask*idealGenerator (T*firstSideCanceled C₁ D₁ left))
          1 w.val t I := by
  dsimp only
  obtain ⟨parent,N,hcoeff⟩ :=
    (Classical.choose_spec (actual_second_side_deleted_dictionary η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F)).2
      left C₂ D₂ hC₂ hD₂ hCD U family hfamily T hT hCT χ z hz
  refine ⟨parent,N,?_⟩
  intro t I
  let Ns := naturalRow (family χ) z hz
  have hcancel : firstSideCanceled C₁ D₁ left ≠ 0 := canceledIdeal_ne_zero C₁ D₁ hC₁ _
  have hh : heightCoeff (excluded Ns.character T) t I =
      heightCoeff (excluded N.character (T*firstSideCanceled C₁ D₁ left)) t I := by
    simp only [heightCoeff,hcoeff Ns I]
  exact (naturalRow_masked_height Ns T hT t I).symm.trans
    (hh.trans (naturalRow_masked_height N _ (mul_ne_zero hT hcancel) t I))

/-- Exact all-ideal source identity in the frequency form used by the
second physical block, including the actual cumulative common mask. -/
theorem actual_second_side_child_row
    (η : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
    (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C₁ D₁ hC₁ E₁ ξ₁ ξ₂)
    (left : Bool) (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD : primeSupport C₂ = primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂))
    (T : Ideal O) (hT : T ≠ 0) (hCT : C₂ ∣ T ∨ D₂ ∣ T)
    (χ : RayCharacter) (z : O) (hz : z ≠ 0) :
    let w := secondReconstructedRow C₁ D₁ hC₁ E₁
      (firstSideDictionaryUnit η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F) C₂ D₂ hC₂ U left z hz
    ∃ parent : JointParentLabel η, ∃ N : NaturalRow parent.val w.val,
      ∀ (t : ℝ) (I : Ideal O),
        rowWeight (childCharacter (firstSideCharacter F left) χ) (fixedBadMask*idealGenerator T)
          (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U) z t I =
        rowWeight parent.val (fixedBadMask*idealGenerator (T*firstSideCanceled C₁ D₁ left))
          1 w.val t I := by
  dsimp only
  obtain ⟨family,hfamily⟩ := exists_exceptional_family (firstSideCharacter F left) C₂ D₂ hC₂ hD₂ hCD U
  obtain ⟨parent,N,hh⟩ := actual_second_side_family_row η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F left
    C₂ D₂ hC₂ hD₂ hCD U family hfamily T hT hCT χ z hz
  refine ⟨parent,N,?_⟩
  intro t I
  have hf := actual_second_family_masked_row (firstSideCharacter F left) C₂ D₂ hC₂ hD₂ U
    family hfamily T hCT χ z t I
  apply Eq.trans _ (hf.symm.trans (hh t I))
  simp only [rowWeight,childCharacter,rayParent,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,one_mul]

/-- Both physical children share one nonzero reconstructed row. The right
child keeps the same G,U family and its literal opposite frequency. -/
theorem actual_second_side_paired_rows
    (η : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
    (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C₁ D₁ hC₁ E₁ ξ₁ ξ₂)
    (left : Bool) (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD : primeSupport C₂ = primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (TL TR : Ideal O) (hTL : TL ≠ 0) (hTR : TR ≠ 0)
    (hCL : C₂ ∣ TL ∨ D₂ ∣ TL) (hCR : C₂ ∣ TR ∨ D₂ ∣ TR)
    (χL χR : RayCharacter) (z : O) (hz : z ≠ 0) :
    let w := secondReconstructedRow C₁ D₁ hC₁ E₁
      (firstSideDictionaryUnit η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F) C₂ D₂ hC₂ U left z hz
    ∃ parentL parentR : JointParentLabel η,
    ∃ NL : NaturalRow parentL.val w.val, ∃ NR : NaturalRow parentR.val w.val,
      ∀ (t : ℝ) (I : Ideal O),
        (rowWeight (childCharacter (firstSideCharacter F left) χL) (fixedBadMask*idealGenerator TL)
          (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U) z t I =
        rowWeight parentL.val (fixedBadMask*idealGenerator (TL*firstSideCanceled C₁ D₁ left))
          1 w.val t I) ∧
        (rowWeight (childCharacter (firstSideCharacter F left) χR) (fixedBadMask*idealGenerator TR)
          (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U) (-z) t I =
        rowWeight parentR.val (fixedBadMask*idealGenerator (TR*firstSideCanceled C₁ D₁ left))
          1 w.val t I) := by
  intro w
  obtain ⟨pL,NL,hL⟩ := actual_second_side_child_row η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F left
    C₂ D₂ hC₂ hD₂ hCD U TL hTL hCL χL z hz
  obtain ⟨pR,NR,hR⟩ := actual_second_side_child_row η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F left
    C₂ D₂ hC₂ hD₂ hCD U TR hTR hCR χR (-z) (neg_ne_zero.mpr hz)
  obtain ⟨pR',hreflect⟩ := jointParentDictionary_reflect η pR
  refine ⟨pL,pR',NL,naturalRow pR'.val w.val w.property,?_⟩
  intro t I
  refine ⟨hL t I,?_⟩
  have hw : (secondReconstructedRow C₁ D₁ hC₁ E₁
      (firstSideDictionaryUnit η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F) C₂ D₂ hC₂ U left (-z)
      (neg_ne_zero.mpr hz)).val = -w.val := by
    dsimp only [secondReconstructedRow,w]
    ring
  have hh := hR t I
  rw [hw] at hh
  apply hh.trans
  have hLam : goodLambda ∣ fixedBadMask := dvd_mul_right _ _
  have htwo : (2 : O) ∣ fixedBadMask := dvd_mul_left _ _
  rw [←rowWeight_ideal_mask _ _ _ _ _ hLam htwo,
    ←rowWeight_ideal_mask _ _ _ _ _ hLam htwo,hreflect w.val t I]

def CommonSecondKernelLabel.leftNaturalPuncture {Slot : Type*} [Fintype Slot]
    (s : CommonSecondKernelLabel Slot) (C₁ D₁ : Ideal O) (left : Bool) : Ideal O :=
  (s.puncture*(s.firstCommon*s.second.val.1))*firstSideCanceled C₁ D₁ left

def CommonSecondKernelLabel.rightNaturalPuncture {Slot : Type*} [Fintype Slot]
    (s : CommonSecondKernelLabel Slot) (C₁ D₁ : Ideal O) (left : Bool) : Ideal O :=
  (s.puncture*(s.firstCommon*s.second.val.2))*firstSideCanceled C₁ D₁ left

/-- The actual common-source label supplies the complete masks and second
arithmetic data internally. No natural dictionary or row-identity premise
is required. -/
theorem actual_common_second_paired_rows
    {Slot : Type*} [Fintype Slot]
    (η : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
    (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C₁ D₁ hC₁ E₁ ξ₁ ξ₂) (left : Bool)
    (s : CommonSecondKernelLabel Slot) (hs : s.parent = firstSideCharacter F left)
    (hpuncture : s.puncture ≠ 0) (z : O) (hz : z ≠ 0) :
    let w := secondReconstructedRow C₁ D₁ hC₁ E₁
      (firstSideDictionaryUnit η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F)
      s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.partition left z hz
    s.leftNaturalPuncture C₁ D₁ left ≠ 0 ∧ s.rightNaturalPuncture C₁ D₁ left ≠ 0 ∧
    ∃ parentL parentR : JointParentLabel η,
    ∃ NL : NaturalRow parentL.val w.val, ∃ NR : NaturalRow parentR.val w.val,
      ∀ (t : ℝ) (I : Ideal O),
        (rowWeight (childCharacter s.parent s.leftRay)
          (fixedBadMask*idealGenerator (s.puncture*(s.firstCommon*s.second.val.1)))
          s.toKernelLabel.frequency z t I =
        rowWeight parentL.val (fixedBadMask*idealGenerator (s.leftNaturalPuncture C₁ D₁ left))
          1 w.val t I) ∧
        (rowWeight (childCharacter s.parent (s.rightRay⁻¹))
          (fixedBadMask*idealGenerator (s.puncture*(s.firstCommon*s.second.val.2)))
          s.toKernelLabel.frequency (-z) t I =
        rowWeight parentR.val (fixedBadMask*idealGenerator (s.rightNaturalPuncture C₁ D₁ left))
          1 w.val t I) := by
  intro w
  have hTL : s.puncture*(s.firstCommon*s.second.val.1) ≠ 0 :=
    mul_ne_zero hpuncture (mul_ne_zero s.hfirst.1 s.toKernelLabel.hC.1)
  have hTR : s.puncture*(s.firstCommon*s.second.val.2) ≠ 0 :=
    mul_ne_zero hpuncture (mul_ne_zero s.hfirst.1 s.toKernelLabel.hD.1)
  have hcancel : firstSideCanceled C₁ D₁ left ≠ 0 := canceledIdeal_ne_zero C₁ D₁ hC₁ _
  refine ⟨mul_ne_zero hTL hcancel,mul_ne_zero hTR hcancel,?_⟩
  obtain ⟨parentL,parentR,NL,NR,hh⟩ := actual_second_side_paired_rows η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F left
    s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.toKernelLabel.hD s.toKernelLabel.hCD s.partition
    (s.puncture*(s.firstCommon*s.second.val.1)) (s.puncture*(s.firstCommon*s.second.val.2)) hTL hTR
    (Or.inl (dvd_mul_of_dvd_right (dvd_mul_left _ _) _))
    (Or.inr (dvd_mul_of_dvd_right (dvd_mul_left _ _) _)) s.leftRay (s.rightRay⁻¹) z hz
  refine ⟨parentL,parentR,NL,NR,?_⟩
  intro t I
  simpa only [hs,CommonSecondKernelLabel.leftNaturalPuncture,
    CommonSecondKernelLabel.rightNaturalPuncture,SecondKernelLabel.frequency,
    CommonSecondKernelLabel.toKernelLabel] using hh t I

/-- Exact natural realizations of a physical pair; constructed below from
source identities, with no analytic estimate among the fields. -/
structure PhysicalNaturalPair {Slot : Type*} [Fintype Slot]
    (η : Character) (w : NonzeroElement) (s : CommonSecondKernelLabel Slot)
    (z : O) (TL TR : Ideal O) where
  parentL : JointParentLabel η
  parentR : JointParentLabel η
  naturalL : NaturalRow parentL.val w.val
  naturalR : NaturalRow parentR.val w.val
  punctureL_ne : TL ≠ 0
  punctureR_ne : TR ≠ 0
  left_eq : ∀ (t : ℝ) (I : Ideal O),
    rowWeight (childCharacter s.parent s.leftRay)
      (fixedBadMask*idealGenerator (s.puncture*(s.firstCommon*s.second.val.1)))
      s.toKernelLabel.frequency z t I = rowWeight parentL.val (fixedBadMask*idealGenerator TL) 1 w.val t I
  right_eq : ∀ (t : ℝ) (I : Ideal O),
    rowWeight (childCharacter s.parent (s.rightRay⁻¹))
      (fixedBadMask*idealGenerator (s.puncture*(s.firstCommon*s.second.val.2)))
      s.toKernelLabel.frequency (-z) t I = rowWeight parentR.val (fixedBadMask*idealGenerator TR) 1 w.val t I

/-- Literal first-source arithmetic data and its selected common side. -/
structure FirstSidePresentation (η : Character) where
  C : Ideal O
  D : Ideal O
  supported : Supported C
  active : Finset (CommonIndex C D)
  leftRay : RayCharacter
  rightRay : RayCharacter
  pair : FixedPair η C D supported active leftRay rightRay
  side : Bool

namespace FirstSidePresentation
variable {η : Character} {Slot : Type*} [Fintype Slot]

def sourceParent (F : FirstSidePresentation η) : Character := firstSideCharacter F.pair F.side

def row (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (z : O) (hz : z ≠ 0) : NonzeroElement :=
  secondReconstructedRow F.C F.D F.supported F.active
    (firstSideDictionaryUnit η F.C F.D F.supported F.active F.leftRay F.rightRay F.pair)
    s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.partition F.side z hz

def leftPuncture (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot) : Ideal O :=
  s.leftNaturalPuncture F.C F.D F.side

def rightPuncture (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot) : Ideal O :=
  s.rightNaturalPuncture F.C F.D F.side

theorem paired_rows (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (hs : s.parent = F.sourceParent) (hp : s.puncture ≠ 0) (z : O) (hz : z ≠ 0) :
    F.leftPuncture s ≠ 0 ∧ F.rightPuncture s ≠ 0 ∧
    ∃ parentL parentR : JointParentLabel η,
    ∃ NL : NaturalRow parentL.val (F.row s z hz).val,
    ∃ NR : NaturalRow parentR.val (F.row s z hz).val,
      ∀ (t : ℝ) (I : Ideal O),
        (rowWeight (childCharacter s.parent s.leftRay)
          (fixedBadMask*idealGenerator (s.puncture*(s.firstCommon*s.second.val.1)))
          s.toKernelLabel.frequency z t I =
        rowWeight parentL.val (fixedBadMask*idealGenerator (F.leftPuncture s)) 1 (F.row s z hz).val t I) ∧
        (rowWeight (childCharacter s.parent (s.rightRay⁻¹))
          (fixedBadMask*idealGenerator (s.puncture*(s.firstCommon*s.second.val.2)))
          s.toKernelLabel.frequency (-z) t I =
        rowWeight parentR.val (fixedBadMask*idealGenerator (F.rightPuncture s)) 1 (F.row s z hz).val t I) :=
  actual_common_second_paired_rows η F.C F.D F.supported F.active F.leftRay F.rightRay F.pair F.side s hs hp z hz

def naturalPair (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (hs : s.parent = F.sourceParent) (hp : s.puncture ≠ 0) (z : O) (hz : z ≠ 0)
    (w : NonzeroElement) (hw : w = F.row s z hz) :
    PhysicalNaturalPair η w s z (F.leftPuncture s) (F.rightPuncture s) :=
  Classical.choice (by
    obtain ⟨hL,hR,parentL,parentR,NL,NR,hrow⟩ := F.paired_rows s hs hp z hz
    rw [←hw] at NL NR hrow
    exact ⟨⟨parentL,parentR,NL,NR,hL,hR,(fun t I => (hrow t I).1),(fun t I => (hrow t I).2)⟩⟩)

end FirstSidePresentation

#print axioms actual_common_second_paired_rows
#print axioms actual_second_side_family_row
#print axioms actual_second_side_child_row
#print axioms actual_second_side_paired_rows
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighSecondRows -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowOriginalVolume ; sha256 dcb85de9a7ce8de8765522af9c491e275ec9332ed56825e6bd78fd5ff7909c0b -/
section


/-! Convert the low sector denominator to the original source volume;
the first common ideal contributes its reciprocal, with only the actual
volume-sector tolerance. -/
set_option autoImplicit false
namespace OAI
noncomputable section
namespace SevenEighths.Local44.Analytic

theorem low_sector_to_original_volume (X V P C Z A c E volumeLoss : ℝ)
    (hZ : 1 < Z) (hP : 0 < P) (hC : 0 ≤ C)
    (hV : Z^(A-volumeLoss) ≤ V)
    (hsector : X/(Z^(A-c)*P) ≤ C*Z^E) :
    X/(V*P) ≤ C*Z^(E-c+volumeLoss) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hv : 0 < V := (Real.rpow_pos_of_pos hz _).trans_le hV
  have hr := sector_original_volume_ratio Z A c volumeLoss V hZ hV
  calc
    X/(V*P) = (X/(Z^(A-c)*P))*(Z^(A-c)/V) := by
      field_simp
    _ ≤ (C*Z^E)*Z^(-c+volumeLoss) := mul_le_mul hsector hr
      (div_nonneg (Real.rpow_nonneg hz.le _) hv.le) (mul_nonneg hC (Real.rpow_nonneg hz.le _))
    _ = _ := by
      rw [mul_assoc,←Real.rpow_add hz]
      congr 2
      ring

#print axioms low_sector_to_original_volume
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowOriginalVolume -/

/- BEGIN ORIGINAL MODULE Analytic.JointProfileEnvelopes ; sha256 6e2bcffc025840a7a9e1aa0f1959eb6741fe4aaf78c407fd03b964130c8e295b -/
section



/-! The profile envelopes have fixed bounds independent of arithmetic
labels, length scales and Fourier heights. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open CenteredMomentCommonRadialData
variable {ι α : Type*} [Fintype ι]

theorem input_profile_mass_le (s : Input ι) (M : ℝ)
    (hM : 0 ≤ M) (hs : ∀ i, s.M i ≤ M) : (∏ i, s.M i) ≤ M^Fintype.card ι := by
  calc
    (∏ i, s.M i) ≤ ∏ _i : ι, M :=
      Finset.prod_le_prod₀ (fun i _ => zero_le_one.trans (s.M_ge_one i)) (fun i _ => hs i)
    _ = M^Fintype.card ι := by simp

theorem originalAbsoluteProfile_le_fixed (s : Input ι) (M upper b₁ b₂ B₁ B₂ : ℝ)
    (hM : 0 ≤ M) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hs : ∀ i, s.M i ≤ M) (hu : s.upper ≤ upper) (hb₁ : s.b₁ ≤ b₁) (hb₂ : s.b₂ ≤ b₂) :
    originalAbsoluteProfile s B₁ B₂ ≤
      2*128^(Fintype.card ι+2)*M^Fintype.card ι*B₁*B₂*
        (max 1 upper)^Fintype.card ι*max 1 b₁*max 1 b₂ := by
  have hp := input_profile_mass_le s M hM hs
  unfold originalAbsoluteProfile
  gcongr

theorem retained_profile_le_fixed (s : Input ι) (M upper b₁ b₂ a : ℝ)
    (hM : 0 ≤ M) (ha : 0 < a)
    (hs : ∀ i, s.M i ≤ M) (hu : s.upper ≤ upper) (hb₁ : s.b₁ ≤ b₁) (hb₂ : s.b₂ ≤ b₂) :
    (secondProfileScalar s.toData)^2*commonSourceProfile s/a ≤
      2*(max 1 b₁*max 1 b₂)*(M^Fintype.card ι)^4*(max 1 upper)^Fintype.card ι/a := by
  have hp := input_profile_mass_le s M hM hs
  have hpn : 0 ≤ ∏ i,s.M i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (s.M_ge_one i))
  calc
    _ = 2*(max 1 s.b₁*max 1 s.b₂)*(∏ i,s.M i)^4*(max 1 s.upper)^Fintype.card ι/a := by
      unfold secondProfileScalar commonSourceProfile
      rw [mul_pow,Real.sq_sqrt (by positivity)]
      ring
    _ ≤ _ := by gcongr

theorem originalAbsoluteEnvelope_le_fixed [DecidableEq ι]
    (S : Finset α) (s : α → CommonSecondKernelLabel ι) (M upper b₁ b₂ B₁ B₂ : ℝ)
    (hM : 0 ≤ M) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hs : ∀ v ∈ S, ∀ i, (s v).input.M i ≤ M)
    (hu : ∀ v ∈ S, (s v).input.upper ≤ upper)
    (hb₁ : ∀ v ∈ S, (s v).input.b₁ ≤ b₁) (hb₂ : ∀ v ∈ S, (s v).input.b₂ ≤ b₂) :
    originalAbsoluteEnvelope S s B₁ B₂ ≤
      max 1 (2*128^(Fintype.card ι+2)*M^Fintype.card ι*B₁*B₂*
        (max 1 upper)^Fintype.card ι*max 1 b₁*max 1 b₂) := by
  unfold originalAbsoluteEnvelope
  split_ifs with hS
  · apply max_le_max le_rfl
    apply Finset.sup'_le
    intro v hv
    exact originalAbsoluteProfile_le_fixed (s v).input M upper b₁ b₂ B₁ B₂
      hM hB₁ hB₂ (hs v hv) (hu v hv) (hb₁ v hv) (hb₂ v hv)
  · exact le_max_left _ _

theorem retainedProfileEnvelope_le_fixed [DecidableEq ι]
    (S : Finset α) (s : α → CommonSecondKernelLabel ι) (M upper b₁ b₂ a : ℝ)
    (hM : 0 ≤ M) (ha : 0 < a)
    (hs : ∀ v ∈ S, ∀ i, (s v).input.M i ≤ M)
    (hu : ∀ v ∈ S, (s v).input.upper ≤ upper)
    (hb₁ : ∀ v ∈ S, (s v).input.b₁ ≤ b₁) (hb₂ : ∀ v ∈ S, (s v).input.b₂ ≤ b₂) :
    retainedProfileEnvelope S s a ≤
      max 1 (2*(max 1 b₁*max 1 b₂)*(M^Fintype.card ι)^4*(max 1 upper)^Fintype.card ι/a) := by
  unfold retainedProfileEnvelope
  split_ifs with hS
  · apply max_le_max le_rfl
    apply Finset.sup'_le
    intro v hv
    exact retained_profile_le_fixed (s v).input M upper b₁ b₂ a
      hM ha (hs v hv) (hu v hv) (hb₁ v hv) (hb₂ v hv)
  · exact le_max_left _ _

#print axioms retainedProfileEnvelope_le_fixed
#print axioms originalAbsoluteEnvelope_le_fixed
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointProfileEnvelopes -/

/- BEGIN ORIGINAL MODULE Analytic.JointSecondLowGate ; sha256 4a8767f5098e419995654b7ea2ec91f2b501fc8851fc5b1302fed5bed943427e -/
section


/-! Actual second-family low gates from the shared reconstructed-row bin.
The unpunctured incumbent state and the literal common/canceled source
masks are related by exact finite deletion, rather than identified. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic RayFourExpansion CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentSecondExceptionalFamily
open CenteredMomentNaturalRowSource CenteredMomentEnergyState
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance secondLowGateFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- No coefficient transport, nonprincipality, or conductor hypothesis is
left to the caller. Both first sides use the same literal fixed dictionary. -/
theorem eventually_actual_second_low_gate
    {Slot : Type*} [Fintype Slot] [Nonempty Slot]
    (η₀ : Character) (radial ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (η : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
        (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair η C₁ D₁ hC₁ E₁ ξ₁ ξ₂),
      let u := firstSideDictionaryUnit η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
      activeConductor C₁ D₁ = (u : O)*∏ i,activePrimary C₁ D₁ i ∧
      ∀ (left : Bool) (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂),
      primeSupport C₂ = primeSupport D₂ →
      ∀ (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
      Family (firstSideCharacter F left) C₂ D₂ hC₂ hD₂ U family →
      ∀ (T : Ideal O), T ≠ 0 → (C₂ ∣ T ∨ D₂ ∣ T) → ∀ (χ : RayCharacter),
      ∀ (Bmask d : ℝ) (s : NaturalState Z Bmask radial),
      s.character = family χ → s.puncture = 1 → s.width+Bmask+ξ ≤ d →
      ∀ (Q : Ideal O) (hQM : Q ≤ M) (hQ : s.fixedModulus = internalQ Q η₀)
        (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)}),
      ∀ (z : O) (hz : (supportedNaturalState s).radial.keep z),
      let w := secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left z (s.row_ne_zero z hz.1)
      ∀ (τ e a : ℝ) (k : ℕ), 0 < e →
      ∀ (holes : JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hholes : ∀ label,holes label ≠ 0),
      jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH (fun _ : Slot => η₀))
        (internalQ Q η₀) hQ72
        (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀) (internalQ Q η₀)
          (inf_le_left.trans hQM) (fun _ => inf_le_right))
        holes hholes a (a+e) (3*(k+1 : ℕ)*Z^τ) w →
      NaturalLowGate M H hH (supportedNaturalState s) η₀ Q hQM hQ d τ e a k z hz := by
  filter_upwards [eventually_supported_low_gate_of_deleted_common_bin (Slot := Slot)
    M H hH η₀ radial ξ hξ] with Z hgate
  refine ⟨hgate.1,?_⟩
  intro η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
  let u := firstSideDictionaryUnit η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
  obtain ⟨hu,hrows⟩ := Classical.choose_spec (actual_second_side_deleted_dictionary η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F)
  refine ⟨hu,?_⟩
  intro left C₂ D₂ hC₂ hD₂ hCD U family hfamily T hT hCT χ Bmask d s hcharacter hpuncture hwidth
    Q hQM hQ hQ72 z hz w τ e a k he holes hholes hbin
  obtain ⟨parent,N,hcoeff⟩ := hrows left C₂ D₂ hC₂ hD₂ hCD U family hfamily T hT hCT χ z (s.row_ne_zero z hz.1)
  have hcancel : firstSideCanceled C₁ D₁ left ≠ 0 := canceledIdeal_ne_zero C₁ D₁ hC₁ _
  apply hgate.2 Bmask d s hwidth η Q hQM hQ hQ72 w parent N
    (T*firstSideCanceled C₁ D₁ left) T (mul_ne_zero hT hcancel) hT z hz
  · intro I
    have hh := hcoeff (naturalRow (family χ) z (s.row_ne_zero z hz.1)) I
    rw [excluded_ideal _ T hT,←hcharacter] at hh
    simpa only [hpuncture,excluded_ideal _ T hT,excluded_ideal _ 1 one_ne_zero,
      isCoprime_one_right,ite_true,supportedNaturalState] using hh
  · exact he
  · exact hbin

#print axioms eventually_actual_second_low_gate
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondLowGate -/
