/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B008
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B015
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B016
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B017
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CanonicalErrorAdmitted
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.State
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformTests
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainFiberSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFixedIdeal

/- BEGIN ORIGINAL MODULE Analytic.ActualUnmarkedCount ; sha256 00f936637951955540be0d6decd8781156c4fc16d44290995e9e71c72df84e54 -/
section


/-!
A balanced unmarked batch count with both mean-value inputs discharged
by the established source. Only the actual batch's character dictionary
and witness geometry remain as hypotheses.
-/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter

namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles
open HeckeDetectorRawFiber HeckeDetectorInverseFiberCount
open HeckeDetectorProfiles HeckeDetectorRowwisePolynomial
open ProbeHighRowFamily LocalMoment

local notation "O" => HeckeFamily.O

/-- The complete unmarked batch bound from actual incumbent moments.

There is no hypothesis asserting either an inverse or a plain mean-value
bound. All heights and witness parameters follow the eventual scale
quantifier. The finite label and dyadic counts are displayed explicitly.
-/
theorem actual_unmarked_batch_count {Label : Type*} [Fintype Label]
    (η : Label → Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hQη : ∀ label, Q ≤ (η label).modulus)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ J : ℕ, ∃ C K₀ : ℝ, 0 < C ∧ 0 ≤ K₀ ∧
      ∀ᶠ U : ℝ in atTop, 1 < U ∧
        ∀ (a ε T allowance height : ℝ) (i : ℕ),
        1/2 ≤ a → 2*a-1 ≤ 5/6 → 0 ≤ ε → ε ≤ 1/1000 →
        0 ≤ height → 2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
        ∀ (B : UnmarkedBatch Label U a ε (unmarkedCutoff (2*a-1)) T allowance i),
        B.data = (fun label => momentData (η label)) →
        (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2 *
          fiberConstant (C*(1+height)^J) height K₀ *
            U^(unmarkedDensity (2*a-1)+156*ε+εm) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hcount⟩ :=
    batch_count_from_unmarked_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨J, C, hC, hmoments⟩ :=
    fixed_family_moments η Q hQtop hQ72 hQη εm c κ hεm hc hκ hβ
  refine ⟨J, C, K₀, hC, hK, ?_⟩
  filter_upwards [hcount, hmoments] with U hcount hmoments
  refine ⟨hmoments.1, ?_⟩
  intro a ε T allowance height i ha hδ hε hεsmall hh hf B hdata
  apply hcount a ε T allowance (C*(1+height)^J) height i hmoments.1
    ha hδ hε hεsmall (by positivity) hh hf B
  intro label left right hne
  have hgeom := fiber_lengths (B.fiber label left right hne).rows
    (B.fiber label left right hne).nonempty B.family U a ε
    (unmarkedCutoff (2*a-1)) T allowance i hmoments.1 B.witness left right
    (B.fiber label left right hne).fixed_left
    (B.fiber label left right hne).fixed_right
  have hm : (B.fiber label left right hne).m ≤ 3/4 := by
    change Real.logb U ((2 : ℝ)^right.val) ≤ 3/4
    linarith [hgeom.2.2.1]
  exact hmoments.2 B hdata label left right hne hm height hh

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualUnmarkedCount -/

/- BEGIN ORIGINAL MODULE Analytic.JointErrorAdmitted ; sha256 10dc58be14a08f4c018b1b6b4954df2c9fefcad376e32ac4ab28ed8f80b2b073 -/
section



/-! The literal source error family with the refined affine term retained. -/
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
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem refined_error_smaller_gaussian
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(hbPlain:0≤ b)
    (L:ℝ)(hL:0≤ L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0< Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0< Cm ∧ 0≤ Ce ∧ 0< Cd ∧ 0< Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Kc:ℝ,0< Kc ∧ ∃Z₀:ℝ,1< Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
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
    ∀K delta reserve cost asource:ℝ,0< K → 1≤ cost → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤ Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤ cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input ((R0*C)*(Ideal.span {prime})^(k+1)) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀_χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let Echild:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+(sigma+errorRemoval prime Z (k+1)-errorMoving prime Z (k+1))/6+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3+κ*mesh))
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc v0
        εsrc (seed.absNorm:ℝ)
        (seededFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Kerror v0
          (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1))) Echild Echild r (∏i,input.lo i) a (seed.absNorm:ℝ)
          (dc+degree+4*n) (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    refined_error_gaussian_from_bands (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  let Zw:=CenteredMomentEnergyAmplifiedChildWidth.threshold N upper sigma hupper hsigma
  refine ⟨Kc,hKc,max Zi Zw,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  subst input
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  have hZiZ:Zi≤ Z:=(le_max_left _ _).trans hZ
  have hZw:Zw≤ Z:=(le_max_right _ _).trans hZ
  have hz:1< Z:=hZi.trans_le hZiZ
  have hk':k+1=1 ∨ k+1=6 ∨ k+1=7:=by omega
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZiZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma.le hcost hasource hdelta hreserve haSource
    prime hprime (k+1) hk' hprimeScale hslot Bp υ v0 hυ _ rfl
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip
    hcap hMdecl hclip hsourceLower Scols β hScols hβ
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  apply hbound χ₀ m hm hml hm2 ?_ r hr1 hr2 hr3 hr4
  intro q hq U dyad hphysical χ
  have hs:=commonLabels_supported (activeSource Scols β) _ _ q.property
  have hη:(src.η.modulus.absNorm:ℝ)≤ Z^(Real.logb Z (src.η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_logb (zero_lt_one.trans hz) (ne_of_gt hz)
      (norm_pos src.η.modulus src.η.modulus_ne_bot)]
  have hh:=CenteredMomentEnergyAmplifiedChildWidth.error_child_width N upper sigma hupper hsigma
    Z hZw src hcard hupperSrc C D R0 hC hD hCD E B τ t hB hmod
    prime hprime k hk hslot Bp υ χerr v0 hN K delta reserve ξ
    (Real.logb Z (src.η.modulus.absNorm:ℝ)) Mwidth hK hdelta hreserve hξsmall hη hMwidth
    (activeSource Scols β) β q.val.1 q.val.2 hs.1 hs.2 U (family q U) (hfamily q U)
    _ CenteredMomentFirstAmplificationChoice.ballProfile (fun i=>(dyad i:ℤ)) hphysical χ
  exact hh.le.trans hdrop

#print axioms refined_error_smaller_gaussian
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointErrorAdmitted -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstVariableLedger ; sha256 2dc8044443137eb05b0b84d437f3f34de68c6e7a9ee1cc6db86f35e94e3eade4 -/
section



/-! Scalar normalization for first blocks with variable rows. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalSourceSupport
open CenteredMomentFirstNonexceptionalPrefactor CenteredMomentFirstCanonicalAllowance
open CenteredMomentFirstColumns CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalFamily
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem joint_first_variable_centered_blocks_from_scalar_cap
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (Mwin : Fin 4 → ℝ) (hMwin : ∀ i, 0 ≤ Mwin i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ Mwin i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (decay P₁ P₂ J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Λ → Finset O) (s : Λ → FirstJointLabel ι)
      (t K K₀ H₀ A₀ B₀ : Λ → ℝ),
      (∀ l, ∀ z ∈ rows l, z ≠ 0) →
      (∀ l, 0 < K l) → (∀ l, 0 < K₀ l) → (∀ l, 0 < H₀ l) →
      (∀ l, 0 < A₀ l) → (∀ l, 0 < B₀ l) →
      ∀ F T NC ND : ℝ, 0 < F → 0 < T → 0 < NC → 0 < ND →
      (∀ l ∈ labels, ‖scalar (s l).C (s l).D (s l).hC (s l).E (K l) (A₀ l) (B₀ l)‖ ≤ F) →
      (∀ l ∈ labels, ‖V 0 ((s l).sourceRowLog (K l) (K₀ l))‖ ≤ 1) →
      (∀ l ∈ labels, ∀ z ∈ rows l, ‖V 1 (Real.log (‖eisEmbedding z‖ ^ 2 / H₀ l))‖ ≤ 1) →
      ∀ (U : ((l : Λ) × (s l).SourceIndex) → 𝓢(ℝ, ℂ))
        (H : ((l : Λ) × (s l).SourceIndex) → ℝ),
      (∀ k ∈ firstSourceLabels labels s, 0 < H k) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z : O,
        0 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z ∈ rows k.1,
        1 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ θ w : ℝ, (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).leftEnergy
          (t k.1 + 2 * Real.pi * (w - θ)) (U k) (H k)) ≤
            (((T/NC)*E₁) * ((1 + ‖θ‖) ^ P₁) ^ 2) * (1 + ‖w‖) ^ (2 * J₁)) →
      (∀ θ w : ℝ, (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).rightEnergy
          (t k.1 + 2 * Real.pi * (w - (-θ))) (U k) (H k)) ≤
            (((T/ND)*E₂) * ((1 + ‖θ‖) ^ P₂) ^ 2) * (1 + ‖w‖) ^ (2 * J₂)) →
      ‖∑ l ∈ labels, (((1 + K₀ l * H₀ l / (A₀ l * B₀ l)) ^ decay : ℝ) : ℂ) *
        (s l).sourceBlock (t l) (rows l) W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l)‖ / T ≤
          C * (F/Real.sqrt (NC*ND)) * (Real.sqrt E₁ * Real.sqrt E₂) := by
  obtain ⟨C, hC, hc⟩ := joint_first_variable_blocks_from_common_energy (ι := ι) W V Mwin hMwin hV
    hV₂c hV₂s hV₃c hV₃s decay P₁ P₂ J₁ J₂
  refine ⟨C, hC, ?_⟩
  intro Λ inst labels rows s t K K₀ H₀ A₀ B₀ hrows hK hK₀ hH₀ hA₀ hB₀
    F T NC ND hF hT hNC hND hscalar hV₀ hV₁ U H hH hU hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hh := hc labels rows s t K K₀ H₀ A₀ B₀ (fun _ => (F : ℂ)⁻¹)
    hrows hK hK₀ hH₀ hA₀ hB₀
    (fun l hl i => (s l).sourceWeight_contraction (K l) (A₀ l) (B₀ l) F hF (hscalar l hl) i)
    hV₀ hV₁ U H hH hU hmajor ((T/NC)*E₁) ((T/ND)*E₂)
    (by positivity) (by positivity) hleft hright
  have hid : (∑ l ∈ labels,
      (((1+K₀ l*H₀ l/(A₀ l*B₀ l))^decay : ℝ) : ℂ)*(F : ℂ)⁻¹*
        (s l).sourceBlock (t l) (rows l) W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l)) =
      (F : ℂ)⁻¹ * ∑ l ∈ labels,
        (((1+K₀ l*H₀ l/(A₀ l*B₀ l))^decay : ℝ) : ℂ)*
          (s l).sourceBlock (t l) (rows l) W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hid, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hF,
    centered_energy_root_identity T NC ND E₁ E₂ hT.le hNC hND] at hh
  have hs := mul_le_mul_of_nonneg_left hh (show 0 ≤ F/T by positivity)
  convert hs using 1 <;> field_simp



#print axioms joint_first_variable_centered_blocks_from_scalar_cap
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstVariableLedger -/

/- BEGIN ORIGINAL MODULE Cycle25.Arithmetic.GlobalBound ; sha256 6a736b1db6aa0acf7d6f7369f0545cdcdfe34f17cfc784f59bd24106f3d6853d -/
section


namespace Cycle25.Arithmetic

noncomputable def certJ (d u : ℝ) : ℝ :=
  (300*kappa0-40)+(120*kappa0+80)*u+d*((24-216*kappa0)+(144*kappa0-96)*u+96*u^2)
noncomputable def certB (u : ℝ) : ℝ := (24*kappa0-4)+(48*kappa0)*u+16*u^2
noncomputable def certR (d u : ℝ) : ℝ := 1-d+d*certB u*(5-6*d)/(2*certJ d u)
noncomputable def boundaryF (d p : ℝ) : ℝ :=
  (1+ell0)/2+d/2+h0*(3*certR d (1/2-p)/4-5/12)+d*p*certT
noncomputable def certA1 (d : ℝ) : ℝ := certA10+certA11*d+certA12*d^2
noncomputable def certA2 (d : ℝ) : ℝ := certA20*d+certA21*d^2

theorem certJ_bounds {d u : ℝ} (hd : 0 ≤ d ∧ d ≤ 5/6) (hu : 0 ≤ u ∧ u ≤ 1/2) :
    69 < certJ d u ∧ certJ d u ≤ 270 := by
  have hk := kappa0_short_interval
  have hk0 : 0 ≤ kappa0 := by linarith
  have hku0 : 0 ≤ kappa0*u := mul_nonneg hk0 hu.1
  have hj11 : 0 ≤ 144*kappa0-96 := by linarith
  have hu2 : u^2 ≤ (1:ℝ)/4 := by nlinarith
  have hju : (144*kappa0-96)*u ≤ (144*kappa0-96)*(1/2) :=
    mul_le_mul_of_nonneg_left hu.2 hj11
  have hder : (24-216*kappa0)+(144*kappa0-96)*u+96*u^2 ≤ 0 := by
    nlinarith
  have hdm : d*((24-216*kappa0)+(144*kappa0-96)*u+96*u^2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hd.1 hder
  have hdl : (5/6)*((24-216*kappa0)+(144*kappa0-96)*u+96*u^2) ≤
      d*((24-216*kappa0)+(144*kappa0-96)*u+96*u^2) :=
    mul_le_mul_of_nonpos_right hd.2 hder
  have hbase : (120*kappa0+80)*u ≤ (120*kappa0+80)*(1/2) :=
    mul_le_mul_of_nonneg_left hu.2 (by linarith)
  unfold certJ
  constructor <;> nlinarith [sq_nonneg u]

theorem certA1_pos {d : ℝ} (hd : 0 ≤ d) : 0 < certA1 d := by
  have hc := coefficient_minorants
  have h1 : (-174:ℝ)*d ≤ certA11*d := mul_le_mul_of_nonneg_right (le_of_lt hc.2.1) hd
  have h2 : (347:ℝ)*d^2 ≤ certA12*d^2 :=
    mul_le_mul_of_nonneg_right (le_of_lt hc.2.2.1) (sq_nonneg d)
  unfold certA1
  linarith [hc.1, positive_A1_minorant d]

theorem certA2_nonneg {d : ℝ} (hd : 0 ≤ d) : 0 ≤ certA2 d := by
  have hc := coefficient_minorants
  have ha : 0 ≤ certA20 := by linarith [hc.2.2.2.1]
  have hb : 0 ≤ certA21 := by linarith [hc.2.2.2.2.1]
  unfold certA2
  positivity

/-- The full bivariate identity B0.49, with no grid or rounding argument. -/
theorem global_certificate {d u : ℝ} (hJ : certJ d u ≠ 0) :
    8*certJ d u*(b0-boundaryF d (1/2-u)) =
      certK*(d-delta0)^2+u*certA1 d+u^2*certA2 d+768*certT*u^3*d^2 := by
  have hexpand : 8*certJ d u*(b0-boundaryF d (1/2-u)) =
      8*(300*kappa0-40)*certk0+
      (8*((300*kappa0-40)*certk1+(24-216*kappa0)*certk0)-15*h0*(24*kappa0-4))*d+
      certK*d^2+u*certA1 d+u^2*certA2 d+768*certT*u^3*d^2 := by
    unfold boundaryF certR
    rw [show (1/2:ℝ)-(1/2-u) = u by ring]
    field_simp [hJ]
    simp only [certJ, certB, certk0, certk1, certK, certA1, certA2,
      certA10, certA11, certA12, certA20, certA21]
    ring
  rw [hexpand, tangency_constant, tangency_linear]
  ring

theorem boundaryF_le_b0 {d p : ℝ} (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    boundaryF d p ≤ b0 := by
  let u : ℝ := 1/2-p
  have hu : 0 ≤ u ∧ u ≤ 1/2 := by dsimp [u]; constructor <;> linarith
  have hJ : 0 < certJ d u := by linarith [(certJ_bounds hd hu).1]
  have heq := global_certificate (ne_of_gt hJ)
  have hc := coefficient_minorants
  have hK : 0 ≤ certK := by linarith [hc.2.2.2.2.2.1]
  have hT : 0 ≤ certT := by linarith [hc.2.2.2.2.2.2.2.1]
  have hA1 : 0 ≤ certA1 d := le_of_lt (certA1_pos hd.1)
  have hA2 : 0 ≤ certA2 d := certA2_nonneg hd.1
  have hu0 : 0 ≤ u := hu.1
  have hnonneg : 0 ≤ certK*(d-delta0)^2+u*certA1 d+u^2*certA2 d+768*certT*u^3*d^2 := by
    positivity
  have hL : 0 ≤ 8*certJ d u*(b0-boundaryF d (1/2-u)) := by rw [heq]; exact hnonneg
  have hdiff : 0 ≤ b0-boundaryF d (1/2-u) :=
    (mul_nonneg_iff_of_pos_left (by positivity : 0 < 8*certJ d u)).mp hL
  have hpu : (1/2:ℝ)-u = p := by dsimp [u]; ring
  rw [hpu] at hdiff
  linarith

theorem boundaryF_binding : boundaryF delta0 (1/2) = b0 := by
  have hd : 0 ≤ delta0 ∧ delta0 ≤ 5/6 := by
    constructor <;> linarith [delta0_interval.1, delta0_interval.2]
  have hJ : 0 < certJ delta0 0 := by linarith [(certJ_bounds hd ⟨le_refl 0, by norm_num⟩).1]
  have heq := global_certificate (d := delta0) (u := 0) (ne_of_gt hJ)
  norm_num at heq
  have hdif : b0-boundaryF delta0 (1/2) = 0 :=
    heq.resolve_left (ne_of_gt hJ)
  linarith

theorem boundaryF_eq_iff {d p : ℝ} (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    boundaryF d p = b0 ↔ d = delta0 ∧ p = 1/2 := by
  constructor
  · intro he
    let u : ℝ := 1/2-p
    have hu : 0 ≤ u ∧ u ≤ 1/2 := by dsimp [u]; constructor <;> linarith
    have hu0 := hu.1
    have hJ : 0 < certJ d u := by linarith [(certJ_bounds hd hu).1]
    have heq := global_certificate (d := d) (u := u) (ne_of_gt hJ)
    have hpu : (1/2:ℝ)-u = p := by dsimp [u]; ring
    rw [hpu, he] at heq
    have hc := coefficient_minorants
    have hK : 0 < certK := by linarith [hc.2.2.2.2.2.1]
    have hT : 0 ≤ certT := by linarith [hc.2.2.2.2.2.2.2.1]
    have hA1 : 0 < certA1 d := certA1_pos hd.1
    have hA2 : 0 ≤ certA2 d := certA2_nonneg hd.1
    have ht0 : 0 ≤ 768*certT*u^3*d^2 := by positivity
    have ht1 : 0 ≤ u^2*certA2 d := by positivity
    have ht2 : 0 ≤ u*certA1 d := by positivity
    have ht3 : 0 ≤ certK*(d-delta0)^2 := by positivity
    have huA : u*certA1 d = 0 := by linarith
    have hsA : certK*(d-delta0)^2 = 0 := by linarith
    have hue : u = 0 := (mul_eq_zero.mp huA).resolve_right (ne_of_gt hA1)
    have hs : (d-delta0)^2 = 0 := (mul_eq_zero.mp hsA).resolve_left (ne_of_gt hK)
    constructor
    · nlinarith
    · dsimp [u] at hue; linarith
  · rintro ⟨rfl, rfl⟩
    exact boundaryF_binding

end Cycle25.Arithmetic
end
/- END ORIGINAL MODULE Cycle25.Arithmetic.GlobalBound -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.Adaptive ; sha256 dead38734fbacbd1f984dfa44909f845a63209e276524ad2e3aa23ee36a67a16 -/
section





namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Cycle25ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount

theorem balanced_adaptive_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance κplain ν C height q : ℝ) (i : ℕ),
      1< U → 51/100< a → 2*a-1≤3/4 → 0≤ε → ε≤1/1000 →
      7/10≤κplain → κplain≤3/4 → 0<ν → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) (q/(2*a-1)) κplain) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(rowCount (2*a-1) (q/(2*a-1)) κplain+
          159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    Cycle25DetectorFixedAmplitudeCount.fixed_amplitude_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance κplain ν C height q i hU ha hd hε hε' hk hk1 hν hC hh hf Label Slot _ B hne hq hmom
  have hδ : 0<2*a-1 := by linarith
  have hqb := HeckeDetectorFixedAmplitudeCount.batch_mean_bounds B hne (by linarith) q hq
  have hx : 0≤ q/(2*a-1) := div_nonneg hqb.1 hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
  have ht := cutoff_bounds hδ.le hd hx hx' hk hk1
  have hc' := hcount a ε (cutoff (2*a-1) (q/(2*a-1)) κplain) T allowance κplain ν C height q i
    hU ha hd hε hε' ht.1 ht.2 hk hk1 hν hC hh hf B hq hmom
  have he := max_at_cutoff hδ.le hd hx hx' hk hk1
  rw [he] at hc'
  exact hc'

end SevenEighths.Cycle25ProbeHighRowFamily
end
end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.Adaptive -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorEnergyInitialState ; sha256 bbd21e169c322784e435cf00e3d900d514618266c89cae982b5ad958e1220ba1 -/
section






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.Cycle25CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorEnergyInitialState Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open Cycle25CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional
local notation "O"=> HeckeFamily.O

def weighted_initialKeep (η:Character)(Q:Ideal O)(z:O):Prop:=
  z≠0 ∧ ¬FixedInducingRow η Q (fixedBadMask*idealGenerator 1) 1 z

def weighted_initialState (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1 ≤ U)(hδ:0 ≤ δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0 ≤ (Φ x).re)(hη:(η.modulus.absNorm:ℝ) ≤ U^δ):NaturalState U 0 bΦ where
  character:=η
  fixedModulus:=Q
  puncture:=1
  radial := {
    keep := weighted_initialKeep η Q
    profile := Φ
    scale := U
    scale_pos := zero_lt_one.trans_le hU
    nonneg := fun z => hp _ }
  rowWidth:=1
  characterWidth:=δ
  base_ge_one:=hU
  row_nonneg:=by norm_num
  character_nonneg:=hδ
  scale_eq:=by simp
  modulus_bound:=hη
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=hs
  row_ne_zero:=fun _ h=> h.1
  nonexceptional:=fun _ h=> h.2

lemma weighted_initialState_width (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1 ≤ U)(hδ:0 ≤ δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0 ≤ (Φ x).re)(hη:(η.modulus.absNorm:ℝ) ≤ U^δ):
    (weighted_initialState η Q Φ bΦ U δ hU hδ hs hp hη).width=1+δ:=rfl

def weighted_detectorProfiles (reverse:Bool)(j k:ℕ)(σ t:ℝ):Profiles (1/4) (9/4) where
  profile:=fun n=> detectorSchwartz reverse (if n=0 then j else k) σ t
  support:=by
    intro n x hx
    have he:(detectorSchwartz reverse (if n=0 then j else k) σ t:ℝ→ℂ)=
      HeckeInverseAmplification.twistProfile
        (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          ((HeckeDetectorRowwisePolynomial.logProfile^[if n=0 then j else k])
            HeckeDetectorDyadicProfiles.positiveAnnular)) σ
          (HeckeDetectorCoefficientTransfer.orientedFrequency reverse t):=by
      funext y;exact detectorSchwartz_apply _ _ _ _ _
    rw [he] at hx
    exact detector_profile_support _ _ _ _ hx

theorem weighted_radialMajorant_support_bound:
    ∃bΦ:ℝ,0< bΦ ∧ Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ:=by
  obtain ⟨b,hb⟩:=radialMajorant_compact.isCompact.bddAbove
  refine ⟨max 1 b,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x hx
  exact (hb (subset_tsupport _ hx)).trans (le_max_right _ _)

variable {D:Cycle25.Weighted.MomentData}

theorem weighted_source_label_modulus_eventually (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (η:Character)(δ:ℝ)(hδ:0<δ):
    ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d:ℝ,(1/200:ℝ) ≤ d→
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
         ≤ (Z^d)^δ:=by
  have hc:∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
         ≤ Z^((1/200)*δ):=by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (mul_pos (by norm_num) hδ)).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro label d hd
  apply (hz label).trans
  rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (mul_le_mul_of_nonneg_right hd hδ.le)

lemma weighted_source_keep_iff (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character)(u:FreeRow):
    weighted_initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val↔¬weighted_sourceExceptional F η u:=by
  exact and_iff_right u.property.1

lemma weighted_source_fixed_gates (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character):
    internalQ (weighted_sourceFixedIdeal F) η≠0 ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ F.modulus ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ η.modulus ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ Ideal.span {(72:O)}:=
  ⟨internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero F) η,
    inf_le_left.trans (weighted_sourceFixedIdeal_le_modulus F),inf_le_right,
    inf_le_left.trans (weighted_sourceFixedIdeal_le_72 F)⟩

end SevenEighths.Cycle25CenteredMomentDetectorEnergyInitialState

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.MomentDetectorEnergyInitialState -/
