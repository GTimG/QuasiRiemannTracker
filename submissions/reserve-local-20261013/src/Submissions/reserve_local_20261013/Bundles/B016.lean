/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.reserve_local_20261013.Bundles.B011
import Submissions.reserve_local_20261013.Bundles.B012
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CanonicalErrorGaussian
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.StageReserveBounded
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAnnularMajorant
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicAssembly
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FixedRay

/- BEGIN ORIGINAL MODULE Analytic.FixedPhaseDictionary ; sha256 8ce7fa9e9d196c454872864c65b60d25433c01e542945103816ff35df6397427 -/
section



/-! The reciprocity factors from an arbitrary active common support belong
to one fixed finite character dictionary of modulus twelve. The dictionary
is chosen before the primes, exponents, and transformed row. -/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Local44.Analytic
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open HeckeFamily HeckeRowClosure CenteredMomentFixedRay CenteredMomentCommonSupport
open RayFourExpansion

local notation "O" => ActualEisensteinCubic.O

theorem phase_monoid_periodic (p : O) (hp : Supported (Ideal.span {p})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(4 : O)})
      (reciprocityPhaseMonoid p hp) := by
  intro x y hxy
  exact sexticReciprocityPhase_congr_right p x y (Ideal.mem_span_singleton.mp hxy)

def phaseRayCharacter (p : O) (hp : Supported (Ideal.span {p})) : RayCharacter :=
  residueRow (Ideal.span {(4 : O)}) (reciprocityPhaseMonoid p hp)
    (phase_monoid_periodic p hp)

theorem phaseRayCharacter_apply (p n : O) (hp : Supported (Ideal.span {p}))
    (hn : Supported (Ideal.span {n})) :
    rayCharacter (phaseRayCharacter p hp) n = sexticReciprocityPhase p n := by
  unfold rayCharacter phaseRayCharacter
  rw [residueRow_mk, ite_eq_left
    (isUnit_residue_of_coprime 4 n (supported_coprime_four n hn))]
  rfl

theorem ray_product_apply {ι : Type*} (s : Finset ι) (χ : ι → RayCharacter)
    (n : O) (hn : Supported (Ideal.span {n})) :
    rayCharacter (∏ i ∈ s, χ i) n = ∏ i ∈ s, rayCharacter (χ i) n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, rayCharacter]
    exact MulChar.one_apply (isUnit_residue_of_coprime 4 n (supported_coprime_four n hn))
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha, rayCharacter, MulChar.mul_apply] at ih ⊢
    rw [ih]

theorem ray_power_apply (χ : RayCharacter) (k : ℕ) (n : O)
    (hn : Supported (Ideal.span {n})) :
    rayCharacter (χ ^ k) n = rayCharacter χ n ^ k := by
  have hu := isUnit_residue_of_coprime 4 n (supported_coprime_four n hn)
  exact MulChar.pow_apply_coe χ k hu.unit

/-- This finite set does not depend on any arithmetic common-support label. -/
def fixedPhaseDictionary : Finset Character :=
  Finset.univ.image primaryRayCharacter

theorem reciprocity_product_in_fixed_dictionary {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i})) (t : ι → ℕ) :
    ∃ η ∈ fixedPhaseDictionary,
      η.modulus = Ideal.span {(12 : O)} ∧
      ∀ n : O, Supported (Ideal.span {n}) → goodLambda ^ 2 ∣ n-1 →
        elementCoeff η n = ∏ i, sexticReciprocityPhase (p i) n ^ t i := by
  let χ : RayCharacter := ∏ i, phaseRayCharacter (p i) (hp i) ^ t i
  refine ⟨primaryRayCharacter χ, ?_, primaryRayCharacter_modulus χ, ?_⟩
  · exact Finset.mem_image.mpr ⟨χ, Finset.mem_univ _, rfl⟩
  · intro n hn hnp
    rw [primaryRayCharacter_primary χ n hn hnp]
    dsimp only [χ]
    rw [ray_product_apply _ _ n hn]
    apply Finset.prod_congr rfl
    intro i _
    rw [ray_power_apply _ _ n hn, phaseRayCharacter_apply (p i) n (hp i) hn]

theorem fixedPhaseDictionary_modulus (η : Character) (hη : η ∈ fixedPhaseDictionary) :
    η.modulus = Ideal.span {(12 : O)} := by
  obtain ⟨χ, _, rfl⟩ := Finset.mem_image.mp hη
  exact primaryRayCharacter_modulus χ

/-- The original fixed-inducing ideal already contains the required modulus;
no enlargement of the exceptional set is needed for the reciprocity phases. -/
theorem fixedPhaseDictionary_fixedQ (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72 : O)}) (η : Character) (hη : η ∈ fixedPhaseDictionary) :
    Q ≤ η.modulus := by
  rw [fixedPhaseDictionary_modulus η hη]
  exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨6, by norm_num⟩)

#print axioms reciprocity_product_in_fixed_dictionary
#print axioms fixedPhaseDictionary_fixedQ

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.FixedPhaseDictionary -/

/- BEGIN ORIGINAL MODULE Analytic.JointErrorGaussian ; sha256 991e0bcc6f753d9685772ad210fe7e927ca06c26f27a03385199998db3bd03ac -/
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

theorem refined_error_gaussian_from_bands
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
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ):
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
    ∀K sigma delta reserve cost asource:ℝ,0< K → 0≤ sigma → 1≤ cost → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=1 ∨ k=6 ∨ k=7) →
    sigma/6≤ Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^k),
    ∀(υ:Character)(v0:ℝ),
    (υ.modulus.absNorm:ℝ)≤ cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
    Ready input ((R0*C)*(Ideal.span {prime})^k) Kerror Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input ((R0*C)*(Ideal.span {prime})^k) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    (∀q∈liveLabels input.η Scols β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀dyad:SourceBlocks q.val.1 q.val.2 U Kerror (frequencyRadius (nominal input Kerror) Z ξ)
        (sourceRadius input),
      physicalBlock input.η input.t (activeSource Scols β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U
        (frequencyRadius (nominal input Kerror) Z ξ)
        (partRows false input.η χ₀ (internalQ Q η₀) m q.val.1 q.val.2 U
          (frequencyRadius (nominal input Kerror) Z ξ))
        CenteredMomentFirstAmplificationChoice.ballProfile Kerror (fun i=>(dyad i:ℤ))≠0 →
      ∀χ:RayCharacter,Real.logb Z (dyadicScale (dyad 1))+
        Real.logb Z ((family q U χ).modulus.absNorm:ℝ)≤ Mcap) →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let Echild:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+(sigma+errorRemoval prime Z k-errorMoving prime Z k)/6+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3+κ*mesh))
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^k) seed CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc v0
        εsrc (seed.absNorm:ℝ)
        (seededFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Kerror v0
          (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) Echild Echild r (∏i,input.lo i) a (seed.absNorm:ℝ)
          (dc+degree+4*n) (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,hmain⟩:=
    refined_error_uniform_child (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
      N lower upper a0 Bcap Bcap θsource hlower ha0 hθsource
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hgauss⟩:=
    actual_nested_subsets_seeded_gaussian_power a b haPlain hbPlain lows highs hhighs
      CenteredMomentFirstAmplificationChoice.ballProfile (dc+degree+4*n) (dc+degree+4*n)
      N upper (max 1 b) (max 1 b) hupper (le_max_left _ _) (le_max_left _ _)
      εsrc δsrc θsrc Bcap Bseed ξ saving hεsrc hδsrc hθsrc hBcap hξ
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Zm,hZm,hm⟩:=hmain η₀
  obtain ⟨Kc,hKc,hevent⟩:=hgauss (internalQ Q η₀) hQ0 hQt hQ72
  obtain ⟨Zg,hZg⟩:=Filter.eventually_atTop.1 hevent
  refine ⟨Kc,hKc,max Zm Zg,lt_of_lt_of_le hZm (le_max_left _ _),?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ v0 hυ input hinput
  subst input
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip
    hcap hMdecl hclip hasourceFactor Scols β hScols hβ
  let input:=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let Km:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
  have hZmZ:Zm≤ Z:=(le_max_left _ _).trans hZ
  have hgZ:=hZg Z ((le_max_right _ _).trans hZ)
  have hz:1< Z:=hgZ.1
  have hP:∀i,1≤ input.P i:=by
    intro i
    change 1≤ src.P i.val.val
    rw [hmatch.scale]
    exact Real.one_le_rpow hz.le (hw i.val.val)
  have hcardInput:Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤ N:=
    (child_card Bp.val).trans ((child_card B.val).trans hcard)
  have hmass:mass input≤ mass src:=
    (child_mass (activeInput (child src C R0 B τ t)) ((Ideal.span {prime})^k) (R0*C) Bp υ v0).trans
      (child_mass src C R0 B τ t)
  have hsource:=hgZ.2 ⟨CenteredMomentCommonProfile.liveIndices B.val,CenteredMomentCommonProfile.liveIndices Bp.val⟩ input p
    (fun i=> hloSrc i.val.val) (fun i=> hhiSrc i.val.val) hP hp₁.symm hp₂.symm (mass src)
    hupperSrc hcardInput hb1 hb2 hb1max hb2max hmass
    ((R0*C)*(Ideal.span {prime})^k) seed hready.puncture_ne hseed hseed0 hseedcap hready.source_nonneg hready.source_cap
    hready.conductor_cap hready.puncture_cap
  change Scols=finiteColumns (Fintype.piFinset input.pools) at hScols
  change β=coefficient input ((R0*C)*(Ideal.span {prime})^k) seed at hβ
  dsimp only at hsource
  subst Scols β
  obtain ⟨family,hfamily,hbound⟩:=hsource
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm0 hml hm2 hwidth r hr1 hr2 hr3 hr4
  let Ec:=CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+(sigma+errorRemoval prime Z k-errorMoving prime Z k)/6+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3+κ*mesh))
  have hEc:0≤ Ec:=CenteredMomentEnergyChildEnvelopeFitting.coefficient_nonneg
    Cc C₀ C₁ p T height (dc+degree+4*n) Z _ hCc.le hC₀ hC₁ hheight (zero_le_one.trans hz.le)
  have hpzero (j:Fin 2):p.profile j 0=0:=by
    by_contra hn
    exact (not_le_of_gt haPlain) ((p.support j hn).1)
  have hz1:input.W₁ 0=0:=by change src.W₁ 0=0;rw [←hp₁];exact hpzero 0
  have hz2:input.W₂ 0=0:=by change src.W₂ 0=0;rw [←hp₂];exact hpzero 1
  have hlowerInput:lower ≤ input.lower:=hlowerSrc
  have hplain₁:∀x,input.W₁ x≠0→a≤ x:=by
    intro x hx
    change src.W₁ x≠0 at hx
    rw [←hp₁] at hx
    exact (p.support 0 hx).1
  have hplain₂:∀x,input.W₂ x≠0→a≤ x:=by
    intro x hx
    change src.W₂ x≠0 at hx
    rw [←hp₂] at hx
    exact (p.support 1 hx).1
  have hlowerBeta (I:Ideal O)
      (hI:coefficient input ((R0*C)*(Ideal.span {prime})^k) seed I≠0):
      asource*volume input≤(I.absNorm:ℝ):=by
    exact (mul_le_mul_of_nonneg_right hasourceFactor (volume_pos input).le).trans
      (CenteredMomentSecondInputCapacitySource.actual_lower_support N lower a hlower haPlain
        input hcardInput hlowerInput hplain₁ hplain₂ _ seed I hI)
  apply hbound χ₀ m hm0 hml hm2 Km (nominal input Km) hready.scale_pos hready.volume_cap
    hready.nominal_cap (le_refl _) hready.frequency_pos hready.frequency_cap
    (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k))
    (mul_pos (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _))
    Ec Ec hEc hEc ?_ ?_ r hr1 hr2 hr3 hr4
  all_goals
    intro q hq U dyad hphysical D0 hD0 hD0cap hD0sq χ v B₂ hB₂ alloc halloc
    have hqp:=q.property
    have hg:=actual_common_gates input ((R0*C)*(Ideal.span {prime})^k) seed hseed hz1 hz2 q.val.1 q.val.2 hqp
    have hs:=commonLabels_supported (activeSource _ _) _ _ q.property
  · exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
      K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ v0 hυ input rfl
      _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
      hlowerBeta hphysical (family q U) (hfamily q U) χ (hwidth q hq U dyad hphysical χ)
      q.val.1 ((R0*C)*(Ideal.span {prime})^k) (Or.inl rfl) hready.puncture_ne hready.puncture_cap
      (hg.2.2.2.2.2.1.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
      hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  · exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
      K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ v0 hυ input rfl
      _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
      hlowerBeta hphysical (family q U) (hfamily q U) χ (hwidth q hq U dyad hphysical χ)
      q.val.2 ((R0*C)*(Ideal.span {prime})^k) (Or.inr rfl) hready.puncture_ne hready.puncture_cap
      (hg.2.2.2.2.2.2.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
      hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip

#print axioms refined_error_gaussian_from_bands
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointErrorGaussian -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstAnnularRows ; sha256 2c1d9285a8a21ced7a0e7c4c6cb5d50b1c1db6a4cce74d862c57df2cdfce0344 -/
section




/-! Exact row restriction for the literal first dyadic window. Its
annular majorant is used only on the rows where that window survives. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstWholeKernel
open CenteredMomentCanonicalFirst CenteredMomentLogDyadic CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

def firstAnnularRows (rows : Finset O) (H : ℝ) : Finset O :=
  rows.filter (fun z => H/4 ≤ ‖eisEmbedding z‖^2 ∧ ‖eisEmbedding z‖^2 ≤ H)

lemma first_logAnnulus_zero_off (z : O) (hz : z ≠ 0) (H : ℝ) (hH : 0 < H)
    (hoff : ¬(H/4 ≤ ‖eisEmbedding z‖^2 ∧ ‖eisEmbedding z‖^2 ≤ H)) :
    logAnnulus (Real.log (‖eisEmbedding z‖^2/H)) = 0 := by
  have hn : 0 < ‖eisEmbedding z‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (eisEmbedding_ne_zero hz))
  rw [logAnnulus_log _ H hn hH,Complex.ofReal_eq_zero]
  by_cases hlo : H/4 ≤ ‖eisEmbedding z‖^2
  · apply annulus_zero_high
    exact (one_le_div hH).mpr (le_of_not_ge (fun hhi => hoff ⟨hlo,hhi⟩))
  · apply annulus_zero_low
    apply (div_le_iff₀ hH).mpr
    linarith [lt_of_not_ge hlo]

theorem firstAnnularRows_majorant (rows : Finset O) (H : ℝ) (hH : 0 < H) :
    ∀ z ∈ firstAnnularRows rows H,
      1 ≤ (CenteredMomentFirstAnnularMajorant.profile (‖eisEmbedding z‖^2/H)).re := by
  intro z hz
  obtain ⟨_,hlo,hhi⟩ := Finset.mem_filter.mp hz
  rw [CenteredMomentFirstAnnularMajorant.scaled_majorant H _ hH hlo hhi]

theorem firstAnnularRows_nonzero (rows : Finset O) (H : ℝ)
    (hrows : ∀ z ∈ rows,z ≠ 0) : ∀ z ∈ firstAnnularRows rows H,z ≠ 0 :=
  fun z hz => hrows z (Finset.mem_filter.mp hz).1

theorem first_physical_block_annular_rows
    (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (hrows : ∀ z ∈ rows,z ≠ 0)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (hV : V 1 = logAnnulus)
    (K K₀ H₀ A₀ B₀ : ℝ) (hH₀ : 0 < H₀) :
    block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀ =
      block η m A t S c C D hC hD E (firstAnnularRows rows H₀) W V K K₀ H₀ A₀ B₀ := by
  unfold block firstAnnularRows
  dsimp only
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs with hband
  · rfl
  · have hzero := first_logAnnulus_zero_off z (hrows z hz) H₀ hH₀ hband
    simp only [windows,hV,hzero,mul_zero,zero_mul,ite_self,Finset.sum_const_zero]

theorem FirstJointLabel.sourceBlock_annular_rows {ι : Type*} [Fintype ι]
    (q : FirstJointLabel ι) (t : ℝ) (rows : Finset O) (hrows : ∀ z ∈ rows,z ≠ 0)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (hV : V 1 = logAnnulus)
    (K K₀ H₀ A₀ B₀ : ℝ) (hH₀ : 0 < H₀) :
    q.sourceBlock t rows W V K K₀ H₀ A₀ B₀ =
      q.sourceBlock t (firstAnnularRows rows H₀) W V K K₀ H₀ A₀ B₀ :=
  first_physical_block_annular_rows _ _ _ _ _ _ _ _ _ _ _ rows hrows W V hV _ _ _ _ _ hH₀

theorem first_dyadic_annular_radius (K R A B : ℝ)
    (n : CenteredMomentFirstPhysicalDyadicAssembly.Blocks K R A B) :
    0 < dyadicScale (n 1) ∧ dyadicScale (n 1) ≤ 4*R :=
  ⟨dyadicScale_pos _,retained_scale_le R _
    (CenteredMomentFirstPhysicalDyadicAssembly.block_retained K R A B n)⟩

#print axioms FirstJointLabel.sourceBlock_annular_rows
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstAnnularRows -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstLedger ; sha256 3f08dc3af9cc482d4cdc60dfedaf57b8fbec9b14779d032fd0e5d891b9eba7e9 -/
section




/-! Source scalar normalization and the first joint exponent ledger.
Möbius and ray coefficients act as contractions on the joint label sum. -/
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

theorem first_ray_coefficient_norm (χ ξ : RayCharacter) :
    ‖pairCoeff firstPhaseTable χ ξ‖ ≤ 1 := by
  apply pairCoeff_norm_le
  intro u v
  unfold firstPhaseTable QuadraticAllOddCRT.quadraticRaySign
  split_ifs <;> norm_num

namespace FirstJointLabel

theorem sourceWeight_norm_le_scalar (s : FirstJointLabel ι) (K A₀ B₀ : ℝ)
    (i : s.SourceIndex) :
    ‖s.sourceWeight K A₀ B₀ i‖ ≤ ‖scalar s.C s.D s.hC s.E K A₀ B₀‖ := by
  simp only [sourceWeight, norm_mul]
  exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (first_ray_coefficient_norm _ _)).trans
    (mul_le_of_le_one_right (norm_nonneg _) (QuadraticInitialBound.norm_ideal_moebius_le_one _))

theorem sourceWeight_contraction (s : FirstJointLabel ι) (K A₀ B₀ F : ℝ)
    (hF : 0 < F) (hscalar : ‖scalar s.C s.D s.hC s.E K A₀ B₀‖ ≤ F)
    (i : s.SourceIndex) : ‖(F : ℂ)⁻¹ * s.sourceWeight K A₀ B₀ i‖ ≤ 1 := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hF]
  calc
    _ ≤ F⁻¹ * F := mul_le_mul_of_nonneg_left
      ((s.sourceWeight_norm_le_scalar K A₀ B₀ i).trans hscalar) (inv_nonneg.mpr hF.le)
    _ = 1 := inv_mul_cancel₀ hF.ne'

/-- The literal scalar after central normalization of both residual
polynomials. This is the source of the first outside factor. -/
theorem normalized_scalar_bound (s : FirstJointLabel ι)
    (K A₀ B₀ a T window : ℝ)
    (hK : 0 < K) (hA : 0 < A₀) (hB : 0 < B₀) (ha : 0 < a) (hT : 0 < T)
    (hl : a*T ≤ (s.C.absNorm : ℝ)*Real.exp window*A₀)
    (hr : a*T ≤ (s.D.absNorm : ℝ)*Real.exp window*B₀) :
    ‖scalar s.C s.D s.hC s.E K A₀ B₀‖ /
      Real.sqrt ((s.C.absNorm : ℝ)*s.D.absNorm) ≤
      (Real.exp window/a)*K /
        (T*‖eisEmbedding s.puncture‖^2*‖eisEmbedding (activeConductor s.C s.D)‖) := by
  have hC : 0 < (s.C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hC.1)
  have hD : 0 < (s.D.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hD.1)
  have hroot : 0 < Real.sqrt ((s.C.absNorm : ℝ)*s.D.absNorm) :=
    Real.sqrt_pos.mpr (mul_pos hC hD)
  have hh := scalar_volume_bound s.C s.D s.hC s.E K A₀ B₀ a T window
    hK hA hB ha.le hT.le hl hr
  have hs := div_le_div_of_nonneg_right hh
    (show 0 ≤ a*T*Real.sqrt ((s.C.absNorm : ℝ)*s.D.absNorm) by positivity)
  unfold puncture
  convert hs using 1 <;> field_simp

def leftWidth (s : FirstJointLabel ι) (Z : ℝ) : ℝ := Real.logb Z (s.C.absNorm : ℝ)
def rightWidth (s : FirstJointLabel ι) (Z : ℝ) : ℝ := Real.logb Z (s.D.absNorm : ℝ)
def radicalWidth (s : FirstJointLabel ι) (Z : ℝ) : ℝ :=
  Real.logb Z ((commonRadical s.C s.D).absNorm : ℝ)
def activeWidth (s : FirstJointLabel ι) (Z : ℝ) : ℝ :=
  Real.logb Z ((Ideal.span {activeConductor s.C s.D}).absNorm : ℝ)
def punctureWidth (s : FirstJointLabel ι) (Z : ℝ) : ℝ :=
  Real.logb Z (‖eisEmbedding s.puncture‖^2)
def leftAllowance (s : FirstJointLabel ι) (Z : ℝ) : ℝ :=
  max (3*s.leftWidth Z-5*s.rightWidth Z-s.activeWidth Z) 0/6
def rightAllowance (s : FirstJointLabel ι) (Z : ℝ) : ℝ :=
  max (3*s.rightWidth Z-5*s.leftWidth Z-s.activeWidth Z) 0/6

theorem actual_joint_allowance (s : FirstJointLabel ι) (Z : ℝ) (hZ : 1 < Z) :
    s.leftAllowance Z+s.rightAllowance Z ≤
      s.leftWidth Z+s.rightWidth Z-2*s.radicalWidth Z-s.activeWidth Z :=
  actual_canonical_common_support_allowance s.C s.D s.hC s.hD s.hCD Z hZ

/-- Exact arithmetic norms identify the first outside power. -/
theorem outside_rpow_identity (s : FirstJointLabel ι) (Z M A : ℝ) (hZ : 1 < Z) :
    Z^M / (Z^A*‖eisEmbedding s.puncture‖^2*‖eisEmbedding (activeConductor s.C s.D)‖) =
      Z^(M-A-s.activeWidth Z/2-s.punctureWidth Z) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have he : 0 < ‖eisEmbedding s.puncture‖^2 := sq_pos_of_pos (norm_pos_iff.mpr
    (eisEmbedding_ne_zero (supported_element_ne_zero _ (subsetGenerator_supported s.C s.D s.hC s.E))))
  have hr : 0 < ‖eisEmbedding (activeConductor s.C s.D)‖ := norm_pos_iff.mpr
    (eisEmbedding_ne_zero (supported_element_ne_zero _ (activeConductor_supported s.C s.D s.hC)))
  have hp : Z^(s.punctureWidth Z) = ‖eisEmbedding s.puncture‖^2 :=
    Real.rpow_logb hz hZ.ne' he
  have hR : Z^(s.activeWidth Z/2) = ‖eisEmbedding (activeConductor s.C s.D)‖ := by
    rw [activeWidth, ← eisEmbedding_norm_sq_eq_absNorm_span, div_eq_mul_one_div,
      Real.rpow_mul hz.le, Real.rpow_logb hz hZ.ne' (sq_pos_of_pos hr),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]
  rw [Real.rpow_sub hz, Real.rpow_sub hz, Real.rpow_sub hz, hp, hR]
  ring

theorem normalized_scalar_rpow_bound (s : FirstJointLabel ι)
    (Z M A A₀ B₀ a window : ℝ) (hZ : 1 < Z)
    (hA : 0 < A₀) (hB : 0 < B₀) (ha : 0 < a)
    (hl : a*Z^A ≤ (s.C.absNorm : ℝ)*Real.exp window*A₀)
    (hr : a*Z^A ≤ (s.D.absNorm : ℝ)*Real.exp window*B₀) :
    ‖scalar s.C s.D s.hC s.E (Z^M) A₀ B₀‖ /
      Real.sqrt ((s.C.absNorm : ℝ)*s.D.absNorm) ≤
      (Real.exp window/a)*Z^(M-A-s.activeWidth Z/2-s.punctureWidth Z) := by
  have hh := s.normalized_scalar_bound (Z^M) A₀ B₀ a (Z^A) window
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hA hB ha
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hl hr
  rw [← s.outside_rpow_identity Z M A hZ]
  convert hh using 1
  ring

end FirstJointLabel

/-- The joint targets close before any count of first labels. -/
theorem first_joint_exponent_budget (M A c d p R E Bc Bd : ℝ)
    (hallow : Bc+Bd ≤ c+d-2*p-R) :
    (M-A-R/2-E) + ((p+A-c+R+E+Bc)+(p+A-d+R+E+Bd))/2 ≤ M := by
  linarith

theorem first_joint_rpow_budget (Z M A c d p R E Bc Bd : ℝ) (hZ : 1 ≤ Z)
    (hallow : Bc+Bd ≤ c+d-2*p-R) :
    Z^(M-A-R/2-E) * Real.sqrt (Z^(p+A-c+R+E+Bc)) *
      Real.sqrt (Z^(p+A-d+R+E+Bd)) ≤ Z^M := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hz.le, ← Real.rpow_mul hz.le,
    ← Real.rpow_add hz, ← Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hh := first_joint_exponent_budget M A c d p R E Bc Bd hallow
  linarith

theorem actual_first_joint_rpow_budget (s : FirstJointLabel ι) (Z M A : ℝ) (hZ : 1 < Z) :
    Z^(M-A-s.activeWidth Z/2-s.punctureWidth Z) *
      Real.sqrt (Z^(s.radicalWidth Z+A-s.leftWidth Z+s.activeWidth Z+s.punctureWidth Z+s.leftAllowance Z)) *
      Real.sqrt (Z^(s.radicalWidth Z+A-s.rightWidth Z+s.activeWidth Z+s.punctureWidth Z+s.rightAllowance Z)) ≤
      Z^M :=
  first_joint_rpow_budget Z M A _ _ _ _ _ _ _ hZ.le (s.actual_joint_allowance Z hZ)



namespace FirstJointLabel

def leftTargetWidth (s : FirstJointLabel ι) (Z A : ℝ) : ℝ :=
  s.radicalWidth Z+A-s.leftWidth Z+s.activeWidth Z+s.punctureWidth Z+s.leftAllowance Z

def rightTargetWidth (s : FirstJointLabel ι) (Z A : ℝ) : ℝ :=
  s.radicalWidth Z+A-s.rightWidth Z+s.activeWidth Z+s.punctureWidth Z+s.rightAllowance Z

/-- A dyadic sector allows label-dependent common ideals. The support
bounds and geometric norm caps give one scalar cap for the entire sector. -/
theorem sector_scalar_cap (s q : FirstJointLabel ι)
    (Z M A δ A₀ B₀ a window : ℝ) (hZ : 1 < Z)
    (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) (ha : 0 < a)
    (hl : a*Z^A ≤ (s.C.absNorm : ℝ)*Real.exp window*A₀)
    (hr : a*Z^A ≤ (s.D.absNorm : ℝ)*Real.exp window*B₀)
    (hNC : (s.C.absNorm : ℝ) ≤ Z^δ*(q.C.absNorm : ℝ))
    (hND : (s.D.absNorm : ℝ) ≤ Z^δ*(q.D.absNorm : ℝ))
    (hscalarWidth : q.activeWidth Z/2+q.punctureWidth Z ≤
      s.activeWidth Z/2+s.punctureWidth Z) :
    ‖scalar s.C s.D s.hC s.E (Z^M) A₀ B₀‖ ≤
      (Real.exp window/a)*Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z+δ)*
        Real.sqrt ((q.C.absNorm : ℝ)*q.D.absNorm) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hCs : 0 < (s.C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hC.1)
  have hDs : 0 < (s.D.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hD.1)
  have hroot := Real.sqrt_le_sqrt (mul_le_mul hNC hND hDs.le (by positivity))
  rw [show (Z^δ*(q.C.absNorm : ℝ))*(Z^δ*(q.D.absNorm : ℝ)) =
    (Z^δ)^2*((q.C.absNorm : ℝ)*q.D.absNorm) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.rpow_nonneg hz.le _)] at hroot
  have hout : Z^(M-A-s.activeWidth Z/2-s.punctureWidth Z) ≤
      Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z) :=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hs := (div_le_iff₀ (Real.sqrt_pos.mpr (mul_pos hCs hDs))).mp
    (s.normalized_scalar_rpow_bound Z M A A₀ B₀ a window hZ hA₀ hB₀ ha hl hr)
  calc
    _ ≤ ((Real.exp window/a)*Z^(M-A-s.activeWidth Z/2-s.punctureWidth Z))*
        Real.sqrt ((s.C.absNorm : ℝ)*s.D.absNorm) := hs
    _ ≤ ((Real.exp window/a)*Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z))*
        (Z^δ*Real.sqrt ((q.C.absNorm : ℝ)*q.D.absNorm)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hout (by positivity)) hroot
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_add hz]; ring

end FirstJointLabel

/-- Converting a sum of normalized energies to raw energy keeps the same
index set. This is a monotonicity step, not a count of labels. -/
theorem joint_raw_energy_from_normalized {Λ : Type*} (labels : Finset Λ)
    (energy norm : Λ → ℝ) (T NC E : ℝ) (hT : 0 < T) (hNC : 0 < NC)
    (hnorm : ∀ l ∈ labels, NC ≤ norm l) (he : ∀ l ∈ labels, 0 ≤ energy l)
    (hjoint : (∑ l ∈ labels, (norm l/T)*energy l) ≤ E) :
    (∑ l ∈ labels, energy l) ≤ (T/NC)*E := by
  have hle : (NC/T)*(∑ l ∈ labels, energy l) ≤ E := by
    rw [Finset.mul_sum]
    apply le_trans _ hjoint
    exact Finset.sum_le_sum (fun l hl => mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hnorm l hl) hT.le) (he l hl))
  have hh := mul_le_mul_of_nonneg_left hle (show 0 ≤ T/NC by positivity)
  convert hh using 1
  field_simp


namespace FirstJointLabel

theorem leftEnergy_nonneg (s : FirstJointLabel ι) (t : ℝ)
    (U : 𝓢(ℝ, ℂ)) (H : ℝ) (hH : 0 < H)
    (hU : ∀ z : O, 0 ≤ (U (‖eisEmbedding z‖^2/H)).re) :
    0 ≤ s.leftEnergy t U H := by
  simpa only [Finset.sum_empty] using
    s.finite_left_energy t U H hH ∅ hU (by simp)

theorem rightEnergy_nonneg (s : FirstJointLabel ι) (t : ℝ)
    (U : 𝓢(ℝ, ℂ)) (H : ℝ) (hH : 0 < H)
    (hU : ∀ z : O, 0 ≤ (U (‖eisEmbedding z‖^2/H)).re) :
    0 ≤ s.rightEnergy t U H := by
  simpa only [Finset.sum_empty] using
    s.finite_right_energy t U H hH ∅ hU (by simp)

end FirstJointLabel

theorem joint_first_raw_left_from_normalized {Λ : Type*}
    (labels : Finset Λ) (s : Λ → FirstJointLabel ι) (t : Λ → ℝ)
    (U : Λ → 𝓢(ℝ, ℂ)) (H : Λ → ℝ)
    (hH : ∀ l ∈ labels, 0 < H l)
    (hU : ∀ l ∈ labels, ∀ z : O, 0 ≤ (U l (‖eisEmbedding z‖^2/H l)).re)
    (T NC E : ℝ) (hT : 0 < T) (hNC : 0 < NC)
    (hnorm : ∀ l ∈ labels, NC ≤ ((s l).C.absNorm : ℝ))
    (hjoint : (∑ l ∈ labels, (((s l).C.absNorm : ℝ)/T)*
      (s l).leftEnergy (t l) (U l) (H l)) ≤ E) :
    (∑ l ∈ labels, (s l).leftEnergy (t l) (U l) (H l)) ≤ (T/NC)*E :=
  joint_raw_energy_from_normalized labels _ _ T NC E hT hNC hnorm
    (fun l hl => (s l).leftEnergy_nonneg (t l) (U l) (H l) (hH l hl) (hU l hl)) hjoint

theorem joint_first_raw_right_from_normalized {Λ : Type*}
    (labels : Finset Λ) (s : Λ → FirstJointLabel ι) (t : Λ → ℝ)
    (U : Λ → 𝓢(ℝ, ℂ)) (H : Λ → ℝ)
    (hH : ∀ l ∈ labels, 0 < H l)
    (hU : ∀ l ∈ labels, ∀ z : O, 0 ≤ (U l (‖eisEmbedding z‖^2/H l)).re)
    (T ND E : ℝ) (hT : 0 < T) (hND : 0 < ND)
    (hnorm : ∀ l ∈ labels, ND ≤ ((s l).D.absNorm : ℝ))
    (hjoint : (∑ l ∈ labels, (((s l).D.absNorm : ℝ)/T)*
      (s l).rightEnergy (t l) (U l) (H l)) ≤ E) :
    (∑ l ∈ labels, (s l).rightEnergy (t l) (U l) (H l)) ≤ (T/ND)*E :=
  joint_raw_energy_from_normalized labels _ _ T ND E hT hND hnorm
    (fun l hl => (s l).rightEnergy_nonneg (t l) (U l) (H l) (hH l hl) (hU l hl)) hjoint

/-- Raw common energies scale by the residual volume T/NC. -/
theorem centered_energy_root_identity (T NC ND E₁ E₂ : ℝ)
    (hT : 0 ≤ T) (hNC : 0 < NC) (hND : 0 < ND) :
    Real.sqrt ((T/NC)*E₁) * Real.sqrt ((T/ND)*E₂) =
      (T/Real.sqrt (NC*ND))*(Real.sqrt E₁*Real.sqrt E₂) := by
  rw [Real.sqrt_mul (div_nonneg hT hNC.le), Real.sqrt_mul (div_nonneg hT hND.le)]
  have hh : Real.sqrt (T/NC)*Real.sqrt (T/ND) = T/Real.sqrt (NC*ND) := by
    rw [←Real.sqrt_mul (div_nonneg hT hNC.le),
      show (T/NC)*(T/ND)=T^2/(NC*ND) by ring,
      Real.sqrt_div (sq_nonneg T), Real.sqrt_sq hT]
  calc
    _ = (Real.sqrt (T/NC)*Real.sqrt (T/ND))*(Real.sqrt E₁*Real.sqrt E₂) := by ring
    _ = _ := by rw [hh]

/-- Automatic scalar contraction and central normalization, with the
complete joint common-energy sums still inside the hypotheses. -/
theorem joint_first_centered_blocks_from_scalar_cap
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (Mwin : Fin 4 → ℝ) (hMwin : ∀ i, 0 ≤ Mwin i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ Mwin i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (decay P₁ P₂ J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
      (t K K₀ H₀ A₀ B₀ : Λ → ℝ),
      (∀ z ∈ rows, z ≠ 0) →
      (∀ l, 0 < K l) → (∀ l, 0 < K₀ l) → (∀ l, 0 < H₀ l) →
      (∀ l, 0 < A₀ l) → (∀ l, 0 < B₀ l) →
      ∀ F T NC ND : ℝ, 0 < F → 0 < T → 0 < NC → 0 < ND →
      (∀ l ∈ labels, ‖scalar (s l).C (s l).D (s l).hC (s l).E (K l) (A₀ l) (B₀ l)‖ ≤ F) →
      (∀ l ∈ labels, ‖V 0 ((s l).sourceRowLog (K l) (K₀ l))‖ ≤ 1) →
      (∀ l ∈ labels, ∀ z ∈ rows, ‖V 1 (Real.log (‖eisEmbedding z‖ ^ 2 / H₀ l))‖ ≤ 1) →
      ∀ (U : ((l : Λ) × (s l).SourceIndex) → 𝓢(ℝ, ℂ))
        (H : ((l : Λ) × (s l).SourceIndex) → ℝ),
      (∀ k ∈ firstSourceLabels labels s, 0 < H k) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z : O,
        0 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z ∈ rows,
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
        (s l).sourceBlock (t l) rows W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l)‖ / T ≤
          C * (F/Real.sqrt (NC*ND)) * (Real.sqrt E₁ * Real.sqrt E₂) := by
  obtain ⟨C, hC, hc⟩ := joint_first_blocks_from_common_energy (ι := ι) W V Mwin hMwin hV
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
        (s l).sourceBlock (t l) rows W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l)) =
      (F : ℂ)⁻¹ * ∑ l ∈ labels,
        (((1+K₀ l*H₀ l/(A₀ l*B₀ l))^decay : ℝ) : ℂ)*
          (s l).sourceBlock (t l) rows W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hid, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hF,
    centered_energy_root_identity T NC ND E₁ E₂ hT.le hNC hND] at hh
  have hs := mul_le_mul_of_nonneg_left hh (show 0 ≤ F/T by positivity)
  convert hs using 1 <;> field_simp


/-- Literal first-block conclusion at the parent scale, conditional only
on the two joint target energies and explicit source sector support.
The width δ pays the common-norm shell tolerance; no first-label count
is introduced after the joint targets. -/
theorem joint_first_centered_sector_from_joint_targets
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (Mwin : Fin 4 → ℝ) (hMwin : ∀ i, 0 ≤ Mwin i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ Mwin i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (decay P₁ P₂ J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
      (q : FirstJointLabel ι) (Z M A δ a window : ℝ), 1 < Z → 0 < a →
      ∀ (t K₀ H₀ A₀ B₀ : Λ → ℝ),
      (∀ z ∈ rows, z ≠ 0) →
      (∀ l, 0 < K₀ l) → (∀ l, 0 < H₀ l) → (∀ l, 0 < A₀ l) → (∀ l, 0 < B₀ l) →
      (∀ l ∈ labels, a*Z^A ≤ ((s l).C.absNorm : ℝ)*Real.exp window*A₀ l) →
      (∀ l ∈ labels, a*Z^A ≤ ((s l).D.absNorm : ℝ)*Real.exp window*B₀ l) →
      (∀ l ∈ labels, ((s l).C.absNorm : ℝ) ≤ Z^δ*(q.C.absNorm : ℝ)) →
      (∀ l ∈ labels, ((s l).D.absNorm : ℝ) ≤ Z^δ*(q.D.absNorm : ℝ)) →
      (∀ l ∈ labels, q.activeWidth Z ≤ (s l).activeWidth Z) →
      (∀ l ∈ labels, q.punctureWidth Z ≤ (s l).punctureWidth Z) →
      (∀ l ∈ labels, ‖V 0 ((s l).sourceRowLog (Z^M) (K₀ l))‖ ≤ 1) →
      (∀ l ∈ labels, ∀ z ∈ rows, ‖V 1 (Real.log (‖eisEmbedding z‖ ^ 2 / H₀ l))‖ ≤ 1) →
      ∀ (U : ((l : Λ) × (s l).SourceIndex) → 𝓢(ℝ, ℂ))
        (H : ((l : Λ) × (s l).SourceIndex) → ℝ),
      (∀ k ∈ firstSourceLabels labels s, 0 < H k) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z : O,
        0 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z ∈ rows,
        1 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ θ w : ℝ, (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).leftEnergy
          (t k.1 + 2 * Real.pi * (w - θ)) (U k) (H k)) ≤
            (((Z^A/(q.C.absNorm : ℝ))*Z^(q.leftTargetWidth Z A)) *
              ((1 + ‖θ‖) ^ P₁) ^ 2) * (1 + ‖w‖) ^ (2 * J₁)) →
      (∀ θ w : ℝ, (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).rightEnergy
          (t k.1 + 2 * Real.pi * (w - (-θ))) (U k) (H k)) ≤
            (((Z^A/(q.D.absNorm : ℝ))*Z^(q.rightTargetWidth Z A)) *
              ((1 + ‖θ‖) ^ P₂) ^ 2) * (1 + ‖w‖) ^ (2 * J₂)) →
      ‖∑ l ∈ labels, (((1 + K₀ l * H₀ l / (A₀ l * B₀ l)) ^ decay : ℝ) : ℂ) *
        (s l).sourceBlock (t l) rows W V (Z^M) (K₀ l) (H₀ l) (A₀ l) (B₀ l)‖ / Z^A ≤
          C * (Real.exp window/a) * Z^(M+δ) := by
  obtain ⟨C, hC, hc⟩ := joint_first_centered_blocks_from_scalar_cap (ι := ι) W V Mwin hMwin hV
    hV₂c hV₂s hV₃c hV₃s decay P₁ P₂ J₁ J₂
  refine ⟨C, hC, ?_⟩
  intro Λ inst labels rows s q Z M A δ a window hZ ha t K₀ H₀ A₀ B₀ hrows
    hK₀ hH₀ hA₀ hB₀ hl hr hNC hND hactive hpuncture hV₀ hV₁ U H hH hU hmajor hleft hright
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hNqC : 0 < (q.C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr q.hC.1)
  have hNqD : 0 < (q.D.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr q.hD.1)
  have hroot : 0 < Real.sqrt ((q.C.absNorm : ℝ)*q.D.absNorm) :=
    Real.sqrt_pos.mpr (mul_pos hNqC hNqD)
  let F := (Real.exp window/a)*Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z+δ)*
    Real.sqrt ((q.C.absNorm : ℝ)*q.D.absNorm)
  have hF : 0 < F := by dsimp [F]; positivity
  have hh := hc labels rows s t (fun _ => Z^M) K₀ H₀ A₀ B₀
    hrows (fun _ => Real.rpow_pos_of_pos hz _) hK₀ hH₀ hA₀ hB₀
    F (Z^A) (q.C.absNorm : ℝ) (q.D.absNorm : ℝ) hF (Real.rpow_pos_of_pos hz _)
    hNqC hNqD
    (fun l hmem => (s l).sector_scalar_cap q Z M A δ (A₀ l) (B₀ l) a window hZ
      (hA₀ l) (hB₀ l) ha (hl l hmem) (hr l hmem) (hNC l hmem) (hND l hmem)
      (by linarith [hactive l hmem,hpuncture l hmem]))
    hV₀ hV₁ U H hH hU hmajor (Z^(q.leftTargetWidth Z A)) (Z^(q.rightTargetWidth Z A))
    (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _) hleft hright
  have hFdiv : F/Real.sqrt ((q.C.absNorm : ℝ)*q.D.absNorm) =
      (Real.exp window/a)*Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z+δ) := by
    dsimp only [F]
    exact mul_div_cancel_right₀ _ hroot.ne'
  rw [hFdiv] at hh
  have hbudget := actual_first_joint_rpow_budget q Z M A hZ
  change Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z)*
    Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A)) ≤ Z^M at hbudget
  calc
    _ ≤ C*((Real.exp window/a)*Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z+δ))*
        (Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A))) := hh
    _ = (C*(Real.exp window/a)*Z^δ)*
        (Z^(M-A-q.activeWidth Z/2-q.punctureWidth Z)*
          Real.sqrt (Z^(q.leftTargetWidth Z A))*Real.sqrt (Z^(q.rightTargetWidth Z A))) := by
      rw [Real.rpow_add hz]
      ring
    _ ≤ (C*(Real.exp window/a)*Z^δ)*Z^M :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by rw [Real.rpow_add hz]; ring

#print axioms joint_first_centered_sector_from_joint_targets

#print axioms joint_first_centered_blocks_from_scalar_cap

#print axioms FirstJointLabel.sourceWeight_contraction
#print axioms FirstJointLabel.normalized_scalar_rpow_bound
#print axioms actual_first_joint_rpow_budget
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstLedger -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstVariableKernel ; sha256 c875d1310735126794c7c479a03b5c51d830127f6763a664dcfb069bae744a87 -/
section



/-! Actual first kernels with label-dependent retained row sets. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentCauchy
open CenteredMomentCanonicalFirst CenteredMomentSecondHeightFamily
open RayFourExpansion ConcretePrimeRowBridge CenteredMomentChildAssembly
open CenteredMomentFirstColumns CenteredMomentFirstChildBound CenteredMomentMobiusRegroup
open CenteredMomentSmooth CenteredMomentSupportedCorrelation CenteredMomentCommonSupport
open CenteredMomentConjugateWindow
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem joint_first_variable_kernel_from_window (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (decay J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Λ → Finset O) (s : Λ → FirstJointLabel ι)
      (t R ρ₀ A₀ B₀ : Λ → ℝ) (x : Λ → O → ℝ) (η : Λ → ℂ) (q : Λ → O → ℂ),
      (∀ l, 0 < R l) → (∀ l ∈ labels, ∀ z ∈ rows l, ‖η l * q l z‖ ≤ 1) →
      (∀ l ∈ labels, ‖V 0 (ρ₀ l)‖ ≤ 1) →
      (∀ l ∈ labels, ∀ z ∈ rows l, ‖V 1 (x l z)‖ ≤ 1) →
      ∀ E : ℝ,
      (∀ θ : ℝ, (∑ l ∈ labels, ∑ z ∈ rows l,
        ‖leftWindowChild (s l).data (s l).parent
          (fixedBadMask * idealGenerator (s l).data.R) (t l)
          (s l).C (s l).D (s l).hC (s l).E (s l).leftRay (s l).projector θ (A₀ l) (V 2) z‖ *
        ‖rightWindowChild (s l).data (s l).parent
          (fixedBadMask * idealGenerator (s l).data.R) (t l)
          (s l).C (s l).D (s l).hC (s l).hD (s l).E (s l).rightRay (s l).projector
          θ (B₀ l) (V 3) (-z)‖) ≤ E * (1 + ‖θ‖) ^ J) →
      ‖∑ l ∈ labels, (((1 + R l) ^ decay : ℝ) : ℂ) * η l *
        (s l).kernelBlock (t l) (rows l) W V (R l) (ρ₀ l) (x l) (A₀ l) (B₀ l) (q l)‖ ≤ C * E := by
  obtain ⟨C, hC, hc⟩ := whole_kernel_joint_estimate W V M hM hV decay J
  refine ⟨C, hC, ?_⟩
  intro Λ inst labels rows s t R ρ₀ A₀ B₀ x η q hR hη hV₀ hV₁ E he
  have h := hc (labels.sigma rows)
    (fun k => (Finset.univ : Finset (s k.1).LeftIndex))
    (fun k => (Finset.univ : Finset (s k.1).RightIndex))
    (fun k => (s k.1).leftRowCoefficient (t k.1) k.2)
    (fun k => (s k.1).rightRowCoefficient (t k.1) k.2)
    (fun k => (s k.1).leftLog (A₀ k.1)) (fun k => (s k.1).rightLog (B₀ k.1))
    (fun k => R k.1) (fun k => ρ₀ k.1) (fun k => x k.1 k.2)
    (fun k => η k.1 * q k.1 k.2) (fun k => hR k.1)
    (fun k hk => hη k.1 (Finset.mem_sigma.mp hk).1 k.2 (Finset.mem_sigma.mp hk).2)
    (fun k hk => hV₀ k.1 (Finset.mem_sigma.mp hk).1)
    (fun k hk => hV₁ k.1 (Finset.mem_sigma.mp hk).1 k.2 (Finset.mem_sigma.mp hk).2)
    E (by
      intro θ
      simp only [Finset.sum_sigma, FirstJointLabel.leftColumn_eq_window,
        FirstJointLabel.rightColumn_eq_window, norm_star]
      exact he θ)
  simpa only [Finset.sum_sigma, FirstJointLabel.kernelBlock, Finset.mul_sum, mul_assoc] using h


theorem joint_first_variable_blocks_from_window (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (decay J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Λ → Finset O) (s : Λ → FirstJointLabel ι)
      (t K K₀ H₀ A₀ B₀ : Λ → ℝ) (η : Λ → ℂ),
      (∀ l, ∀ z ∈ rows l, z ≠ 0) →
      (∀ l, 0 < K l) → (∀ l, 0 < K₀ l) → (∀ l, 0 < H₀ l) →
      (∀ l, 0 < A₀ l) → (∀ l, 0 < B₀ l) →
      (∀ l ∈ labels, ∀ i : (s l).SourceIndex,
        ‖η l * (s l).sourceWeight (K l) (A₀ l) (B₀ l) i‖ ≤ 1) →
      (∀ l ∈ labels, ‖V 0 ((s l).sourceRowLog (K l) (K₀ l))‖ ≤ 1) →
      (∀ l ∈ labels, ∀ z ∈ rows l, ‖V 1 (Real.log (‖eisEmbedding z‖ ^ 2 / H₀ l))‖ ≤ 1) →
      ∀ E : ℝ,
      (∀ θ : ℝ, (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).windowPair (t k.1) θ (A₀ k.1) (B₀ k.1) V (rows k.1)) ≤
          E * (1 + ‖θ‖) ^ J) →
      ‖∑ l ∈ labels, (((1 + K₀ l * H₀ l / (A₀ l * B₀ l)) ^ decay : ℝ) : ℂ) * η l *
        (s l).sourceBlock (t l) (rows l) W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l)‖ ≤ C * E := by
  obtain ⟨C, hC, hc⟩ := joint_first_variable_kernel_from_window (ι := ι) W V M hM hV decay J
  refine ⟨C, hC, ?_⟩
  intro Λ inst labels rows s t K K₀ H₀ A₀ B₀ η hrows hK hK₀ hH₀ hA₀ hB₀ hη hV₀ hV₁ E he
  have h := hc (firstSourceLabels labels s) (fun k => rows k.1)
    (fun k => (s k.1).sourceChild k.2) (fun k => t k.1)
    (fun k => K₀ k.1 * H₀ k.1 / (A₀ k.1 * B₀ k.1))
    (fun k => (s k.1).sourceRowLog (K k.1) (K₀ k.1))
    (fun k => A₀ k.1) (fun k => B₀ k.1)
    (fun k z => Real.log (‖eisEmbedding z‖ ^ 2 / H₀ k.1))
    (fun k => η k.1 * (s k.1).sourceWeight (K k.1) (A₀ k.1) (B₀ k.1) k.2)
    (fun k => (s k.1).sourcePhase)
    (fun k => div_pos (mul_pos (hK₀ k.1) (hH₀ k.1)) (mul_pos (hA₀ k.1) (hB₀ k.1)))
    (fun k hk z hz => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (hη k.1 (Finset.mem_sigma.mp hk).1 k.2)).trans ((s k.1).sourcePhase_norm z))
    (fun k hk => hV₀ k.1 (Finset.mem_sigma.mp hk).1)
    (fun k hk z hz => hV₁ k.1 (Finset.mem_sigma.mp hk).1 z hz) E he
  have hi (l : Λ) : (s l).sourceBlock (t l) (rows l) W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l) =
      ∑ i : (s l).SourceIndex, (s l).sourceWeight (K l) (A₀ l) (B₀ l) i *
        ((s l).sourceChild i).kernelBlock (t l) (rows l) W V (K₀ l * H₀ l / (A₀ l * B₀ l))
          ((s l).sourceRowLog (K l) (K₀ l))
          (fun z => Real.log (‖eisEmbedding z‖ ^ 2 / H₀ l)) (A₀ l) (B₀ l) (s l).sourcePhase :=
    (s l).sourceBlock_eq_sum (t l) (rows l) (hrows l) W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l)
      (hK l) (hK₀ l) (hH₀ l) (hA₀ l) (hB₀ l)
  simp_rw [hi]
  simpa only [firstSourceLabels, Finset.sum_sigma, Finset.mul_sum, mul_assoc] using h


/-- A literal source adapter from joint common energies at common Fourier
heights to the summed first blocks. The complete projector and ray labels
remain inside both input energies throughout the two Fourier windows. -/
theorem joint_first_variable_blocks_from_common_energy
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (decay P₁ P₂ J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Λ → Finset O) (s : Λ → FirstJointLabel ι)
      (t K K₀ H₀ A₀ B₀ : Λ → ℝ) (η : Λ → ℂ),
      (∀ l, ∀ z ∈ rows l, z ≠ 0) →
      (∀ l, 0 < K l) → (∀ l, 0 < K₀ l) → (∀ l, 0 < H₀ l) →
      (∀ l, 0 < A₀ l) → (∀ l, 0 < B₀ l) →
      (∀ l ∈ labels, ∀ i : (s l).SourceIndex,
        ‖η l * (s l).sourceWeight (K l) (A₀ l) (B₀ l) i‖ ≤ 1) →
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
            (E₁ * ((1 + ‖θ‖) ^ P₁) ^ 2) * (1 + ‖w‖) ^ (2 * J₁)) →
      (∀ θ w : ℝ, (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).rightEnergy
          (t k.1 + 2 * Real.pi * (w - (-θ))) (U k) (H k)) ≤
            (E₂ * ((1 + ‖θ‖) ^ P₂) ^ 2) * (1 + ‖w‖) ^ (2 * J₂)) →
      ‖∑ l ∈ labels, (((1 + K₀ l * H₀ l / (A₀ l * B₀ l)) ^ decay : ℝ) : ℂ) * η l *
        (s l).sourceBlock (t l) (rows l) W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l)‖ ≤
          C * (Real.sqrt E₁ * Real.sqrt E₂) := by
  let I₁ := jointColumnMoment (V 2) hV₂c hV₂s J₁
  let I₂ := jointColumnMoment (fun x => star (V 3 x))
    (conjugate_compact (V 3) hV₃c) (conjugate_smooth (V 3) hV₃s) J₂
  have hI₁ : 0 ≤ I₁ := jointColumnMoment_nonneg _ _ _ _
  have hI₂ : 0 ≤ I₂ := jointColumnMoment_nonneg _ _ _ _
  obtain ⟨C, hC, hc⟩ := joint_first_variable_blocks_from_window (ι := ι) W V M hM hV decay (P₁ + P₂)
  refine ⟨C * (I₁ * I₂), mul_nonneg hC (mul_nonneg hI₁ hI₂), ?_⟩
  intro Λ inst labels rows s t K K₀ H₀ A₀ B₀ η hrows hK hK₀ hH₀ hA₀ hB₀ hη hV₀ hV₁
    U H hH hU hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hwindow (θ : ℝ) :
      (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).windowPair (t k.1) θ (A₀ k.1) (B₀ k.1) V (rows k.1)) ≤
        ((Real.sqrt E₁ * Real.sqrt E₂) * (I₁ * I₂)) * (1 + ‖θ‖) ^ (P₁ + P₂) := by
    have hh := joint_first_variable_window_abs_bound (firstSourceLabels labels s) (fun k => rows k.1)
      (fun k => (s k.1).sourceChild k.2) (fun k => t k.1) (fun k => t k.1)
      (fun k => A₀ k.1) (fun k => B₀ k.1) (fun k _ => hA₀ k.1) (fun k _ => hB₀ k.1) θ
      (V 2) hV₂c hV₂s (V 3) hV₃c hV₃s U H hH hU hmajor J₁ J₂
      (E₁ * ((1 + ‖θ‖) ^ P₁) ^ 2) (E₂ * ((1 + ‖θ‖) ^ P₂) ^ 2)
      (mul_nonneg hE₁ (sq_nonneg _)) (mul_nonneg hE₂ (sq_nonneg _))
      (hleft θ) (hright θ)
    change _ ≤ (Real.sqrt (E₁ * ((1 + ‖θ‖) ^ P₁) ^ 2) * I₁) *
      (Real.sqrt (E₂ * ((1 + ‖θ‖) ^ P₂) ^ 2) * I₂) at hh
    rw [Real.sqrt_mul hE₁, Real.sqrt_mul hE₂,
      Real.sqrt_sq (by positivity : 0 ≤ (1 + ‖θ‖) ^ P₁),
      Real.sqrt_sq (by positivity : 0 ≤ (1 + ‖θ‖) ^ P₂)] at hh
    simpa only [FirstJointLabel.windowPair, FirstJointLabel.leftWindowValue,
      FirstJointLabel.rightWindowValue, pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
  have hh := hc labels rows s t K K₀ H₀ A₀ B₀ η hrows hK hK₀ hH₀ hA₀ hB₀
    hη hV₀ hV₁ ((Real.sqrt E₁ * Real.sqrt E₂) * (I₁ * I₂)) hwindow
  convert hh using 1
  ring

#print axioms joint_first_variable_blocks_from_common_energy

#print axioms joint_first_variable_blocks_from_window

#print axioms FirstJointLabel.block_eq_kernel_children
#print axioms joint_first_variable_kernel_from_window
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstVariableKernel -/

/- BEGIN ORIGINAL MODULE Analytic.JointOriginalComparisonPower ; sha256 a6456fc9afd26eaadd01a18bf8ee4c641724248525311c5c929b994fa215d14e -/
section




set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance originalComparisonPowerFinite : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem local_comparison_power_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hrhocap:rho≤1/10):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e → 0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → κ=3/4 →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → 1≤ s.width → s.width≤101/100 → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,1≤ X₁ → 1≤ X₂ → X₁≤ Z^(1/4:ℝ) → X₂≤ Z^(3/5:ℝ) →
      (∑i,w i)≤37/1000 →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hLupper,hscalar⟩:=
    exists_bounded_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    local_comparison_original_energy (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi (by linarith) hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hshi hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hslots
  have hh:=hZ.2 Lslot e κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hslo hshi W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hslots
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hsumcap:(∑i,w i)≤ Mcap:=by linarith
  have hledger:=hscalar e he Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤ A:=by dsimp only [A];positivity
  have hE:0≤ E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left hdiag (le_add_of_nonneg_left hK)) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤ L:=by linarith
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hP:0≤ P:=by dsimp only [P];positivity
  have hQmain:0≤ Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤ Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤ Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

#print axioms local_comparison_power_from_low
end SevenEighths.Local44.Analytic

end

end OAI
end
/- END ORIGINAL MODULE Analytic.JointOriginalComparisonPower -/
