/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.reserve_local_20261013.Bundles.B022
import Submissions.reserve_local_20261013.Bundles.B026
import Submissions.reserve_local_20261013.Bundles.B044
import Submissions.reserve_local_20261013.Bundles.B047
import Submissions.reserve_local_20261013.Bundles.B056
import Submissions.reserve_local_20261013.Bundles.B067
import Submissions.reserve_local_20261013.Bundles.B069
import Submissions.reserve_local_20261013.Bundles.B070
import Submissions.reserve_local_20261013.Bundles.B071
import Submissions.reserve_local_20261013.Bundles.B072
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.PaidRemoval
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass

/- BEGIN ORIGINAL MODULE Analytic.ActualErrorPower ; sha256 7f75d2d62bf42452462d9ed33be7a4734ee8345b889767485c573c1e1902bef7 -/
section



/-! Actual extracted Gaussian errors, uniformly over original source subsets.
The genuine incumbent endpoints are consumed internally. The first Gaussian
power retains sigma + removal - moving and therefore the local reserve. -/
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
local instance actualErrorPowerInstance1 {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance actualErrorPowerInstance2 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem actual_original_subsets_error_power
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
    (sigma cost:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost):
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
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
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
    length Z src.X₁+length Z src.X₂+6*(3/4)*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,(Cbound*(p.control Uprofile)^2*(1+|v0|+height)^Jheight*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (refinedErrorDeficit prime Z (k+1) sigma (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 := by
  have hmax : 0 < max 1 b := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ha' : 0 < a/max 1 b := div_pos haPlain hmax
  have haUpper' : a/max 1 b ≤ 1/4 := by
    apply (div_le_iff₀ hmax).mpr
    nlinarith [le_max_left (1 : ℝ) b]
  obtain ⟨degree,S,hinc⟩ := actual_incumbent_pair (α := α) M H hH Wslot aslot bslot
    (a/max 1 b) b 2 0 L lo hi Mcap εchild ha hWs hW hbslot ha' haUpper' hbPlain
    (by norm_num) (by norm_num) hMcap hεchild hbeta hbetaTop
  have hmesh := Cycle25.Energy.commonMesh_pos Mcap 0 L εchild hMcap.le (by norm_num) hεchild
  obtain ⟨Uprofile,Jheight,hmain⟩ := refined_original_subsets_error_power (α := α) M H hH
    Wslot aslot bslot Mcap (Cycle25.Energy.commonMesh Mcap 0 L εchild) εremove lo hi (3/4)
    a b Mslot εmask hMslot hεmask haPlain (zero_le_one.trans hbPlain)
    L hL degree S ha hWs hW hMcap.le hmesh.le hε (by norm_num) hbeta (by linarith)
    N lower upper a0 θsource hlower hupper ha0 hθsource lows highs hhighs
    εsrc δsrc θsrc Bcap Bseed ξ saving hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,Z₀,hZ₀,hconsume⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,hC₁,hincZ⟩ := hinc η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound*(C₀+C₁+1),mul_pos hCbound (by positivity),?_⟩
  filter_upwards [hincZ,eventually_ge_atTop Z₀] with Z hZ hZ₀Z
  refine ⟨hZ.1,?_⟩
  intro Aorig θ
  exact hconsume Aorig θ Z hZ₀Z εchild C₀ C₁ hC₀.le hC₁.le hZ.2.1 hZ.2.2

#print axioms actual_original_subsets_error_power
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualErrorPower -/

/- BEGIN ORIGINAL MODULE Analytic.ActualGlobalRemoval ; sha256 4f60b5520c9d48dddae86c920ffbfe3064e2436622671d2c1601c0f74d504bec -/
section



/-! The unconditional removal estimate used by the three amplification
errors. Both remaining-slot endpoints are supplied by the actual incumbent,
and all finite ray choices share one eventual scale threshold. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyPaidRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentPrimeSlot QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_global_removal
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap εchild εremove : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεchild : 0 < εchild) (hεremove : 0 < εremove)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character,
      ∀ Q : Ideal O, Q ≤ M → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H)
          (w σ v : α → ℝ) (t height mesh : ℝ),
        0 ≤ mesh → mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εchild →
        (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
        (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |v i| ≤ height) →
        ∀ s : NaturalState Z Bmask radial, s.puncture = 1 →
          s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap →
        ∀ (p : Profiles a b) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun i : J => primePool M H bslot (Z^(w i)))
          (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
          (fun i : J => Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
          C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree*
            Z^(s.width+εchild+εremove+
              max (length Z X₁+length Z X₂+(9/2)*(∑ i ∈ J, w i)-s.width) 0/6+(3/4)*mesh) := by
  obtain ⟨degree,S,hinc⟩ := actual_incumbent_pair (α := α) M H hH W aslot bslot a b
    radial Bmask L lo hi Mcap εchild haslot hWs hW hbslot ha haUpper hb hrad hmask
    hMcap hεchild hbeta hbetaTop
  have hmesh := Cycle25.Energy.commonMesh_pos Mcap Bmask L εchild hMcap.le hmask hεchild
  obtain ⟨dc,Cc,hCc,hpaid⟩ := actual_paid_bands (α := α) M H hH W aslot bslot Mcap radial
    (Cycle25.Energy.commonMesh Mcap Bmask L εchild) εremove lo hi (3/4)
    haslot hWs hW hMcap.le hrad.le hmesh.le hεremove hbeta (by linarith)
  refine ⟨dc+degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,hC₁,hincZ⟩ := hinc η₀ Q hQM hQ0 hQt hQ72
  choose Z₀ hZ₀ hpaidZ using hpaid η₀
  have hthreshold : ∀ᶠ Z : ℝ in atTop, ∀ θ, Z₀ θ ≤ Z :=
    Filter.eventually_all.mpr (fun θ => eventually_ge_atTop (Z₀ θ))
  refine ⟨Cc*(C₀+C₁), mul_pos hCc (add_pos hC₀ hC₁), ?_⟩
  filter_upwards [hincZ,hthreshold] with Z hincZ hZ₀all
  refine ⟨hincZ.1,?_⟩
  intro J θ w σ v t height mesh hmesh0 hmeshCap hw hwm hσlo hσhi hheight hv
    s hunit hQ hs p X₁ X₂ hX₁ hX₂ hLX₁ hLX₂
  have hh := hpaidZ θ Z (hZ₀all θ) a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀.le hC₁.le
    hincZ.2.1 hincZ.2.2 J w σ v t height mesh hmesh0 hw hwm
    (fun i => (hwm i).trans hmeshCap) hσlo hσhi hheight hv s hunit hQ hs
    p X₁ X₂ hX₁ hX₂ hLX₁ hLX₂
  norm_num only [CenteredMomentLiveCapacity.excess, show (6 : ℝ)*(3/4)=9/2 by norm_num] at hh
  exact hh

#print axioms actual_global_removal
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualGlobalRemoval -/

/- BEGIN ORIGINAL MODULE Analytic.JointCommonShortGates ; sha256 38db11ebc9097734498a2bba3191ff00cb4bf4517e6638c6d2bc4685f8db3814 -/
section




/-! The actual common-source X/Y branch, with its inherited slots and
comparison scales, produces admissible data on the original slot type. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDyadic ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentRetainedProfile CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentPrimeSlot CenteredMomentHeckeExpansion
open CenteredMomentDivisorRectangle CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
local notation "O" => HeckeFamily.O

theorem actual_common_retained_short_gates
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
        (orders : Finset ι → ℕ) (edge e : ℝ), edge ≤ 1 → e ≤ 1/1000 →
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
        (hH : RayOrthogonality.globalUnits M ≤ H)
        (η : Character) (w : NonzeroElement) (parent : JointParentLabel η)
        (N : NaturalRow parent.val w.val) (puncture : Ideal O) (hpuncture : puncture ≠ 0)
        (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
        (source : Character) (A z : O) (t : ℝ)
        (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset
          (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2))) (branch : Bool)
        (Z d : ℝ) (η₀ : ι → Character) (V : ι → ℝ → ℂ)
        (alo bhi : ι → ℝ) (bin : ℕ) (Rwidth τ ηaux σmin σmax T : ℝ),
      s.W₁ = W₁ → s.W₂ = W₂ →
      (∀ i, s.slots i = primePool M H (bhi i) (s.P i)) →
      (∀ i I, I ∈ s.slots i → s.ν i I = idealCoeff (η₀ i).inverse I) → (∀ i, s.W i = V i) →
      (∀ I : Ideal O, rowWeight source (fixedBadMask*idealGenerator (R*C)) A z t I =
        rowWeight parent.val (fixedBadMask*idealGenerator puncture) 1 w.val t I) →
      1 < Z → d ≠ 0 → 1 < Z^d → 0 ≤ Rwidth →
      s.X₁ ≤ (Z^d)^Rwidth → s.X₂ ≤ (Z^d)^Rwidth →
      s.Y₁ ≤ (Z^d)^Rwidth → s.Y₂ ≤ (Z^d)^Rwidth →
      (∀ i, 1 ≤ s.P i ∧ s.P i ≤ (Z^d)^Rwidth) → σmin ≤ 0 → 0 ≤ σmax →
      (∀ label, (bufferedProductFamily M H hH η₀
        (excluded N.character puncture) label).modulus.absNorm ≤ Z^d) →
      |t|+Z^τ/2 ≤ (3*bin+2 : ℕ)*Z^τ →
      (3+(3*bin+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux →
      (3+(3*bin+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux →
      3*(bin+1 : ℕ)*Z^τ ≤ T →
      secondRetainedPositive (secondCommonData s C R B source A t).toSource
        D allocation branch z ≠ 0 →
      ∃ data : SurvivingBufferedData η w ι orders profileBound edge e,
        data.slots = embeddedSlots (allocationSlotEmbedding (commonSlotEmbedding s C B) D allocation) ∧
        ‖secondRetainedPositive (secondCommonData s C R B source A t).toSource
          D allocation branch z‖ = ‖data.value M H η₀ V bhi Z d‖ ∧
        d*data.length ≤ Real.logb Z (secondCommonVolume s C B)-
          Real.logb Z (formalReductionFactor D allocation (fun i => s.P i.val))+
          Real.logb Z (max 1 b₁*max 1 b₂) ∧
        data.ShortSlotGates M H hH η₀ Rwidth τ ηaux σmin σmax Z d T ∧
        (∀ j : data.slots, (Z^d)^(data.data.r j) = s.P j.val) ∧
        (∀ j, data.data.σ j = 0 ∧ data.data.v j = 0) ∧ data.data.t = t ∧ data.data.bin = bin := by
  obtain ⟨profileBound,hprofile,hdata⟩ := actual_source_allocated_short_gates
    W₁ W₂ a₁ b₁ a₂ b₂ ha₁ ha₂ hs₁ hW₁ hs₂ hW₂
  refine ⟨profileBound,hprofile,?_⟩
  intro ι instι instDι orders edge e hedge he M instM H hH η w parent N puncture hpuncture
    s C R B source A z t D allocation branch Z d η₀ V alo bhi bin Rwidth τ ηaux σmin σmax T
    hsW₁ hsW₂ hslots hν hW hrow hZ hd hbase hR hX₁ hX₂ hY₁ hY₂ hP hσmin hσmax
    hconductor hfreq hfour htwo hbuffer hn
  let c := secondCommonData s C R B source A t
  let X₁ := if branch then c.X₁ else c.Y₁
  let X₂ := if branch then c.X₂ else c.Y₂
  have hx₁ : 0 < X₁ := by unfold X₁; split_ifs; exact c.X₁_pos; exact c.Y₁_pos
  have hx₂ : 0 < X₂ := by unfold X₂; split_ifs; exact c.X₂_pos; exact c.Y₂_pos
  have hN (j : Fin 2) : (1 : ℝ) ≤ Ideal.absNorm (B.val (Sum.inr j)) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B (Sum.inr j)))
  have hx₁cap : X₁ ≤ (Z^d)^Rwidth := by
    unfold X₁
    split_ifs
    · exact (div_le_self s.X₁_pos.le (hN 0)).trans hX₁
    · exact (div_le_self s.Y₁_pos.le (hN 0)).trans hY₁
  have hx₂cap : X₂ ≤ (Z^d)^Rwidth := by
    unfold X₂
    split_ifs
    · exact (div_le_self s.X₂_pos.le (hN 1)).trans hX₂
    · exact (div_le_self s.Y₂_pos.le (hN 1)).trans hY₂
  have heq : secondRetainedPositive c.toSource D allocation branch z =
      allocatedPositiveRow source (fixedBadMask*idealGenerator (R*C)) A z t
        (fun i : CenteredMomentCommonProfile.liveIndices B.val => primePool M H (bhi i.val) (s.P i.val))
        (fun i I => idealCoeff (η₀ i.val).inverse I*V i.val ((I.absNorm : ℝ)/s.P i.val))
        (fun i => s.P i.val) D allocation W₁ W₂ X₁ X₂ := by
    simp only [secondRetainedPositive,X₁,X₂,c,secondCommonData,commonData,hslots,hW,hsW₁,hsW₂]
    apply allocatedPositiveRow_congr_coeff_on_pool
    intro i I hI
    rw [hν i.val I (by simpa only [hslots] using hI)]
  have hne := ne_of_eq_of_ne heq.symm hn
  obtain ⟨data,hslots',hnorm,hlength,had,hscale,hzero,ht,hbi⟩ := hdata (commonSlotEmbedding s C B) orders edge e
    hedge he M H hH η w parent N puncture hpuncture source
      (fixedBadMask*idealGenerator (R*C)) A z t hrow D allocation Z d X₁ X₂
      η₀ V alo bhi (fun i => s.P i.val) s.P bin Rwidth τ ηaux σmin σmax T
      (fun _ => rfl) hZ hd hbase hx₁ hx₂ hR hx₁cap hx₂cap (fun i => hP i.val) hσmin hσmax
      hconductor hfreq hfour htwo hbuffer hne
  refine ⟨data,hslots',(congrArg (fun x : ℂ => ‖x‖) heq).trans hnorm,?_,had,hscale,hzero,ht,hbi⟩
  have hvolume : X₁*X₂*(∏ i : CenteredMomentCommonProfile.liveIndices B.val, s.P i.val) =
      secondCommonVolume s C B := by
    unfold X₁ X₂
    cases branch
    · change c.Y₁*c.Y₂*_ = c.X₁*c.X₂*_
      rw [c.same_product]
    · rfl
  simpa only [hvolume] using hlength

#print axioms actual_common_retained_short_gates
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCommonShortGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointFullRetainedFiber ; sha256 d40a779102e29871c2fb1be49f70e57e2d13de21c0c0e254a380a750e0644ac0 -/
section



/-! One finite dependent fiber retains the second projector and every
literal allocated branch; only the reconstructed arithmetic label is
counted by density. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily
local notation "O" => HeckeFamily.O
namespace CommonSecondKernelLabel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev FullRetainedFiber (s : CommonSecondKernelLabel ι) :=
  (L : Ideal O) × (s.withProjector L).RetainedFiber

def fullRetainedFiber (s : CommonSecondKernelLabel ι) (Ds : Finset (Ideal O))
    (t₁ t₂ : ℝ) : Finset s.FullRetainedFiber :=
  Ds.sigma (fun L => (s.withProjector L).retainedFiber t₁ t₂)

def fullFiberWeight (s : CommonSecondKernelLabel ι) (t₁ t₂ H₁ H₂ : ℝ)
    (q : s.FullRetainedFiber) : ℝ :=
  ‖(UniqueFactorizationMonoid.moebius q.1 : ℂ)‖ *
    (s.withProjector q.1).fiberWeight t₁ t₂ H₁ H₂ q.2

def fullFiberValue (s : CommonSecondKernelLabel ι) (t₁ t₂ : ℝ) (z : O)
    (q : s.FullRetainedFiber) : ℝ :=
  (s.withProjector q.1).fiberValue t₁ t₂ z q.2

def liveFullRetainedFiber (s : CommonSecondKernelLabel ι) (Ds : Finset (Ideal O))
    (t₁ t₂ : ℝ) (z : O) : Finset s.FullRetainedFiber :=
  (s.fullRetainedFiber Ds t₁ t₂).filter (fun q => s.fullFiberValue t₁ t₂ z q ≠ 0)

theorem fullFiberWeight_nonneg (s : CommonSecondKernelLabel ι) (t₁ t₂ H₁ H₂ : ℝ)
    (q : s.FullRetainedFiber) : 0 ≤ s.fullFiberWeight t₁ t₂ H₁ H₂ q :=
  mul_nonneg (norm_nonneg _) ((s.withProjector q.1).fiberWeight_nonneg t₁ t₂ H₁ H₂ q.2)

theorem liveFullRetainedFiber_nonzero (s : CommonSecondKernelLabel ι)
    (Ds : Finset (Ideal O)) (t₁ t₂ : ℝ) (z : O) (q : s.FullRetainedFiber)
    (hq : q ∈ s.liveFullRetainedFiber Ds t₁ t₂ z) :
    (s.withProjector q.1).fiberLeft t₁ z q.2 ≠ 0 ∧
      (s.withProjector q.1).fiberRight t₂ z q.2 ≠ 0 := by
  have hn := (Finset.mem_filter.mp hq).2
  simpa only [fullFiberValue,fiberValue,ne_eq,mul_eq_zero,norm_eq_zero,not_or] using hn

theorem fullRetainedFiber_mass (s : CommonSecondKernelLabel ι)
    (Ds : Finset (Ideal O)) (t₁ t₂ H₁ H₂ : ℝ) :
    (∑ q ∈ s.fullRetainedFiber Ds t₁ t₂, s.fullFiberWeight t₁ t₂ H₁ H₂ q) =
      s.fullFiberMass Ds t₁ t₂ H₁ H₂ := by
  simp only [fullRetainedFiber,fullFiberWeight,fullFiberMass,Finset.sum_sigma,Finset.mul_sum]

theorem liveFullRetainedFiber_mass_le (s : CommonSecondKernelLabel ι)
    (Ds : Finset (Ideal O)) (t₁ t₂ H₁ H₂ : ℝ) (z : O) :
    (∑ q ∈ s.liveFullRetainedFiber Ds t₁ t₂ z, s.fullFiberWeight t₁ t₂ H₁ H₂ q) ≤
      s.fullFiberMass Ds t₁ t₂ H₁ H₂ := by
  rw [← s.fullRetainedFiber_mass Ds t₁ t₂ H₁ H₂]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun q _ _ => s.fullFiberWeight_nonneg t₁ t₂ H₁ H₂ q)

theorem retained_projector_sum_le_fullFiber (s : CommonSecondKernelLabel ι)
    (Ds : Finset (Ideal O)) (t₁ t₂ H₁ H₂ : ℝ) (z : O) :
    (∑ L ∈ Ds, ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
      (s.withProjector L).retainedPair t₁ t₂ z H₁ H₂) ≤
      ∑ q ∈ s.fullRetainedFiber Ds t₁ t₂,
        s.fullFiberWeight t₁ t₂ H₁ H₂ q*s.fullFiberValue t₁ t₂ z q := by
  simp only [fullRetainedFiber,fullFiberWeight,fullFiberValue,Finset.sum_sigma,← mul_assoc]
  apply Finset.sum_le_sum
  intro L hL
  simpa only [Finset.mul_sum,mul_assoc] using mul_le_mul_of_nonneg_left
    ((s.withProjector L).retainedPair_le_fiber t₁ t₂ z H₁ H₂) (norm_nonneg (UniqueFactorizationMonoid.moebius L : ℂ))

theorem retained_projector_sum_le_liveFullFiber (s : CommonSecondKernelLabel ι)
    (Ds : Finset (Ideal O)) (t₁ t₂ H₁ H₂ : ℝ) (z : O) :
    (∑ L ∈ Ds, ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
      (s.withProjector L).retainedPair t₁ t₂ z H₁ H₂) ≤
      ∑ q ∈ s.liveFullRetainedFiber Ds t₁ t₂ z,
        s.fullFiberWeight t₁ t₂ H₁ H₂ q*s.fullFiberValue t₁ t₂ z q := by
  rw [liveFullRetainedFiber,Finset.sum_filter]
  convert s.retained_projector_sum_le_fullFiber Ds t₁ t₂ H₁ H₂ z using 1
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : s.fullFiberValue t₁ t₂ z q = 0 <;> simp [h]

def activeFullRetainedFiber (s : CommonSecondKernelLabel ι) (Ds : Finset (Ideal O))
    (t₁ t₂ H₁ H₂ : ℝ) (z : O) : Finset s.FullRetainedFiber :=
  (s.liveFullRetainedFiber Ds t₁ t₂ z).filter (fun q => s.fullFiberWeight t₁ t₂ H₁ H₂ q ≠ 0)

theorem activeFullRetainedFiber_live (s : CommonSecondKernelLabel ι)
    (Ds : Finset (Ideal O)) (t₁ t₂ H₁ H₂ : ℝ) (z : O) :
    s.activeFullRetainedFiber Ds t₁ t₂ H₁ H₂ z ⊆ s.liveFullRetainedFiber Ds t₁ t₂ z :=
  Finset.filter_subset _ _

theorem activeFullRetainedFiber_mass_le (s : CommonSecondKernelLabel ι)
    (Ds : Finset (Ideal O)) (t₁ t₂ H₁ H₂ : ℝ) (z : O) :
    (∑ q ∈ s.activeFullRetainedFiber Ds t₁ t₂ H₁ H₂ z, s.fullFiberWeight t₁ t₂ H₁ H₂ q) ≤
      s.fullFiberMass Ds t₁ t₂ H₁ H₂ := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg (s.activeFullRetainedFiber_live Ds t₁ t₂ H₁ H₂ z)
    (fun q _ _ => s.fullFiberWeight_nonneg t₁ t₂ H₁ H₂ q)).trans
  exact s.liveFullRetainedFiber_mass_le Ds t₁ t₂ H₁ H₂ z

theorem activeFullRetainedFiber_weights_ne (s : CommonSecondKernelLabel ι)
    (Ds : Finset (Ideal O)) (t₁ t₂ H₁ H₂ : ℝ) (z : O) (q : s.FullRetainedFiber)
    (hq : q ∈ s.activeFullRetainedFiber Ds t₁ t₂ H₁ H₂ z) :
    s.leftWeight q.2.1 H₁ ≠ 0 ∧ s.rightWeight q.2.2.1 H₂ ≠ 0 := by
  have h := right_ne_zero_of_mul (Finset.mem_filter.mp hq).2
  have hh := left_ne_zero_of_mul h
  exact ⟨norm_ne_zero_iff.mp (left_ne_zero_of_mul hh),
    norm_ne_zero_iff.mp (right_ne_zero_of_mul hh)⟩

theorem retained_projector_sum_le_activeFullFiber (s : CommonSecondKernelLabel ι)
    (Ds : Finset (Ideal O)) (t₁ t₂ H₁ H₂ : ℝ) (z : O) :
    (∑ L ∈ Ds, ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖ *
      (s.withProjector L).retainedPair t₁ t₂ z H₁ H₂) ≤
      ∑ q ∈ s.activeFullRetainedFiber Ds t₁ t₂ H₁ H₂ z,
        s.fullFiberWeight t₁ t₂ H₁ H₂ q*s.fullFiberValue t₁ t₂ z q := by
  rw [activeFullRetainedFiber,Finset.sum_filter]
  convert s.retained_projector_sum_le_liveFullFiber Ds t₁ t₂ H₁ H₂ z using 1
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : s.fullFiberWeight t₁ t₂ H₁ H₂ q = 0 <;> simp [h]

end CommonSecondKernelLabel
#print axioms CommonSecondKernelLabel.retained_projector_sum_le_liveFullFiber
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFullRetainedFiber -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowMoment ; sha256 50afcf7dde64db62e767852fce5e37e49c05d51aeaa7e0bda8623f454e3d751b -/
section





/-! Actual low-bin mean value. The incumbent positive and zero endpoints
are obtained from the completed source theorem. Removed-slot estimates
come from the buffered prime theorem, with exact pool coefficients. -/
set_option autoImplicit false
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
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

lemma naturalState_relative_nonprincipal {Z Bmask radial : ℝ}
    (s : NaturalState Z Bmask radial) (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ : s.fixedModulus = internalQ Q η₀) (z : O) (hz : s.radial.keep z) :
    ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH ((excluded
        (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture).product η₀.inverse) θ).residue ≠ 1 := by
  intro θ
  exact bufferedProductFamily_nonprincipal M H hH (fun _ : Unit => η₀) s.character z
    (naturalRow s.character z (s.row_ne_zero z hz)) (internalQ Q η₀) s.puncture
    (inf_le_left.trans hQM) (fun _ => inf_le_right) s.puncture_ne_zero (s.row_ne_zero z hz)
    (by simpa only [← hQ] using s.nonexceptional z hz) (some ((),θ))

/-- A literal source upper-bin and conductor gate at every retained row.
Nonprincipality is derived from the state's fixed eligibility predicate. -/
structure NaturalLowGate {Z Bmask radial : ℝ}
    (s : NaturalState Z Bmask radial) (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ : s.fixedModulus = internalQ Q η₀) (d τ e a : ℝ) (k : ℕ)
    (z : O) (hz : s.radial.keep z) : Prop where
  maximum : zeroMaximum (twistedFamily M H hH ((excluded
      (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture).product η₀.inverse))
      (naturalState_relative_nonprincipal M H hH s η₀ Q hQM hQ z hz)
      (3*(k+1 : ℕ)*Z^τ) < a+2*e
  conductor : ∀ θ : RayQuotient.Characters M H,
    (twistedFamily M H hH ((excluded
      (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture).product η₀.inverse) θ).modulus.absNorm ≤ Z^d

lemma normalizedSlot_relative_pool (η η₀ : Character) (θ : RayQuotient.Characters M H)
    (m A z : O) (W : ℝ → ℂ) (b P σ v t : ℝ) :
    normalizedSlot η m A z (primePool M H b P)
      (fun I => idealCoeff (relativeCharacter M H hH η₀ θ) I * annularWeight W P σ v I) t P =
    normalizedSlot η m A z (primePool M H b P)
      (fun I => idealCoeff η₀.inverse I * annularWeight W P σ v I) t P := by
  unfold normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only
  rw [CenteredMomentDetectorPlainRelativeClass.relative_pool M H hH η₀ θ b P I hI]

lemma constant_removal_product {α : Type*} [Fintype α]
    (R : Finset α) (C Z ε : ℝ) (hC : 1 ≤ C) (hZ : 1 ≤ Z) (hε : 0 ≤ ε) :
    (∏ _i ∈ R, C*Z^(2*ε)) ≤ C^(Fintype.card α)*Z^(2*ε*(Fintype.card α)) := by
  have hp : 1 ≤ C*Z^(2*ε) := one_le_mul_of_one_le_of_one_le hC
    (Real.one_le_rpow hZ (by positivity))
  have hcard := Finset.card_le_univ R
  simp only [Finset.prod_const]
  calc
    (C*Z^(2*ε))^R.card ≤ (C*Z^(2*ε))^(Fintype.card α) :=
      pow_le_pow_right₀ hp hcard
    _ = _ := by
      rw [mul_pow, ← Real.rpow_natCast (Z^(2*ε)) (Fintype.card α),
        ← Real.rpow_mul (by linarith : 0 ≤ Z)]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- One actual restricted low-bin mean value, including complete exhaustion
of the slots. Mesh and profile seminorms precede every parent and live row;
the only remaining hypotheses are literal source geometry and zero gates. -/
theorem actual_joint_low_moment
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεmoment : 0 < εmoment)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (Rwidth d τ εslot e κ ηheight loss : ℝ)
    (hRw : 0 < Rwidth) (hd : 0 < d) (hτ : 0 < τ) (hεslot : 0 < εslot)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ ηheight)
    (hbudget : 8*e*Rwidth+κ ≤ εslot)
    (mesh : ℝ) (hmesh : 0 < mesh)
    (hmeshInc : mesh ≤ Cycle25.Energy.commonMesh Mcap Bmask L εmoment)
    (hmeshWidth : mesh ≤ d*Rwidth)
    (hmeshLoss : εmoment+(67/100)*mesh+2*d*εslot*(Fintype.card α) ≤ loss) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ)
        (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |v i| ≤ height) →
      ∀ (s : NaturalState Z Bmask radial) (hQ : s.fixedModulus = internalQ Q η₀),
      s.width ≤ Mcap → ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : s.radial.keep z, low z → NaturalLowGate M H hH s η₀ Q hQM hQ d τ e abin k z hz) →
      (∀ i ∈ J, 2*(|Real.log aslot|+|Real.log bslot|)+1 ≤ Real.log (Z^(w i))) →
      (∀ i ∈ J, |t+v i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ (p : Profiles a b) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : J => primePool M H bslot (Z^(w i)))
        (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i : J => Z^(w i)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
        s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree *
        Z^(s.width+(67/450)*max (length Z X₁+length Z X₂+(9/2)*(∑ i ∈ J, w i)-s.width) 0+loss) := by
  obtain ⟨degree,S,hinc⟩ := actual_incumbent_pair (α := α) M H hH W
    aslot bslot a b radial Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hrad hmask hMcap hεmoment hbeta hbetaTop
  obtain ⟨Cp,hCp,hpoint⟩ := natural_relative_slot_buffered_bound M H hH W aslot bslot
    haslot hWs hW Rwidth d τ εslot e κ ηheight lo hi hRw.le hd.le
    hτ hεslot he he' hκ hη hbudget
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQne hQtop hQ72
  obtain ⟨C₀,C₁,hC₀,hC₁,hinc⟩ := hinc η₀ Q hQM hQne hQtop hQ72
  let Bp : ℝ := max 1 (Cp^2)
  have hBp : 1 ≤ Bp := le_max_left _ _
  refine ⟨Bp^(Fintype.card α)*(C₀+C₁),by positivity,?_⟩
  filter_upwards [hinc] with Z hinc
  obtain ⟨hZ,hzero,hpositive⟩ := hinc
  refine ⟨hZ,?_⟩
  intro J θ w σ v t height hw hwmesh hσlo hσhi hheight hv s hQ hs low abin k
    habin habinTop hbase hT hlow hlarge hfreq hheightSource p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  obtain ⟨R,hR,hcapacity,hpay⟩ := greedy_low_selection J w (length Z X₁) (length Z X₂)
    s.width (3/4) (67/100) mesh (by norm_num) (by norm_num) hmesh.le
    (fun i _ => hw i) (fun i _ => hwmesh i)
  have hslot (z : O) (hz : s.radial.keep z) (hl : low z) (i : α) (hi : i ∈ R) :
      ‖normalizedSlot s.character s.mask 1 z (primePool M H bslot (Z^(w i)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v i) I) t (Z^(w i))‖^2 ≤
      (Bp*Z^(2*d*εslot))*Z^((67/100)*w i) := by
    rw [normalizedSlot_relative_pool M H hH]
    have hgate := hlow z hz hl
    have hscale : (Z^d)^(w i/d) = Z^(w i) := by
      rw [← Real.rpow_mul (zero_lt_one.trans hZ).le]
      congr 1
      field_simp
    have hh := hpoint Z d hZ.le hd.le le_rfl hbase hT
      s.character z (naturalRow s.character z (s.row_ne_zero z hz)) η₀ s.puncture
      s.puncture_ne_zero (naturalState_relative_nonprincipal M H hH s η₀ Q hQM hQ z hz)
      abin k habin (by linarith) hgate.maximum (w i/d) (σ i) t (v i)
      (div_nonneg (hw i) hd.le) ((div_le_iff₀ hd).mpr (by nlinarith [hwmesh i])) (hσlo i) (hσhi i)
      (by simpa only [hscale] using hlarge i (hR hi)) hgate.conductor
      (hfreq i (hR hi)) (by simpa using hheightSource)
    rw [hscale, ← Real.rpow_mul (zero_lt_one.trans hZ).le] at hh
    have hexp : d*((2*abin-1)*(w i/d)+2*εslot) = (2*abin-1)*w i+2*d*εslot := by
      field_simp
    rw [hexp] at hh
    apply hh.trans
    calc
      Cp^2*Z^((2*abin-1)*w i+2*d*εslot) ≤ Bp*Z^((67/100)*w i+2*d*εslot) :=
        mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow_of_exponent_le hZ.le
          (by nlinarith [hw i])) (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add (zero_lt_one.trans hZ)]; ring
  have hpaid := restricted_paid_incumbent M H hH W bslot a b radial Bmask L
    (Cycle25.Energy.commonMesh Mcap Bmask L εmoment) lo hi Mcap εmoment (3/4) Z η₀ Q
    degree S C₀ C₁ hC₀.le hC₁.le hzero hpositive J R hR θ w σ v t height (67/100)
    (fun _ => Bp*Z^(2*d*εslot)) hw (fun i => (hwmesh i).trans hmeshInc) hσlo hσhi
    hheight hv (fun i _ => by positivity) s hQ hs low p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hslot
  have hprod₀ := constant_removal_product R Bp Z (d*εslot) hBp hZ.le (mul_nonneg hd.le hεslot.le)
  have hprod : (∏ _i ∈ R, Bp*Z^(2*d*εslot)) ≤
      Bp^(Fintype.card α)*Z^(2*d*εslot*(Fintype.card α)) := by
    simpa only [mul_assoc] using hprod₀
  have hpay' : (67/100)*(∑ i ∈ R, w i) ≤
      (67/450)*max (length Z X₁+length Z X₂+(9/2)*(∑ i ∈ J, w i)-s.width) 0+(67/100)*mesh := by
    norm_num at hpay
    exact hpay
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  apply hpaid.trans
  calc
    _ ≤ (Bp^(Fintype.card α)*Z^(2*d*εslot*(Fintype.card α))) *
        ((C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree) *
        Z^(s.width+εmoment+(67/100)*(∑ i ∈ R, w i)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod (by positivity)) (by positivity)
    _ = Bp^(Fintype.card α)*(C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree *
        Z^(s.width+εmoment+(67/100)*(∑ i ∈ R, w i)+2*d*εslot*(Fintype.card α)) := by
      simp only [Real.rpow_add hZpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) (by positivity)


/-- Exact child-width deficits are paid together with the low-bin defect.
This permits a nominal ledger width only with its explicit nonnegative pad. -/
lemma low_nominal_width (actual nominal total pad : ℝ)
    (hpad : 0 ≤ pad) (hactual : actual ≤ nominal+pad) :
    actual+(67/450)*max (total-actual) 0 ≤
      nominal+pad+(67/450)*max (total-nominal) 0 := by
  have h := width_plus_low_defect (actual-nominal) (total-nominal) pad (67/450)
    (by norm_num) (by norm_num) hpad (by linarith)
  have he : total-nominal-(actual-nominal) = total-actual := by ring
  rw [he] at h
  linarith

/-- The mesh is chosen before the slot count. Only the small pointwise
loss per slot is chosen afterwards; it leaves the same mesh admissible. -/
lemma low_mesh_independent_of_slot_count (loss d mesh εmoment : ℝ)
    (hloss : 0 < loss) (hd : 0 < d) (hmesh : 0 ≤ mesh)
    (hmeshCap : mesh ≤ loss/4) (hεmoment : εmoment ≤ loss/4) (N : ℕ) :
    0 < loss/(8*d*(N+1)) ∧
      εmoment+(67/100)*mesh+2*d*(loss/(8*d*(N+1)))*N ≤ loss := by
  have hN : (0 : ℝ) < N+1 := by positivity
  have hratio : (N : ℝ)/(N+1) ≤ 1 := (div_le_one hN).mpr (by linarith)
  have hfee : 2*d*(loss/(8*d*(N+1)))*N = (loss/4)*((N : ℝ)/(N+1)) := by
    field_simp [hd.ne', hN.ne']
    <;> ring
  refine ⟨by positivity, ?_⟩
  rw [hfee]
  have hb := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ loss/4)
  nlinarith

#print axioms actual_joint_low_moment
#print axioms low_mesh_independent_of_slot_count
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowMoment -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.ActualMoments ; sha256 b4fac19450ff5b268fd81946730cf65dedc0722fa9154078a3ed7bc3c53d40fc -/
section





namespace OAI.SevenEighths.Cycle25ProbeFinalAssembly
noncomputable section
open scoped Classical
open Filter HeckeFamily
open Cycle25ProbeDetectorPlainMarkedFineField

/-- Fresh inverse detector parameters for the variable-κ count. -/
theorem weighted_fresh_count_parameters {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) :
    Nonempty (Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) := by
  exact Cycle25ProbeHighRowFamily.exists_count_parameters F.modulus ⊤ le_top F.S F.w
    F.smooth F.compact F.positive_support (fun x=>(F.bounded x).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support
    (fun x=>(F.bounded x).2) D.t D.t_pos

/-- Actual physical source moments from the completed energy endpoint, on the
same mesh used by the physical numerator. -/
theorem weighted_actual_source_moments {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t)
    (hfine : ∀j,D.ell j≤ Cycle25.sourceMesh D.t/200) :
    ∃J:ℝ,0≤ J ∧ ∀η:Character,∃C:ℝ,0< C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        weighted_SourceMomentBound F κplain counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  exact Cycle25ProbeFinalAssemblyCertifiedBands.weighted_source_moments F κplain hk1
    counts (Cycle25.sourceMesh D.t) (Cycle25.sourceMesh_pos D.t_pos) hfine
    (terminal_plain_input F κplain hk hk1 hbeta hκbeta)
    (terminal_zero_input F κplain hk hk1 hbeta hκbeta)
end
end OAI.SevenEighths.Cycle25ProbeFinalAssembly
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.ActualMoments -/
