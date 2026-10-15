/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.reserve_local_20261013.Bundles.B047
import Submissions.reserve_local_20261013.Bundles.B055
import Submissions.reserve_local_20261013.Bundles.B065
import Submissions.reserve_local_20261013.Bundles.B069
import Submissions.reserve_local_20261013.Bundles.B071
import Submissions.reserve_local_20261013.Bundles.B072
import Submissions.reserve_local_20261013.Bundles.B075
import Submissions.reserve_local_20261013.Bundles.B081
import Submissions.reserve_local_20261013.Bundles.B082
import Submissions.reserve_local_20261013.Bundles.B083
import Submissions.reserve_local_20261013.Bundles.B084
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AddedZero
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstDivisorCommonBound

/- BEGIN ORIGINAL MODULE Global.Numerator.ActiveFourth ; sha256 2aedaa26254101ec6ef0e92239993f4e39e37444100407efd2dbb4d067b938c6 -/
section




/-! Actual rowwise coefficient choices on one finite dilation box. Inactive
choices are replaced by a positive admissible scale before invoking the moment
bound, and their nonnegative contribution is subsequently discarded. -/
noncomputable section
set_option maxHeartbeats 1400000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace Submission20261012.Global.Numerator
open Cycle25.Numerator
open Cycle25.Weighted.Numerator Cycle25.Weighted.Numerator.PhysicalMoment
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

def fallbackCoefficientScale (b Y C Cu U m:ℝ) : ℝ := min (b*Y) (C*U^m*Y/Cu)

lemma fallback_scale_admissible (b Y C Cu U m:ℝ)
    (hb:0 < b) (hY:0 < Y) (hC:0 < C) (hCu:0 < Cu) (hU:0 < U) :
    0 < fallbackCoefficientScale b Y C Cu U m ∧
      fallbackCoefficientScale b Y C Cu U m ≤ b*Y ∧
      Cu ≤ C*U^m*(Y/fallbackCoefficientScale b Y C Cu U m) := by
  have hp : 0 < fallbackCoefficientScale b Y C Cu U m := by
    unfold fallbackCoefficientScale
    exact lt_min (mul_pos hb hY) (by positivity)
  refine ⟨hp,min_le_left _ _,?_⟩
  rw [←mul_div_assoc,le_div_iff₀ hp]
  have hh := (le_div_iff₀ hCu).mp (min_le_right (b*Y) (C*U^m*Y/Cu))
  simpa only [fallbackCoefficientScale,mul_comm Cu] using hh

/-- The concrete masked fourth-moment premise needed by the actual packet/bin
bound. All constants precede every rowwise coefficient choice. -/
theorem certified_active_box_fourth {D:Cycle25.Weighted.MomentData}
    (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (kap:ℝ) (hkaplo:7/10≤ kap) (hkaphi:kap≤3/4)
    (hkapbeta:2*HeckeZeroSupremum.beta-1≤ kap) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (G:𝓢(ℝ,ℂ)) (loss boxWidth annulusSlack b:ℝ)
    (hloss:0 < loss) (hbox:0 < boxWidth) (hann:0 < annulusSlack) (hb:0 < b)
    (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀data:∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val,
      ∀N:rows→ℝ,(∀i,0 < N i) → ∀d:ℝ,(1/2:ℝ) ≤ d → d ≤ Submission20261012.Global.h+Submission20261012.Global.rowExtension →
      ∀j∈Finset.range (coefficientBoxCount boxWidth+1),
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 < width i) →
      (∀i,width i ≤ Cycle25.sourceMesh D.t) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (∑i,width i) ≤ selectedCapacity kap ((2*(Submission20261012.Global.ly/d)-1)/(6*kap)-annulusSlack/(3*kap))
        ((j:ℝ)*boxWidth+boxWidth) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ U) →
      let Y := U^(Submission20261012.Global.ly/d)
      let Lc (i:rows) := (data i).combinedConductor/((fixedConductorConstant F.S:ℝ)*rowNorm i.val)
      (∑i:rows,‖if N i ≤ b*Y ∧
          dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
        else 0‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  obtain ⟨degree,C,hC,hmoment⟩ := certified_original_numerator_fourth F kap hkaplo hkaphi hbeta hkapbeta G loss annulusSlack 1 b 1
    hloss hann hb (by norm_num)
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,eventually_physical_cutoff_le_base b hb.le] with U hmom hcutoff
  have hU := hmom.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N hN d hd hdmax j hj T width z height hw hwmax hz hh him hselected hQ
  dsimp only
  let Y := U^(Submission20261012.Global.ly/d)
  let Ccond:ℝ := fixedConductorConstant F.S
  let Lc (i:rows) := (data i).combinedConductor/(Ccond*rowNorm i.val)
  let active (i:rows) : Prop := N i ≤ b*Y ∧
    dilationBox U boxWidth (coefficientBoxCount boxWidth) (max 1 (Lc i*N i))=j
  let m := 1-Submission20261012.Global.ly/d+(j:ℝ)*boxWidth+boxWidth
  have hY : 0 < Y := Real.rpow_pos_of_pos hUp _
  have hCcond : 0 < Ccond := by
    dsimp [Ccond]
    exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  have hNu (i:rows) : 0 < rowNorm i.val :=
    (Real.rpow_pos_of_pos hUp _).trans_le (hrows i.val i.property).1
  have hL (i:rows) : Lc i ≤ 1 := by
    apply (div_le_one (mul_pos hCcond (hNu i))).mpr
    exact (data i).combined_le_row
  have hcut : b*Y ≤ U^((coefficientBoxCount boxWidth:ℝ)*boxWidth) := by
    apply (hcutoff.2 d hd).trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU.le
      (coefficientBoxCount_extent boxWidth hbox).1
  have hcombinedActive (i:rows) (hi:active i) :
      (data i).combinedConductor ≤ Ccond*U^m*(Y/N i) := by
    have hupper := active_dilation_upper U boxWidth (Lc i) (N i) b Y
      (coefficientBoxCount boxWidth) hU.le hbox.le (hL i) (hN i).le hi.1 hcut
    have hspec := (dilationBox_spec U boxWidth hU.le hbox.le (coefficientBoxCount boxWidth)
      (max 1 (Lc i*N i)) (le_max_left _ _) hupper).2
    rw [hi.2] at hspec
    have hb' : max 1 ((data i).combinedConductor*N i/(Ccond*rowNorm i.val)) ≤
        U^((j:ℝ)*boxWidth+boxWidth) := by
      have hprod : Lc i*N i = (data i).combinedConductor*N i/(Ccond*rowNorm i.val) := by
        dsimp only [Lc]
        ring
      have hexp : ((j:ℝ)+1)*boxWidth = (j:ℝ)*boxWidth+boxWidth := by ring
      rw [hprod,hexp] at hspec
      exact hspec
    have hc := combined_scale_of_dilation (data i).combinedConductor Ccond (rowNorm i.val)
      (N i) Y U (Submission20261012.Global.ly/d) ((j:ℝ)*boxWidth+boxWidth)
      hCcond (hNu i) (hN i) hUp (hrows i.val i.property).2 rfl hb'
    simpa only [m,add_assoc] using hc
  let Nsafe (i:rows) := if active i then N i
    else fallbackCoefficientScale b Y Ccond (data i).combinedConductor U m
  have hsafe (i:rows) : 0 < Nsafe i ∧ Nsafe i ≤ b*Y ∧
      (data i).combinedConductor ≤ Ccond*U^m*(Y/Nsafe i) := by
    dsimp only [Nsafe]
    split_ifs with hi
    · exact ⟨hN i,hi.1,hcombinedActive i hi⟩
    · exact fallback_scale_admissible b Y Ccond (data i).combinedConductor U m
        hb hY hCcond (data i).combined_pos hUp
  obtain ⟨hm,hmmax⟩ := physical_coefficient_box_geometry d boxWidth annulusSlack
    hd hdmax hbox hann.le hsmall j hj
  have hcapacity := physical_reflected_capacity_or_empty_subtype T width kap (Submission20261012.Global.ly/d)
    ((j:ℝ)*boxWidth) boxWidth annulusSlack (by linarith) hw hselected
  have hQ' (i:rows) : ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
      (U^(width s)) (z s)‖ ≤ (1:ℝ)*U^(1:ℝ) := by simpa using hQ i
  have hbound := hmom.2 rows hrows data Nsafe Y m hY (fun i=>⟨(hsafe i).1,(hsafe i).2.1⟩)
    hm hmmax (fun i=>(hsafe i).2.2) T width z height (fun i=>(hw i).le) hwmax hz hh him
    (by simpa only [m] using hcapacity) hQ'
  apply (Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>?_)).trans hbound
  change ‖if active i then _ else 0‖^4*_ ≤ _
  by_cases hi:active i
  · simp only [hi,ite_true,Nsafe,Y]
    exact le_rfl
  · simp only [hi,ite_false,norm_zero,zero_pow (by norm_num:4≠0),zero_mul]
    positivity

end Submission20261012.Global.Numerator
end

/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

-- New geometry wrapper, 13 October 2026; inherited analytic core unchanged.
end
/- END ORIGINAL MODULE Global.Numerator.ActiveFourth -/

/- BEGIN ORIGINAL MODULE Analytic.ActualExtractedLocalErrors ; sha256 bf2e972c8f0b74904185fd0aa779429f6f8e6d4079167f55ba14e92165025f0c -/
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
local instance actualExtractedLocalErrorsDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance actualExtractedLocalErrorsFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem actual_firstExtractedErrors_local_bound
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
    Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ))≤1/250 →
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
  obtain ⟨Uprofile,Jheight,hactual⟩ := actual_firstExtractedErrors_power_from_caps (α := α) M H hH
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
  intro Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
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
  have hbound := hZ.2 Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
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

#print axioms actual_firstExtractedErrors_local_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualExtractedLocalErrors -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstCoarse ; sha256 3de274af28013f98493b989ca670d1c9fba0d8fac435ed1821520c8e34b6a8f4 -/
section




/-! A literal first-common Fourier-tail envelope. The coefficient mass and
column norms come from the actual original input, uniformly in heights. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstDivisorCommonBound CenteredMomentGaussEnergy
open CenteredMomentAbsoluteEnergy CenteredMomentAddedZero CenteredMomentSourceRow
open CenteredMomentFirstPhysicalSource CenteredMomentFirstSectors CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentExceptionalAmplitudePair
open QuadraticInitialBound
local notation "O" => HeckeFamily.O
local instance firstCoarseDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma gauss_pair_absolute (u v : O) (hu : Supported (Ideal.span {u}))
    (hv : Supported (Ideal.span {v})) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) :
    ‖∑' z : O,(gaussRow u hu z*star (gaussRow v hv z))*W (‖eisEmbedding z‖^2/K)‖ ≤
      (Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ)*Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ))*
        (diagonalControl W*max 1 K) := by
  have hs := (gaussRow_pair_summable u v hu hv W K hK).norm
  calc
    _ ≤ ∑' z : O,‖(gaussRow u hu z*star (gaussRow v hv z))*W (‖eisEmbedding z‖^2/K)‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' z : O,
        (Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ)*Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ))*
          ‖W (‖eisEmbedding z‖^2/K)‖ := by
      apply hs.tsum_le_tsum _ ((radial_norm_summable W K hK).mul_left _)
      intro z
      simp only [norm_mul,norm_star]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (gaussRow_norm_le u hu z) (gaussRow_norm_le v hv z)
          (norm_nonneg _) (Real.sqrt_nonneg _)) (norm_nonneg _)
    _ = _ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all W K hK) (by positivity)

lemma pairMajorant_absolute {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (b : α → ℝ) (hb : ∀ i ∈ S, 0 ≤ b i)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) :
    pairMajorant S a ha b W K ≤
      (diagonalControl W*max 1 K)*
        (∑ i ∈ S,b i*Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ))^2 := by
  unfold pairMajorant
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, (b i*b j)*
        (Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ)*Real.sqrt (Ideal.absNorm (Ideal.span {a j}) : ℝ))*
          (diagonalControl W*max 1 K) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact (mul_le_mul_of_nonneg_left (gauss_pair_absolute (a i) (a j) (ha i) (ha j) W K hK)
        (mul_nonneg (hb i hi) (hb j hj))).trans_eq (by ring)
    _ = _ := by
      rw [sq,Finset.sum_mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The common ideal contributes the precise inverse norm, even to this
coarse estimate. Zero coefficients impose no column-norm hypothesis. -/
theorem common_coarse_absolute {ι : Type*} [Fintype ι]
    (s : OriginalData ι) (C : Ideal O) (hC : Supported C) (L : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K H : ℝ) (hK : 0 < K) (hH : 0 ≤ H)
    (hsource : ∀ I, s.beta I ≠ 0 → (I.absNorm : ℝ) ≤ H) :
    coarse s C hC L W K ≤
      (diagonalControl W*max 1 K)*(H/(C.absNorm : ℝ))*(sourceAbsoluteMass s.columns s.beta)^2 := by
  let Q := residualPool C hC.1 s.columns
  let b : supportedColumns Q → ℝ := fun I =>
    ‖if IsCoprime C (I:Ideal O) ∧ L ∣ (I:Ideal O) then s.beta (C*I) else 0‖
  have hc := CenteredMomentFirstScale.norm_pos C hC.1
  have hm : (∑ I : supportedColumns Q,
      b I*Real.sqrt (Ideal.absNorm (Ideal.span {sourceGenerator Q I}) : ℝ)) ≤
      Real.sqrt (H/(C.absNorm : ℝ))*sourceAbsoluteMass s.columns s.beta := by
    calc
      _ ≤ ∑ I : supportedColumns Q, Real.sqrt (H/(C.absNorm:ℝ))*‖s.beta (C*I)‖ := by
        apply Finset.sum_le_sum
        intro I hI
        rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2]
        by_cases hz : s.beta (C*I) = 0
        · simp only [b,hz,ite_self,norm_zero,zero_mul,mul_zero,le_refl]
        · have hN := hsource (C*I) hz
          simp only [map_mul,Nat.cast_mul] at hN
          have hn : (I.val.absNorm:ℝ) ≤ H/(C.absNorm:ℝ) :=
            (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hN)
          have hb : b I ≤ ‖s.beta (C*I)‖ := by dsimp only [b];split_ifs <;> simp
          exact (mul_le_mul hb (Real.sqrt_le_sqrt hn) (Real.sqrt_nonneg _) (norm_nonneg _)).trans_eq (by ring)
      _ = Real.sqrt (H/(C.absNorm:ℝ))*∑ I : supportedColumns Q, ‖s.beta (C*I)‖ := by rw [Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        rw [Finset.sum_coe_sort (supportedColumns Q) (fun I => ‖s.beta (C*I)‖)]
        apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun I _ _ => norm_nonneg (s.beta (C*I)))).trans
        exact residual_absolute_mass_le_all s.columns s.beta C hC.1
  have hbase := pairMajorant_absolute Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    b (fun _ _ => norm_nonneg _) W K hK
  apply hbase.trans
  have hsum : 0 ≤ ∑ I : supportedColumns Q,
      b I*Real.sqrt (Ideal.absNorm (Ideal.span {sourceGenerator Q I}) : ℝ) :=
    Finset.sum_nonneg (fun I _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum hm 2)
    (mul_nonneg (diagonalControl_nonneg W) (by positivity))).trans_eq
  rw [mul_pow,Real.sq_sqrt (div_nonneg hH hc.le)]
  ring

/-- The literal original coefficient bound pays the first Fourier tail;
all dependence on characters, Fourier heights, and masks has disappeared. -/
theorem original_common_coarse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (R seed C L : Ideal O) (hC : Supported C)
    (W : 𝓢(ℝ,ℂ)) (K H B₁ B₂ : ℝ) (hK : 0 < K) (hH : 0 ≤ H)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hz₁ : s.W₁ 0 = 0) (hz₂ : s.W₂ 0 = 0)
    (hb₁ : ∀ x, ‖s.W₁ x‖ ≤ B₁) (hb₂ : ∀ x, ‖s.W₂ x‖ ≤ B₂)
    (hsource : sourceRadius s ≤ H) :
    coarse (original s R seed) C hC L W K ≤
      (volume s.toData/(C.absNorm : ℝ))*
        (diagonalControl W*(originalAbsoluteProfile s B₁ B₂)^2*max 1 K*H*volume s.toData) := by
  have hc := CenteredMomentFirstScale.norm_pos C hC.1
  have hh := common_coarse_absolute (original s R seed) C hC L W K H hK hH
    (fun I hI => (original_column_norm s R seed I hz₁ hz₂ hI).2.trans hsource)
  have hm := original_absolute_mass s R seed B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (sourceAbsoluteMass_nonneg _ _) hm 2)
    (mul_nonneg (mul_nonneg (diagonalControl_nonneg W) (by positivity))
      (div_nonneg hH hc.le))).trans_eq
  ring

#print axioms original_common_coarse
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstCoarse -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowPhysicalSource ; sha256 56877da28597eb2502a0739f50bff3031779dad9fef9fa0ab4db21342093d3b3 -/
section











/-! The actual low-bin source coefficients after both common and divisor
allocations. The source dictionary map returns surviving indices to the
original fixed slot system while preserving the same low-bin indicator. -/
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
local instance lowPhysicalSourceFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α]

open CanonicalQuadraticSieve CenteredMomentSourceLiveColumn
open CenteredMomentCommonRadialSource CenteredMomentSourceProfileMass CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialCost CenteredMomentCommonLinearNormalization

open ActualEisensteinCubic RayFourExpansion CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentEnergyChildState
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit CenteredMomentExceptionalAmplitudePair

theorem actual_second_low_source
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
    (ηfirst : Character) (parentLoss : ℝ) (hparentLoss : 0 < parentLoss) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (v height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
      ∀ (p : Profiles a b) (src : Input α), Matches M H hH src η₀ θ w σ freq W bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      p.profile 0 = src.W₁ → p.profile 1 = src.W₂ →
      (∀ i,src.lo i = loInput i) → (∀ i,src.hi i = hiInput i) →
      src.X₁ ≤ Z^L → src.X₂ ≤ Z^L → src.Y₁ ≤ Z^L → src.Y₂ ≤ Z^L →
      ∀ (C₁ D₁ C₂ D₂ Rmask seed Lproj : Ideal O) (hC₁ : Supported C₁)
        (hD₁ : D₁ ≠ 0) (hC₂ : Supported C₂) (hD₂ : Supported D₂),
      primeSupport C₂ = primeSupport D₂ →
      ∀ (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂) (parent : Character),
      (parent = F.left ∨ parent = F.right) →
      ∀ (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
      Family parent C₂ D₂ hC₂ hD₂ U family →
      ∀ (T : Ideal O) (hTpick : T = C₂ ∨ T = D₂),
      Rmask ≠ 0 → seed ∣ C₁*T → Squarefree Lproj →
      ((C₁*T).absNorm : ℝ) ≤ Z^Bcommon → (Lproj.absNorm : ℝ) ≤ Z^Bcommon →
      ∀ (t : ℝ) (columns : Finset (Ideal O)) (β : Ideal O → ℂ) (rows : Finset O)
        (Wrad : 𝓢(ℝ,ℂ)) (Kcut : ℝ) (n : Fin 4 → ℤ)
        (Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip : ℝ),
      0 < Kcut → 0 < Hsource → Real.logb Z Hsource ≤ A+sourceLoss →
      A+(7/2)*(∑ i,w i) ≤ Mparent+g → Real.logb Z (volume src.toData) ≤ A →
      (Fintype.card α : ℝ)*Real.logb Z (max 1 src.upper) ≤ profileLoss →
      0 ≤ g → g ≤ 1/250 → 0 ≤ omegaLoss → 3/500 ≤ allowance →
      0 ≤ profileLoss → 0 ≤ clip → Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      let c := Real.logb Z (C₁.absNorm : ℝ)
      let d₁ := Real.logb Z (D₁.absNorm : ℝ)
      let r₁ := Real.logb Z (normValue (activeConductor C₁ D₁))
      let e₁ := Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E₁))
      let radius := frequencyRadius (jointSecondNominal C₁ Hsource Z A c d₁ r₁ e₁ Mparent (3/500) omegaLoss) Z ξ
      let nominal := jointLowNominal Mparent c d₁ (3/500) omegaLoss
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ))
      let pad := 2*sourceLoss+parentLoss+ξ/2+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))
      0 ≤ pad → nominal+pad ≤ Mcap →
      pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 1/45000 →
      ∀ hne : physicalBlock parent t columns β C₂ D₂ hC₂ hD₂ U radius rows Wrad Kcut n ≠ 0,
      ∀ χ : RayCharacter,
      let s := actualState (τ := family) t columns β radius rows Wrad Kcut n hne Z Bmask hZ
        χ (internalQ Q η₀) 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hmask)
      ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : (supportedNaturalState s).radial.keep z, low z →
        NaturalLowGate M H hH (supportedNaturalState s) η₀ Q hQM rfl d τ e abin k z hz) →
      (∀ i, |v+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      sourceEnergy (withHeight src s.character v) (restrictedLowRadial s.radial low)
        (C₁*T) ((supported_mul_iff _ _).mpr ⟨hC₁,second_selected_supported hC₂ hD₂ hTpick⟩) Rmask seed Lproj ≤
        Cbound*((Rmask*(C₁*T)).radical.absNorm : ℝ)^εmask*profileCost src*diagonalControl s.radial.profile*
          (p.control S)^2*(1+|v|+height)^degree *
          Z^(δcommon+(nominal+allowance-1/45000))/(((C₁*T).absNorm : ℝ)*Lproj.absNorm) := by
  obtain ⟨degree,S,hmain⟩ := actual_live_low_source M H hH W
    aslot bslot a b 2 Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb (by norm_num) hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hmain,eventually_actual_low_state_width ηfirst parentLoss hparentLoss] with Z hmain hwidth
  intro hZ θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ C₁ D₁ C₂ D₂ Rmask seed Lproj hC₁ hD₁ hC₂ hD₂ hCD₂
    E₁ ξ₁ ξ₂ F parent hparent U family hfamily T hTpick hR hseed hLproj hCcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    c d₁ r₁ e₁ radius nominal pad hpad hMcapSource hbudgetSource hne χ s low abin k
    habin habinTop hbase hT hlow hfreqGate hheightSource
  have hswidth : s.width ≤ nominal+pad := hwidth hZ C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F parent hparent
    C₂ D₂ hC₂ hD₂ U family hfamily t columns β rows Wrad Kcut n Hsource A Mparent omegaLoss ξ sourceLoss Bmask
    hKcut hHsource hmask hsource hne χ (internalQ Q η₀)
  have hgeometry := actual_low_live_source_geometry src C₁ D₁ C₂ D₂ Rmask hC₁.1 hD₁ hC₂ hD₂ hCD₂ U T hTpick
    Z A Mparent g L omegaLoss profileLoss hZ w hw hcapacity hvolume hprofile hX₁ hX₂ hY₁ hY₂ s.character v
  exact hmain.2 θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq s rfl rfl
    (hswidth.trans hMcapSource) low abin k habin habinTop hbase hT hlow hfreqGate hheightSource
    p src hmatch hhi hMs hp₁ hp₂ hloInput hhiInput (C₁*T) Rmask seed Lproj
    ((supported_mul_iff _ _).mpr ⟨hC₁,second_selected_supported hC₂ hD₂ hTpick⟩) hR hseed hLproj hCcap hLcap
    A (Mparent+g) nominal pad g allowance (omegaLoss+profileLoss) clip hpad hswidth hg hgCap
    hallowance (add_nonneg homega hprofile0) hclip hclipCost hbudgetSource hgeometry

#print axioms actual_second_low_source
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowPhysicalSource -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSelectedPhysicalSource ; sha256 75fb6e58646cf681e7eeb8d32f7b3513cea12c69b2e0033b45beafc39c4ef277 -/
section











/-! The actual low-bin source coefficients after both common and divisor
allocations. The source dictionary map returns surviving indices to the
original fixed slot system while preserving the same low-bin indicator. -/
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
local instance selectedLowPhysicalSourceFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α]

open CanonicalQuadraticSieve CenteredMomentSourceLiveColumn
open CenteredMomentCommonRadialSource CenteredMomentSourceProfileMass CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialCost CenteredMomentCommonLinearNormalization

open ActualEisensteinCubic RayFourExpansion CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentEnergyChildState
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit CenteredMomentExceptionalAmplitudePair

theorem actual_selected_second_low_source
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
    (ηfirst : Character) (parentLoss : ℝ) (hparentLoss : 0 < parentLoss) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (v height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
      ∀ (p : Profiles a b) (src : Input α), Matches M H hH src η₀ θ w σ freq W bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      p.profile 0 = src.W₁ → p.profile 1 = src.W₂ →
      (∀ i,src.lo i = loInput i) → (∀ i,src.hi i = hiInput i) →
      src.X₁ ≤ Z^L → src.X₂ ≤ Z^L → src.Y₁ ≤ Z^L → src.Y₂ ≤ Z^L →
      ∀ (P₁ Q₁ : Ideal O) (hP₁ : Supported P₁),
      ∀ (C₁ D₁ C₂ D₂ Rmask seed Lproj : Ideal O) (hC₁ : Supported C₁)
        (hD₁ : D₁ ≠ 0) (hC₂ : Supported C₂) (hD₂ : Supported D₂),
      primeSupport C₂ = primeSupport D₂ →
      ∀ (E₁ : Finset (CommonIndex P₁ Q₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂) (parent : Character),
      (parent = F.left ∨ parent = F.right) →
      ∀ (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
      Family parent C₂ D₂ hC₂ hD₂ U family →
      ∀ (T : Ideal O) (hTpick : T = C₂ ∨ T = D₂),
      Rmask ≠ 0 → seed ∣ C₁*T → Squarefree Lproj →
      ((C₁*T).absNorm : ℝ) ≤ Z^Bcommon → (Lproj.absNorm : ℝ) ≤ Z^Bcommon →
      ∀ (t : ℝ) (columns : Finset (Ideal O)) (β : Ideal O → ℂ) (rows : Finset O)
        (Wrad : 𝓢(ℝ,ℂ)) (Kcut : ℝ) (n : Fin 4 → ℤ)
        (Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip : ℝ),
      0 < Kcut → 0 < Hsource → Real.logb Z Hsource ≤ A+sourceLoss →
      A+(7/2)*(∑ i,w i) ≤ Mparent+g → Real.logb Z (volume src.toData) ≤ A →
      (Fintype.card α : ℝ)*Real.logb Z (max 1 src.upper) ≤ profileLoss →
      0 ≤ g → g ≤ 1/250 → 0 ≤ omegaLoss → 3/500 ≤ allowance →
      0 ≤ profileLoss → 0 ≤ clip → Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      let c := Real.logb Z (C₁.absNorm : ℝ)
      let d₁ := Real.logb Z (D₁.absNorm : ℝ)
      let r₁ := Real.logb Z (normValue (activeConductor P₁ Q₁))
      let e₁ := Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex P₁ Q₁ => P.val) E₁))
      let radius := frequencyRadius (jointSecondNominal C₁ Hsource Z A c d₁ r₁ e₁ Mparent (3/500) omegaLoss) Z ξ
      let nominal := jointLowNominal Mparent c d₁ (3/500) omegaLoss
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ))
      let pad := 2*sourceLoss+parentLoss+ξ/2+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))
      0 ≤ pad → nominal+pad ≤ Mcap →
      pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 1/45000 →
      ∀ hne : physicalBlock parent t columns β C₂ D₂ hC₂ hD₂ U radius rows Wrad Kcut n ≠ 0,
      ∀ χ : RayCharacter,
      let s := actualState (τ := family) t columns β radius rows Wrad Kcut n hne Z Bmask hZ
        χ (internalQ Q η₀) 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hmask)
      ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : (supportedNaturalState s).radial.keep z, low z →
        NaturalLowGate M H hH (supportedNaturalState s) η₀ Q hQM rfl d τ e abin k z hz) →
      (∀ i, |v+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      sourceEnergy (withHeight src s.character v) (restrictedLowRadial s.radial low)
        (C₁*T) ((supported_mul_iff _ _).mpr ⟨hC₁,second_selected_supported hC₂ hD₂ hTpick⟩) Rmask seed Lproj ≤
        Cbound*((Rmask*(C₁*T)).radical.absNorm : ℝ)^εmask*profileCost src*diagonalControl s.radial.profile*
          (p.control S)^2*(1+|v|+height)^degree *
          Z^(δcommon+(nominal+allowance-1/45000))/(((C₁*T).absNorm : ℝ)*Lproj.absNorm) := by
  obtain ⟨degree,S,hmain⟩ := actual_live_low_source M H hH W
    aslot bslot a b 2 Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb (by norm_num) hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hmain,eventually_selected_low_state_width ηfirst parentLoss hparentLoss] with Z hmain hwidth
  intro hZ θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ C₂ D₂ Rmask seed Lproj hC₁ hD₁ hC₂ hD₂ hCD₂
    E₁ ξ₁ ξ₂ F parent hparent U family hfamily T hTpick hR hseed hLproj hCcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    c d₁ r₁ e₁ radius nominal pad hpad hMcapSource hbudgetSource hne χ s low abin k
    habin habinTop hbase hT hlow hfreqGate hheightSource
  have hswidth : s.width ≤ nominal+pad := hwidth hZ P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F parent hparent
    C₁ D₁ hC₁ C₂ D₂ hC₂ hD₂ U family hfamily t columns β rows Wrad Kcut n Hsource A Mparent omegaLoss ξ sourceLoss Bmask
    hKcut hHsource hmask hsource hne χ (internalQ Q η₀)
  have hgeometry := actual_low_live_source_geometry src C₁ D₁ C₂ D₂ Rmask hC₁.1 hD₁ hC₂ hD₂ hCD₂ U T hTpick
    Z A Mparent g L omegaLoss profileLoss hZ w hw hcapacity hvolume hprofile hX₁ hX₂ hY₁ hY₂ s.character v
  exact hmain.2 θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq s rfl rfl
    (hswidth.trans hMcapSource) low abin k habin habinTop hbase hT hlow hfreqGate hheightSource
    p src hmatch hhi hMs hp₁ hp₂ hloInput hhiInput (C₁*T) Rmask seed Lproj
    ((supported_mul_iff _ _).mpr ⟨hC₁,second_selected_supported hC₂ hD₂ hTpick⟩) hR hseed hLproj hCcap hLcap
    A (Mparent+g) nominal pad g allowance (omegaLoss+profileLoss) clip hpad hswidth hg hgCap
    hallowance (add_nonneg homega hprofile0) hclip hclipCost hbudgetSource hgeometry

#print axioms actual_selected_second_low_source
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSelectedPhysicalSource -/

/- BEGIN ORIGINAL MODULE Analytic.JointPhysicalOriginalVolume ; sha256 bd9505ac1838cd5ee9cf1ef247685c6e571b59c371849442a04bc3c4b509b85f -/
section


/-! The sector denominator is converted back to the original source volume
exactly, before using a volume interval. No actual common norm is frozen. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily RayFourExpansion
local notation "O" => HeckeFamily.O

theorem secondPrecountFactor_change_volume (V H P : ℝ) (hV : V ≠ 0) (hH : H ≠ 0)
    (C D : Ideal O) (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
    (K : ℝ) (n : Fin 4 → ℤ) :
    secondPrecountFactor V P C D U K n = (H/V)*secondPrecountFactor H P C D U K n := by
  unfold secondPrecountFactor
  simp only [div_eq_mul_inv,mul_inv_rev]
  field_simp

theorem sector_original_volume_ratio (Z A c volumeLoss V : ℝ)
    (hZ : 1 < Z) (hV : Z^(A-volumeLoss) ≤ V) :
    Z^(A-c)/V ≤ Z^(-c+volumeLoss) := by
  have hz := zero_lt_one.trans hZ
  calc
    _ ≤ Z^(A-c)/Z^(A-volumeLoss) := by gcongr
    _ = _ := by rw [←Real.rpow_sub hz]; congr 1; ring

namespace CommonSecondKernelLabel
variable {Slot : Type*} [Fintype Slot]

theorem physicalRowTerm_change_volume (s : CommonSecondKernelLabel Slot)
    (V H P : ℝ) (hV : V ≠ 0) (hH : H ≠ 0)
    (t : ℝ) (z : O) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (n : Fin 4 → ℤ) (D : Ideal O) :
    s.physicalRowTerm V P t z W K R n D =
      ((H/V : ℝ) : ℂ)*s.physicalRowTerm H P t z W K R n D := by
  simp only [physicalRowTerm,secondPrecountFactor_change_volume V H P hV hH,
    Complex.ofReal_mul]
  ring

end CommonSecondKernelLabel

theorem physical_source_sum_change_volume {α Slot : Type*} [Fintype Slot]
    (qs : Finset α) (s : α → CommonSecondKernelLabel Slot)
    (t K Radius : α → ℝ) (z : α → O) (n : α → Fin 4 → ℤ) (W : 𝓢(ℝ,ℂ))
    (V H P : ℝ) (hV : 0 < V) (hH : 0 < H) :
    (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ∑ q ∈ qs, ∑ D ∈ (s q).physicalProjectors,
      ‖((s q).withRays χ ξ).physicalRowTerm V P (t q) (z q) W (K q) (Radius q) (n q) D‖) =
    (H/V)*(∑ χ : RayCharacter, ∑ ξ : RayCharacter, ∑ q ∈ qs, ∑ D ∈ (s q).physicalProjectors,
      ‖((s q).withRays χ ξ).physicalRowTerm H P (t q) (z q) W (K q) (Radius q) (n q) D‖) := by
  simp only [CommonSecondKernelLabel.physicalRowTerm_change_volume _ V H P hV.ne' hH.ne',
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hH hV),Finset.mul_sum]

#print axioms physical_source_sum_change_volume
#print axioms sector_original_volume_ratio
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointPhysicalOriginalVolume -/
