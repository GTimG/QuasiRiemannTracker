/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.local44_20261013.Bundles.B033
import Submissions.local44_20261013.Bundles.B047
import Submissions.local44_20261013.Bundles.B053
import Submissions.local44_20261013.Bundles.B064
import Submissions.local44_20261013.Bundles.B065
import Submissions.local44_20261013.Bundles.B067
import Submissions.local44_20261013.Bundles.B069
import Submissions.local44_20261013.Bundles.B075
import Submissions.local44_20261013.Bundles.B077
import Submissions.local44_20261013.Bundles.B078
import Submissions.local44_20261013.Bundles.B081
import Submissions.local44_20261013.Bundles.B082
import Submissions.local44_20261013.Bundles.B083
import Submissions.local44_20261013.Bundles.B084
import Submissions.local44_20261013.Bundles.B085
import Submissions.local44_20261013.Bundles.B087
import Submissions.local44_20261013.Bundles.B089
import Submissions.local44_20261013.Bundles.B091
import Submissions.local44_20261013.Bundles.B092
import Submissions.local44_20261013.Bundles.B093
import Submissions.local44_20261013.Bundles.B094
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGaussianRemote
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FixedQForcingCount

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowGaussianRemote ; sha256 061f3bddf9e4f44c6979ff1aa1ac90813aea55da1ca51b31975afbb268eaa9cc -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowGaussianRemote.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical SchwartzMap
namespace LowProbe
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma slotProduct_subtype {K : ℕ} (p : Fin K→O) (J : Finset (Fin K)) :
    slotProduct p J=∏i : J,p i.val := by rw [Finset.prod_coe_sort];rfl

lemma eventually_low_physical_scales {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (hsum : ∑i,ell i≤ Submission20261012.Global.ell) (b : ℝ) :
    ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
      ∀(slots : Fin K→Finset O),(∀i x,x∈slots i→x≠0)→
      (∀i x,x∈slots i→elementNorm x≤ b*Z^(ell i))→
      ∀(J : Finset (Fin K))(p : ∀i,slots i),
      1≤ Z^(Submission20261012.Global.lx:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) ∧
      1≤ Z^(Submission20261012.Global.ly:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) := by
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<((Submission20261012.Global.lx-Submission20261012.Global.ell):ℝ) from Submission20261012.Global.x_rescaled_pos)).eventually
      (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro slots hn hnorm J p
  have hl : 0< elementNorm (slotProduct (fun i=>(p i).val) J) :=
    slotProduct_norm_pos _ (fun i=> hn i _ (p i).property) J
  have hb := lowUnselectedProduct_norm_bound ell hell hsum (max 1 b) Z (le_max_left _ _) hZ.le
    slots (fun i n hm=>(hnorm i n hm).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    J (fun i=> p i.val)
  rw [←slotProduct_subtype (fun i=>(p i).val) J] at hb
  have hLX : elementNorm (slotProduct (fun i=>(p i).val) J)≤ Z^(Submission20261012.Global.lx:ℝ) := by
    apply hb.trans
    calc
      _≤ Z^((Submission20261012.Global.lx-Submission20261012.Global.ell):ℝ)*Z^(Submission20261012.Global.ell:ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)]; congr 1; ring
  constructor
  · exact (one_le_div hl).mpr hLX
  · exact (one_le_div hl).mpr (hLX.trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [Submission20261012.Global.b_pos,Submission20261012.Global.length_difference])))

lemma low_remote_power (Z ell ε : ℝ) (N : ℕ) (hZ : 1≤ Z) (hell : ell≤ Submission20261012.Global.ell)
    (hN : (4+2*Submission20261012.Global.ell)≤(ε/2)*(N:ℝ)) :
    Z*(Z^(1+ell))^2/(Z^(ε/2))^N≤ Z^(-1:ℝ) := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hsq : (Z^(1+ell))^2=Z^(2*(1+ell)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    congr 1
    push_cast
    ring
  have hn : (Z^(ε/2))^N=Z^((ε/2)*(N:ℝ)) := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  rw [hsq,hn,show Z*Z^(2*(1+ell))=Z^(1+2*(1+ell)) by rw [Real.rpow_add hz,Real.rpow_one],←Real.rpow_sub hz]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

def lowRemote (Z ell ε T : ℝ) : Prop :=
  T/Z^(1+ell)≤(Z^(ε/2))⁻¹ ∨ Z^(ε/2)≤ T/Z^(1+ell)

theorem low_remote_gaussian_dyads (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Submission20261012.Global.ell)
    (b ε : ℝ) (hε : 0<ε) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(η : HeckeFamily.Character)(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=> if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
          W (fun i=> Z^(ell i)) J (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖ else 0
      Summable f ∧ (∑'j : ℕ,f j)≤ C*Z^(-1:ℝ) := by
  have hep : 0<ε/2 := by linarith
  obtain ⟨N,hN⟩ := exists_nat_gt (((4+2*Submission20261012.Global.ell):ℝ)/(ε/2))
  have hN' : ((4+2*Submission20261012.Global.ell):ℝ)≤(ε/2)*(N:ℝ) := by
    have hh := (div_lt_iff₀ hep).mp hN
    nlinarith
  obtain ⟨Cg,hCg,he⟩ := gaussianPhysicalFamily_remote_polynomial V hV N
    a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  let q := elementNorm (calibrationForSet S hS).generator
  let C0 := Cg*(q*(128*max 1 b)^K)
  have hq : 0< q := calibration_elementNorm_pos _
  refine ⟨C0,by dsimp [C0];positivity,?_⟩
  filter_upwards [eventually_low_physical_scales ell hell hsum b] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro η T hT hnorm J W hW
  dsimp only [lowRemote]
  have hz : 0< Z := lt_trans zero_lt_one hZ.1
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=> canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈canonicalSlotSupport (T i)→elementNorm n≤ b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hs := hZ.2 _ hslots hnormE J
  have hh := he η S hS W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    hW0 hW1 hWB0 hWB1 (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
    (fun p=> compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J)
    (fun p=> Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
    (fun p=> Z^(Submission20261012.Global.lx:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p=> Z^(Submission20261012.Global.ly:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p _=>(hs p).1) (fun p _=>(hs p).2)
    (fun i : SelectedSlot J=> W i.val) (fun p i=> elementNorm (p i.val).val/Z^(ell i.val))
    (Z^(1+lowSelectedLength ell J)) (Z^(ε/2)) (by positivity) (Real.one_le_rpow hZ.1.le hep.le)
  simp only [←lowCommonDyad_eq_family] at hh
  refine ⟨?_,?_⟩
  · convert hh.1 using 1
    funext j
    split_ifs with h <;> simp_all only [ite_true, ite_false]
  · have hhFinal := hh.2.trans (show _≤ C0*Z^(-1:ℝ) from by
      have hm := compensation_scale_mass_bound η (calibrationForSet S hS) ell hell hsum b Z hZ.1.le T hT hnorm J W hW
      calc
        _≤ Cg*((q*(128*max 1 b)^K)*Z)*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N := by gcongr
        _=C0*(Z*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N) := by dsimp [C0];ring
        _≤_ := mul_le_mul_of_nonneg_left (low_remote_power Z (lowSelectedLength ell J) ε N hZ.1.le
          (by have hb := lowLength_bounds ell hell hsum J;linarith) hN') (by dsimp [C0];positivity))
    convert hhFinal using 1
    apply tsum_congr
    intro j
    split_ifs with h <;> simp_all only [ite_true, ite_false]

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowGaussianRemote -/

/- BEGIN ORIGINAL MODULE Analytic.ActualAllocatedErrorUniform ; sha256 077e82802e33cdbe166a24e6646a5f0adde73e4812aa751dd972aa906a4b60ce -/
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
local instance actualAllocatedErrorUniformDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance actualAllocatedErrorUniformFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem actual_allocated_extracted_errors_uniform
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
    (hsaving : 0 ≤ saving):
    ∃ Calloc : ℝ, 0 < Calloc ∧
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
    Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ))≤37/10000 →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh
    ∀ Bfirst heightCap : ℝ, 0 ≤ heightCap → |t| ≤ heightCap →
    (C.absNorm : ℝ) ≤ Z^Bfirst → εalloc*Bfirst ≤ 1/10000 →
    paid ≤ 1/10000 → delta+reserve ≤ 1/1000 → εsrc*Mvolume ≤ 1/1000 →
    allocatedExtractedErrors N src C R0 seed τ t upper Z
      (Real.logb Z (D.absNorm : ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve P family/
      ((τ.modulus.absNorm : ℝ)*(volume src/(C.absNorm : ℝ)^2)*Z^(allowance C D Z)) ≤
      Calloc*Cbound*(profile.control Uprofile)^2*(1+heightCap+height)^Jheight*mass src^2*
        Z^(-1/2500 : ℝ)/(seed.absNorm : ℝ) := by
  obtain ⟨Dalloc,hDalloc,Uprofile,Jheight,hactual⟩ := actual_allocated_extracted_errors (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ Sbad hbad sigma cost hsigma hξsmall hcost hsigma_eq
    Avol Dscale Pmask qmoving εgeo hεgeo hbudget εalloc hεalloc
  let weights : Fin 4 → ℝ := fun j => (upper^N)^(powers εsrc j)
  let Calloc := Dalloc*(56*1872*(Fintype.card RayCharacter : ℝ))*(∑j,weights j)
  have hweights (j : Fin 4) : 0 < weights j := by
    dsimp [weights]
    positivity
  have hsum : 0 < ∑j,weights j := Finset.sum_pos (fun j _ => hweights j) Finset.univ_nonempty
  have hCalloc : 0 < Calloc := by dsimp [Calloc]; positivity
  refine ⟨Calloc,hCalloc,Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hactualZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    C D R0 hC hD hCD E τ t hmod K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hP hslot family hrad hfamily
  intro hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv hconductorCap seed hseed hseed0 hseedcap
    profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip
    hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂ hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
  intro Bfirst heightCap hheightCap ht hCcap hallocSmall hpaid hfrequency hepsSmall
  have hh := hZ.2 Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    C D R0 hC hD hCD E τ t hmod K delta reserve asource hK hasource hdelta hreserve haSource
    hP hslot family hrad hfamily hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv hconductorCap
    seed hseed hseed0 hseedcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂ hplainY₁
    hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
  let paid := (Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  have hreserve := local_error_allocation_reserve Z (C.absNorm : ℝ) Bfirst εalloc paid εsrc Mvolume
    saving delta reserve (CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap)
    weights hZ.1 (by positivity) hCcap hεalloc.le hallocSmall hpaid hloss hfrequency hepsSmall hsaving
    (fun j => (hweights j).le)
  let F := Dalloc*mass src^2*(56*1872*(Fintype.card RayCharacter : ℝ))*
    Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight/(seed.absNorm : ℝ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  apply hh.trans
  calc
    _ = F*((C.absNorm : ℝ)^εalloc*∑j,weights j*
        Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)*
        Z^(localErrorExponents paid εsrc Mvolume saving delta reserve j)) := by
      dsimp only [F,weights,paid]
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ F*((∑j,weights j)*Z^(-1/2500 : ℝ)) := mul_le_mul_of_nonneg_left hreserve hF
    _ = Calloc*Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight*mass src^2*
        Z^(-1/2500 : ℝ)/(seed.absNorm : ℝ) := by dsimp only [F,Calloc]; ring
    _ ≤ _ := by gcongr

#print axioms actual_allocated_extracted_errors_uniform
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualAllocatedErrorUniform -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalCount ; sha256 e13ce4ae1a980fcb53648d38472f0a1a34cc89bdb5ec0ccac1ad2ffa44349c3e -/
section



/-! The original-input amplitude saving and the actual second-stage forcing
count. The cumulative extraction ideals occur only in the amplitude bounds. -/
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
open CenteredMomentChildRows
open CenteredMomentFixedQForcingCount CenteredMomentForcing CenteredMomentRankinRadical
open RayFourExpansion UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local instance coherentExceptionalCountDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_coherent_exceptional_counted_values
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi) (lo hi : ι → ℝ)
    (ε δ θ B Lbound : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ)
    (hB : 0 ≤ B) (hL : 0 ≤ Lbound) :
    ∃ J : ℕ, ∃ Sprofile : Finset (ℕ×ℕ), (0,0) ∈ Sprofile ∧
    ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} → ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
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
    idealCoeff η p.val.1 ≠ 0 →
    ∀ m : O, m ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m →
    ∀ rows : Finset O, (∀ z ∈ rows, z ≠ 0) →
    (∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow (childCharacter η χL) Q m
      (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) z) →
    ∀ Cr rowExponent : ℝ, 0 ≤ Cr →
    (∀ z ∈ rows, ((Ideal.span {z}).absNorm : ℝ) ≤ Cr*Z^rowExponent) →
    (∀ z ∈ rows, ((family χL).modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*(C₁*p.val.1).absNorm)*(Ideal.span {z}).absNorm : ℝ) ≤ Z^B) →
    (∀ z ∈ rows, ((reflected (family χR)).modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*(C₁*p.val.2).absNorm)*(Ideal.span {z}).absNorm : ℝ) ≤ Z^B) →
    ∀ Ds : Finset (Ideal O),
    (∀ L ∈ Ds, (moebius L : ℂ) ≠ 0 → (L.absNorm : ℝ) ≤ Z^Lbound) →
    commonSecondValuePair src R seed C₁ L₁ hC₁ p η U χL χR vL vR HL HR Ds rows ≤
      (volume src.toData/Real.sqrt (HL*HR))*
        (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((rowExponent-4*Real.logb Z ((forcingIdeal (fun P : CommonIndex p.val.1 p.val.2 => P.val)
            (leftExponent p.val.1 p.val.2) (rightExponent p.val.1 p.val.2)
            (nonunitPartitionSet p.val.1 p.val.2 U)).absNorm : ℝ))/6+2*ε+δ-max (max (r-Real.logb Z ((C₁*p.val.1).absNorm : ℝ)) 0)
          (max (r-Real.logb Z ((C₁*p.val.2).absNorm : ℝ)) 0))*
          (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)^θ*
          (profileMass Sprofile (withHeight src (family χL) vL).toData
            (withHeight src (reflected (family χR)) vR).toData profile profile J*
              frozenProfile src*frozenProfile src/
                (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm))) := by
  obtain ⟨J,Sprofile,hSprofile,hbound⟩ := actual_coherent_exceptional_values
    wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩ := hbound Q hQ
  let qcost : ℝ := ((commonRadical Q Q).absNorm : ℝ)^(2/3:ℝ)
  have hqcost : 0 < qcost := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero Q Q))
  refine ⟨K*qcost,mul_pos hK hqcost,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro src profile hlo hhi hP hW₁ hW₂ R seed C₁ L₁ hC₁ hR hseed
    p η U family hfamily χL χR vL vR HL HR r hHL hHR hX₁ hX₂ hY₁ hY₂ hη m hm hml hm2
    rows hn hex Cr rowExponent hCr hN hcondL hcondR Ds hDs
  have hexL (z : O) (hz : z ∈ rows) :
      CenteredExceptionalProfile.FixedInducingRow (family χL) Q fixedBadMask 1 z :=
    (hfamily.inducing_iff χL Q m z hm (hn z hz) hml hm2).mp (hex z hz)
  have hexR (z : O) (hz : z ∈ rows) :
      CenteredExceptionalProfile.FixedInducingRow (family χR) Q fixedBadMask 1 (-z) :=
    (hfamily.paired_inducing_iff χL χR Q hQ72 m z hm (hn z hz) hml hm2).mp (hexL z hz)
  have hb := hZ.2 src profile hlo hhi hP hW₁ hW₂ R seed C₁ L₁ hC₁ hR hseed
    p η U family hfamily χL χR vL vR HL HR r hHL hHR hX₁ hX₂ hY₁ hY₂
    rows hn hexL hexR hcondL hcondR Ds hDs
  have hc := actual_canonical_exceptional_count_fixedQ η χL p.val.1 p.val.2
    (lowActiveLeftSupported p) U Q hQ hQtop hQ72 hη m hm hml hm2
    rows hn hex Z Cr rowExponent hZ.1 hCr hN
  let F : ℝ := profileMass Sprofile (withHeight src (family χL) vL).toData
    (withHeight src (reflected (family χR)) vR).toData profile profile J*
      frozenProfile src*frozenProfile src/(((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)
  have hF : 0 ≤ F := div_nonneg
    (mul_nonneg (mul_nonneg (profileMass_nonneg Sprofile _ _ _ _ _) (frozenProfile_nonneg _))
      (frozenProfile_nonneg _)) (by positivity)
  let e : ℝ := 2*ε+δ-max (max (r-Real.logb Z ((C₁*p.val.1).absNorm : ℝ)) 0)
    (max (r-Real.logb Z ((C₁*p.val.2).absNorm : ℝ)) 0)
  let f : ℝ := (rowExponent-4*Real.logb Z ((forcingIdeal
    (fun P : CommonIndex p.val.1 p.val.2 => P.val)
    (leftExponent p.val.1 p.val.2) (rightExponent p.val.1 p.val.2)
    (nonunitPartitionSet p.val.1 p.val.2 U)).absNorm : ℝ))/6
  have hz := zero_lt_one.trans hZ.1
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg (CenteredMomentExceptionalAmplitudePair.volume_pos src.toData).le (Real.sqrt_nonneg _))
  calc
    _ ≤ K*(qcost*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*Z^f))*Z^e*
        (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)^θ*F := by
      apply mul_le_mul_of_nonneg_right _ hF
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left hc hK.le
    _ = _ := by
      change K*(qcost*((768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*Z^f))*Z^e*
        (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)^θ*F =
        (K*qcost)*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        Z^(f+2*ε+δ-max (max (r-Real.logb Z ((C₁*p.val.1).absNorm : ℝ)) 0)
          (max (r-Real.logb Z ((C₁*p.val.2).absNorm : ℝ)) 0))*
        (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)^θ*F
      rw [show f+2*ε+δ-max (max (r-Real.logb Z ((C₁*p.val.1).absNorm : ℝ)) 0)
          (max (r-Real.logb Z ((C₁*p.val.2).absNorm : ℝ)) 0) = f+e by dsimp [e];ring,
        Real.rpow_add hz]
      ring

#print axioms actual_coherent_exceptional_counted_values
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalCount -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstActualCoarse ; sha256 870a18f05f6c1bad3d6681edf28b818732e93ef4acd0fab3c0169dd15db533c6 -/
section


/-! Actual first-source Fourier tails with a fixed polynomial exponent,
including every live common pair, inactive subset, dyadic block,
projector and both ray labels. No cardinality premise remains. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors
local notation "O" => HeckeFamily.O
local instance firstActualCoarseDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem eventually_actual_first_source_coarse_powers
    (N : ℕ) (F U b₁ b₂ B₁ B₂ D B L Cr A J : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hD : 0 ≤ D)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hCr : 0 < Cr) (hJ : 0 ≤ J) :
    ∀ᶠ Z : ℝ in atTop,
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (s : Input ι) (R seed : Ideal O),
    Fintype.card ι ≤ N → (∀ i, s.M i ≤ F) → s.upper ≤ U → s.b₁ ≤ b₁ → s.b₂ ≤ b₂ →
    s.W₁ 0 = 0 → s.W₂ 0 = 0 →
    (∀ x, ‖s.W₁ x‖ ≤ B₁) → (∀ x, ‖s.W₂ x‖ ≤ B₂) →
    0 < sourceRadius s → sourceRadius s ≤ Z^B → volume s.toData ≤ Z^A →
    ∀ (K : ℝ), 0 < K →
    ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
    (∀ p E, radius p E ≤ Cr*Z^L) →
    ∀ (W : FirstSourceOuterIndex s R seed K radius → 𝓢(ℝ,ℂ))
      (H : FirstSourceOuterIndex s R seed K radius → ℝ),
    (∀ i, 0 < H i) → (∀ i, H i ≤ Z^J) →
    (∀ i, QuadraticInitialBound.diagonalControl (W i) ≤ D) →
    ∀ p : Labels s R seed,
    (∑ k ∈ firstSourceLabels Finset.univ (firstSourceOuterLabel s R seed K radius),
      ((firstSourceOuterLabel s R seed K radius k.1).sourceChild k.2).leftCoarse (W k.1) (H k.1)) ≤
      (volume s.toData/(p.val.1.absNorm : ℝ))*
        (((Fintype.card RayCharacter : ℝ)^2*128*D*
          (firstAbsoluteProfileConstant N F U b₁ b₂ B₁ B₂)^2)*Z^(J+6*B+A+2)) ∧
    (∑ k ∈ firstSourceLabels Finset.univ (firstSourceOuterLabel s R seed K radius),
      ((firstSourceOuterLabel s R seed K radius k.1).sourceChild k.2).rightCoarse (W k.1) (H k.1)) ≤
      (volume s.toData/(p.val.2.absNorm : ℝ))*
        (((Fintype.card RayCharacter : ℝ)^2*128*D*
          (firstAbsoluteProfileConstant N F U b₁ b₂ B₁ B₂)^2)*Z^(J+6*B+A+2)) := by
  filter_upwards [eventually_firstSourceOuter_card B L Cr hB hL hCr,
    eventually_ge_atTop (1:ℝ)] with Z hc hZ
  intro ι _ _ s R seed hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hsourcepos hsource hvolume
    K hK radius hr W H hH hHcap hW p
  have hp := commonLabels_supported
    (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
  have hn := commonLabel_norm_bounds (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) (Z^B)
    (fun I _ hI => (original_column_norm s R seed I hz₁ hz₂ hI).2.trans hsource)
    p.val.1 p.val.2 p.property
  have hh := first_source_joint_coarse_powers N F U b₁ b₂ B₁ B₂ D hB₁ hB₂ hD
    s R seed Finset.univ (firstSourceOuterLabel s R seed K radius) (fun _ _ => rfl)
    W H Z A B J (3*B+2) B p.val.1.absNorm p.val.2.absNorm hZ hJ
    (CenteredMomentFirstScale.norm_pos _ hp.1.1) (CenteredMomentFirstScale.norm_pos _ hp.2.1)
    hn.1 hn.2 (by
      simpa only [Finset.card_univ] using hc ι s R seed hz₁ hz₂ hsourcepos hsource K hK radius hr)
    hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ (fun i _ => hH i) (fun i _ => hHcap i)
    (fun i _ => hW i) hsource hvolume
  convert hh using 1 <;> congr 4 <;> ring

#print axioms eventually_actual_first_source_coarse_powers
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstActualCoarse -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighKernelUniform ; sha256 6b2fbc059e72a6824bf2b5ffb621fa52b7b9613ad233e96e68f00d8b8251742a -/
section










/-! The high retained source estimate with every buffered product
constructed internally from its literal source coefficient identities. -/
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

theorem actual_joint_high_kernel_uniform
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
    (Wkernel : 𝓢(ℝ,ℂ)) (decay : ℕ)
    (tailA targetLower plainBound₁ plainBound₂ : ℝ)
    (hplainBound₁ : 0 ≤ plainBound₁) (hplainBound₂ : 0 ≤ plainBound₂)
    (hplainNorm₁ : ∀ x, ‖W₁ x‖ ≤ plainBound₁) (hplainNorm₂ : ∀ x, ‖W₂ x‖ ≤ plainBound₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N Nkernel : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (d P W : ℝ), dmin ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (unit : JointReconstructionLabel → Oˣ) (S : Finset JointReconstructionLabel)
        (w : JointReconstructionLabel → NonzeroElement),
      (∀ v ∈ S, (w v).val = v.row (unit v)) →
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧ primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ (s : JointReconstructionLabel → CommonSecondKernelLabel Slot)
        (Ds : JointReconstructionLabel → Finset (Ideal O))
        (z : JointReconstructionLabel → O) (t K Radius tbase firstU firstTheta : JointReconstructionLabel → ℝ)
        (n : JointReconstructionLabel → Fin 4 → ℤ) (rayWeight : JointReconstructionLabel → ℂ)
        (σ freq : JointReconstructionLabel → Slot → ℝ)
        (θ : JointReconstructionLabel → Slot → RayQuotient.Characters M H)
        (slotWidth : JointReconstructionLabel → Slot → ℝ),
      (∀ v ∈ S, ‖rayWeight v‖ ≤ 1) →
      (∀ v ∈ S, (∀ j, (s v).input.M j ≤ Mslot) ∧ (s v).input.upper ≤ upper ∧
        (s v).input.b₁ ≤ b₁ ∧ (s v).input.b₂ ≤ b₂plain) →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ v ∈ S, (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^(2*B) ∧
        (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, ∀ L ∈ Ds v, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 →
        (L.absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, 0 < dyadicScale (n v 2) ∧ 0 < dyadicScale (n v 3) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ dyadicScale (n v 2) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ dyadicScale (n v 3)) →
      ∀ (first : JointReconstructionLabel → FirstSidePresentation η)
        (hz : ∀ v, z v ≠ 0),
      (∀ v, (s v).parent = (first v).sourceParent) →
      (∀ v, (s v).puncture ≠ 0) →
      (∀ v, w v = (first v).row (s v) (z v) (hz v)) →
      ∀ Bmask : ℝ, W+Bmask+conductorReserve ≤ d →
      (∀ v ∈ S, (((first v).leftPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask ∧
        (((first v).rightPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask) →
      (∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂) →
      (∀ v ∈ S, CenteredMomentAllocatedRayDictionary.Matches M H hH (s v).input
        ηcommon (θ v) (slotWidth v) (σ v) (freq v) Wslot bslot Z) →
      (∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, t v = tbase v+2*Real.pi*(firstU v-firstTheta v)) →
      (∀ v ∈ S, |tbase v| ≤ Z^ν ∧ |firstU v| ≤ Z^ν ∧ |firstTheta v| ≤ Z^ν) →
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
      (∑ v ∈ S, ∑ D ∈ Ds v,
        ‖(((1+SecondKernelLabel.kernelScale (n v))^decay : ℝ) : ℂ) *
          ((UniqueFactorizationMonoid.moebius D : ℂ)*
            ((Z^(A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss) : ℝ) : ℂ)*rayWeight v) *
          ((s v).withProjector D).toKernelLabel.kernelRow (t v) (z v) Wkernel (K v) (Radius v) (n v)‖) ≤
        C*Z^(π+A-c+R₁+E+Bc-144011/109800000) := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_kernel_from_source η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV ηcommon hanchor Wslot hVslot bslot hBslot
      Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B
      hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget hproductLoss hpopulationLoss hB hloss
      τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi fiberLoss hfiberLoss
      conductorReserve hconductorReserve Wkernel decay tailA targetLower plainBound₁ plainBound₂
      hplainBound₁ hplainBound₂ hplainNorm₁ hplainNorm₂
  let Eret := max 1 (2*(max 1 b₁*max 1 b₂plain)*(Mslot^Fintype.card Slot)^4*
    (max 1 upper)^Fintype.card Slot/aSource)
  let Eabs := max 1 (2*128^(Fintype.card Slot+2)*Mslot^Fintype.card Slot*plainBound₁*plainBound₂*
    (max 1 upper)^Fintype.card Slot*max 1 b₁*max 1 b₂plain)
  have hEret : 0 ≤ Eret := by dsimp [Eret]; positivity
  have hEabs : 0 ≤ Eabs := by dsimp [Eabs]; positivity
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C*(Eret+128/aSource*Eabs^2+1),
    hν,hντ,hτdet,hheight,horders,mul_pos hC (by positivity),?_⟩
  filter_upwards [hhigh] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t K Radius tbase firstU firstTheta n rayWeight
    σ freq θ slotWidth hray hprofileCaps hsourceIntervals hsourceNorm hprojectorNorm hphysical
    first hz hfirst hpuncture hwsource Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget
  have hh := hZ.2 d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t K Radius tbase firstU firstTheta n rayWeight
    σ freq θ slotWidth aSource haSource hray hsourceIntervals hsourceNorm hprojectorNorm hphysical
    first hz hfirst hpuncture hwsource Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget
  have hret : retainedProfileEnvelope S s aSource ≤ Eret :=
    retainedProfileEnvelope_le_fixed S s Mslot upper b₁ b₂plain aSource hMslot haSource
      (fun v hv => (hprofileCaps v hv).1) (fun v hv => (hprofileCaps v hv).2.1)
      (fun v hv => (hprofileCaps v hv).2.2.1) (fun v hv => (hprofileCaps v hv).2.2.2)
  have habs : originalAbsoluteEnvelope S s plainBound₁ plainBound₂ ≤ Eabs :=
    originalAbsoluteEnvelope_le_fixed S s Mslot upper b₁ b₂plain plainBound₁ plainBound₂
      hMslot hplainBound₁ hplainBound₂ (fun v hv => (hprofileCaps v hv).1)
      (fun v hv => (hprofileCaps v hv).2.1) (fun v hv => (hprofileCaps v hv).2.2.1)
      (fun v hv => (hprofileCaps v hv).2.2.2)
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  have habs0 := originalAbsoluteEnvelope_nonneg S s plainBound₁ plainBound₂
  apply hh.trans
  gcongr

end FixedData
#print axioms actual_joint_high_kernel_uniform
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighKernelUniform -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowKernel ; sha256 dee0797654f23a34e9ecbacb8f2fa88ebd65f14b3763a8db54097821b43cc732 -/
section


















/-! The actual low-bin source coefficients after both common and divisor
allocations. The source dictionary map returns surviving indices to the
original fixed slot system while preserving the same low-bin indicator. -/
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
local instance lowKernelFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

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
theorem actual_second_low_kernel_of_common_bin
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
      ∀ (Wkernel : 𝓢(ℝ,ℂ)) (decay : ℕ) (ν tailRows tailV lower tailSaving : ℝ), 0 < ν → 0 ≤ tailRows →
      ∃ (Nkernel : ℕ) (Ckernel : ℝ), 0 ≤ Ckernel ∧
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → ∀ hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)},
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
      ∀ (p : Profiles a b) (src : Input α), Matches M H hH src η₀ θ w σ freq W bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      p.profile 0 = src.W₁ → p.profile 1 = src.W₂ →
      (∀ i,src.lo i = loInput i) → (∀ i,src.hi i = hiInput i) →
      src.X₁ ≤ Z^L → src.X₂ ≤ Z^L → src.Y₁ ≤ Z^L → src.Y₂ ≤ Z^L →
      ∀ (C₁ D₁ Rmask seed Lproj Lfirst : Ideal O) (hC₁ : Supported C₁) (hD₁ : D₁ ≠ 0)
        (p₂ : ActiveLabel (commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁)
          (commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst)),
      let C₂ := p₂.val.1
      let D₂ := p₂.val.2
      let hC₂ := lowActiveLeftSupported p₂
      let hD₂ := lowActiveRightSupported p₂
      primeSupport C₂ = primeSupport D₂ →
      ∀ (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂),
      let u := firstSideDictionaryUnit ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
      activeConductor C₁ D₁ = (u : O)*∏ i,activePrimary C₁ D₁ i ∧
      ∀ left : Bool, let parent := firstSideCharacter F left
      ∀ (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
      Family parent C₂ D₂ hC₂ hD₂ U family →
      Rmask ≠ 0 → ∀ hseedfirst : seed ∣ C₁, Squarefree Lproj →
      ((C₁*C₂).absNorm : ℝ) ≤ Z^Bcommon → ((C₁*D₂).absNorm : ℝ) ≤ Z^Bcommon →
      (Lproj.absNorm : ℝ) ≤ Z^Bcommon →
      ∀ (t : ℝ) (columns : Finset (Ideal O)) (β : Ideal O → ℂ) (rows : Finset O)
        (Wrad : 𝓢(ℝ,ℂ)) (Kcut : ℝ) (n : Fin 4 → ℤ)
        (Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip : ℝ),
      0 < Kcut → 0 < Hsource → Real.logb Z Hsource ≤ A+sourceLoss →
      A+(7/2)*(∑ i,w i) ≤ Mparent+g → Real.logb Z (volume src.toData) ≤ A →
      (Fintype.card α : ℝ)*Real.logb Z (max 1 src.upper) ≤ profileLoss →
      0 ≤ g → g ≤ 37/10000 → 0 ≤ omegaLoss → 3/500 ≤ allowance →
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
      0 ≤ pad → nominal+pad ≤ Mcap → nominal+pad+Bmask+ξconductor ≤ d →
      pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 401/9000000 →
      ∀ hne : physicalBlock parent t columns β C₂ D₂ hC₂ hD₂ U radius rows Wrad Kcut n ≠ 0,
      ∀ χL χR : RayCharacter,
      let sL := actualState (τ := family) t columns β radius rows Wrad Kcut n hne Z Bmask hZ
        χL (internalQ Q η₀) 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hmask)
      let sR := actualState (τ := family) t columns β radius rows Wrad Kcut n hne Z Bmask hZ
        (χR⁻¹) (internalQ Q η₀) 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hmask)
      ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      ∀ (holes : O → JointRelativeLabel ηfirst (Option (α × RayQuotient.Characters M H)) → Ideal O)
        (hholes : ∀ z label,holes z label ≠ 0),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : (supportedNaturalState sL).radial.keep z, low z →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (holes z) (hholes z) abin (abin+e) (3*(k+1 : ℕ)*Z^τ)
          (secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left z (sL.row_ne_zero z hz.1))) →
      (∀ z, ∀ hz : (supportedNaturalState sR).radial.keep z, low (-z) →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (holes (-z)) (hholes (-z)) abin (abin+e) (3*(k+1 : ℕ)*Z^τ)
          (secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left (-z) (neg_ne_zero.mpr (sR.row_ne_zero z hz.1)))) →
      (∀ θ u v : ℝ, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → ‖v‖ ≤ Z^ν → ∀ i,
        |(t+2*Real.pi*(u-θ))+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ ∧
        |(t+2*Real.pi*(v-(-θ)))+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ Ω : Finset O,
      (∀ z ∈ Ω,sL.radial.keep z ∧ low z) →
      (∀ z ∈ Ω,sR.radial.keep (-z) ∧ low z) →
      (∀ z ∈ Ω,normValue z ≤ dyadicScale (n 1)) →
      ∀ (vBound B₁ B₂ aSource : ℝ), 0 ≤ vBound → 0 ≤ B₁ → 0 ≤ B₂ → 0 < aSource →
      (∀ θ u v : ℝ, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → ‖v‖ ≤ Z^ν →
        |t+2*Real.pi*(u-θ)| ≤ vBound ∧ |t+2*Real.pi*(v-(-θ))| ≤ vBound) →
      src.W₁ 0 = 0 → src.W₂ 0 = 0 →
      (∀ x, ‖src.W₁ x‖ ≤ B₁) → (∀ x, ‖src.W₂ x‖ ≤ B₂) →
      dyadicScale (n 1) ≤ Z^tailRows → A ≤ tailV →
      aSource*volume src.toData/((C₁*C₂).absNorm : ℝ) ≤ dyadicScale (n 2) →
      aSource*volume src.toData/((C₁*D₂).absNorm : ℝ) ≤ dyadicScale (n 3) →
      let target := δcommon+nominal+allowance-401/9000000
      lower ≤ target →
      let BL := Cbound*((Rmask*(C₁*C₂)).radical.absNorm : ℝ)^εmask*profileCost src*
        diagonalControl sL.radial.profile*(p.control S)^2*(1+vBound+height)^degree /
          (((C₁*C₂).absNorm : ℝ)*Lproj.absNorm)
      let BR := Cbound*((Rmask*(C₁*D₂)).radical.absNorm : ℝ)^εmask*profileCost src*
        diagonalControl sR.radial.profile*(p.control S)^2*(1+vBound+height)^degree /
          (((C₁*D₂).absNorm : ℝ)*Lproj.absNorm)
      let label : CommonSecondKernelLabel α :=
        ⟨src,Rmask,seed,C₁,Lfirst,hC₁,hseedfirst,parent,p₂,U,Lproj,χL,χR⟩
      (∑ z ∈ Ω, ‖(((1+SecondKernelLabel.kernelScale n)^decay : ℝ) : ℂ)*
        label.toKernelLabel.kernelRow t z Wkernel Kcut radius n‖) ≤
        Ckernel*(((volume src.toData/Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
          (Real.sqrt BL*Real.sqrt BR)+(128/aSource)*(originalAbsoluteProfile src B₁ B₂)^2*Z^(-tailSaving))*Z^target) := by
  obtain ⟨degree,S,hmain⟩ := actual_second_low_paired_values_of_common_bin M H hH W
    aslot bslot a b Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon ηfirst parentLoss hparentLoss ξconductor hξconductor
  refine ⟨degree,S,?_⟩
  intro Wkernel decay ν tailRows tailV lower tailSaving hν htailRows
  obtain ⟨Nkernel,Ckernel,hCkernel,hkernel⟩ := actual_second_kernel_of_local_values
    Wkernel decay ν tailRows tailV Bcommon lower tailSaving hν htailRows
  refine ⟨Nkernel,Ckernel,hCkernel,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hmain] with Z hmain
  intro hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ C₁ D₁ Rmask seed Lproj Lfirst hC₁ hD₁ p₂ C₂ D₂ hC₂ hD₂ hCD₂
    E₁ ξ₁ ξ₂ F
  let u := firstSideDictionaryUnit ηfirst C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
  have hbase (vL vR : ℝ) := hmain hZ θ w σ freq vL vR height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ C₁ D₁ Rmask seed Lproj Lfirst hC₁ hD₁ p₂ hCD₂ E₁ ξ₁ ξ₂ F
  refine ⟨(hbase 0 0).1,?_⟩
  intro left parent U family hfamily hR hseed hLproj hCcap hDcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    c d₁ r₁ e₁ radius nominal pad hpad hMcapSource hconductorSource hbudgetSource hne χL χR sL sR low abin k holes hholes
    habin habinTop hbaseScale hT hbinL hbinR hfreqGate hheightSource Ω hkeepL hkeepR hnorm
    vBound B₁ B₂ aSource hvBound hB₁ hB₂ haSource hvCube hz₁ hz₂ hW₁ hW₂ hdyadRows hAtail hphysicalL hphysicalR target htarget BL BR label
  have hvolume0 := (volume_pos src.toData).le
  have hpc := profileCost_nonneg src
  have hdl := diagonalControl_nonneg sL.radial.profile
  have hdr := diagonalControl_nonneg sR.radial.profile
  have hBL : 0 ≤ BL := by dsimp only [BL]; positivity
  have hBR : 0 ≤ BR := by dsimp only [BR]; positivity
  apply hkernel label Ω t Kcut radius n Z target
    ((volume src.toData/Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*(Real.sqrt BL*Real.sqrt BR))
    B₁ B₂ aSource hZ htarget (by positivity) hB₁ hB₂ haSource hz₁ hz₂ hW₁ hW₂
    (fun z hz => (hnorm z hz).trans hdyadRows) (by
      rw [←Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (volume_pos src.toData)]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (hvolume.trans hAtail))
    hCcap hDcap hphysicalL hphysicalR
  intro theta u₁ u₂ htheta hu₁ hu₂
  let vL := t+2*Real.pi*(u₁-theta)
  let vR := t+2*Real.pi*(u₂-(-theta))
  have hh := (hbase vL vR).2 left U family hfamily hR
    (hseed.trans (dvd_mul_right C₁ C₂)) (hseed.trans (dvd_mul_right C₁ D₂)) hLproj hCcap hDcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    hpad hMcapSource hconductorSource hbudgetSource hne χL (χR⁻¹) low abin k holes hholes
    habin habinTop hbaseScale hT hbinL hbinR
    (fun i => (hfreqGate theta u₁ u₂ htheta hu₁ hu₂ i).1)
    (fun i => (hfreqGate theta u₁ u₂ htheta hu₁ hu₂ i).2) hheightSource
    (dyadicScale (n 2)) (dyadicScale (n 3)) (dyadicScale_pos _) (dyadicScale_pos _) Ω hkeepL hkeepR hnorm
  have hvl := (hvCube theta u₁ u₂ htheta hu₁ hu₂).1
  have hvr := (hvCube theta u₁ u₂ htheta hu₁ hu₂).2
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hexp : δcommon+(nominal+allowance-401/9000000) = target := by dsimp [target]; ring
  have hleft : Cbound*((Rmask*(C₁*C₂)).radical.absNorm : ℝ)^εmask*profileCost src*
      diagonalControl sL.radial.profile*(p.control S)^2*(1+|vL|+height)^degree *
        Z^(δcommon+(nominal+allowance-401/9000000))/(((C₁*C₂).absNorm : ℝ)*Lproj.absNorm) ≤ BL*Z^target := by
    rw [hexp]
    dsimp only [BL]
    rw [div_mul_eq_mul_div]
    gcongr
  have hright : Cbound*((Rmask*(C₁*D₂)).radical.absNorm : ℝ)^εmask*profileCost src*
      diagonalControl sR.radial.profile*(p.control S)^2*(1+|vR|+height)^degree *
        Z^(δcommon+(nominal+allowance-401/9000000))/(((C₁*D₂).absNorm : ℝ)*Lproj.absNorm) ≤ BR*Z^target := by
    rw [hexp]
    dsimp only [BR]
    rw [div_mul_eq_mul_div]
    gcongr
  have hfactor : Real.sqrt (BL*Z^target)*Real.sqrt (BR*Z^target) =
      (Real.sqrt BL*Real.sqrt BR)*Z^target := by
    rw [Real.sqrt_mul hBL,Real.sqrt_mul hBR]
    calc
      _ = (Real.sqrt BL*Real.sqrt BR)*(Real.sqrt (Z^target)*Real.sqrt (Z^target)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (Real.rpow_nonneg hZpos.le _)]
  have hbound := hh.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (div_nonneg (volume_pos src.toData).le (Real.sqrt_nonneg _)))
  rw [hfactor] at hbound
  have heqL (z : O) : label.toKernelLabel.leftValue vL z (dyadicScale (n 2)) =
      secondChildValue parent vL (commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁)
        (commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst)
        C₂ hC₂ (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U) Lproj χL z (dyadicScale (n 2)) := by
    exact secondChildValue_active _ _ _ _ _ _ _ _ _ _ _
  have heqR (z : O) : label.toKernelLabel.rightValue vR z (dyadicScale (n 3)) =
      secondChildValue parent vR (commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁)
        (commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst)
        D₂ hD₂ (commonFrequencyGenerator C₂ D₂*nonunitFrequencyGenerator C₂ D₂ U) Lproj (χR⁻¹) (-z) (dyadicScale (n 3)) := by
    exact secondChildValue_active _ _ _ _ _ _ _ _ _ _ _
  change (∑ z ∈ Ω, ‖label.toKernelLabel.leftValue vL z (dyadicScale (n 2))‖ *
    ‖label.toKernelLabel.rightValue vR z (dyadicScale (n 3))‖) ≤ _
  simp only [heqL,heqR]
  simpa only [mul_assoc] using hbound

#print axioms actual_second_low_kernel_of_common_bin
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowKernel -/
