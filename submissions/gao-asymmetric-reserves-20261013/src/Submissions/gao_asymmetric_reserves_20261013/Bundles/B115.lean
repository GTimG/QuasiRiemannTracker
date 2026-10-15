/-
Reserve-balanced affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 and Kari Roegnvaldsson affine-local-20261013 at c707738.
Retains the amplifier and final savings while reallocating intermediate reserves.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below.
Affine-capacity adaptation: the source module hashes below identify the
pre-adaptation provenance, not the modified declarations in this file. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B100
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B104
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B108
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B109
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B110
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B111
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B113
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B114

/- BEGIN ORIGINAL MODULE Analytic.JointHighPacketDataBound ; sha256 fdb436501c110746c7fed0c7be99f47d945faee97aaf60abf5a58b795d8da315 -/
section





/-! The genuine high-source estimate summed over both actual dyadic block
families. Maximization pays their subpower mass without recounting arithmetic rows. -/
set_option autoImplicit false
set_option maxRecDepth 8192
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
open NonzeroJointSourceRow CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentActive CenteredMomentCompleteCommon
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSourceRow CenteredMomentSecondLiveBlock
open CanonicalRowCompletion CenteredMomentRankinRadical ActualEisensteinCubic
open ActualFirstSecondSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstPhysicalDyadicAssembly
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

theorem actual_high_packet_data_bound
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
    (hdyadicLoss : 0 < dyadicLoss)
    (rowAbsorb : ℝ) (hrowAbsorb : 0 < rowAbsorb)
    (haSource_eq : aSource = (∏ j, lo j)*a₁*a₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N Nkernel : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ value exponent : ℝ, HighPacketSourceData η η₀ Q hQ72 M H hH hQM hQη₀ ηcommon Wslot bslot Rwidth dmax e σmin σmax loss B dmin heightLoss I W₁ W₂ b₁ b₂plain lo hi fiberLoss Mslot upper conductorReserve Sbad Wkernel tailA targetLower Bdyad₁ Ldyad₁ Crdyad₁ Bdyad₂ Ldyad₂ Crdyad₂ dyadicLoss rowAbsorb Z τ ν value exponent → value ≤ C*Z^exponent := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_packet_geometry η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV ηcommon hanchor Wslot hVslot bslot hBslot
      Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B
      hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget hproductLoss hpopulationLoss hB hloss
      τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi fiberLoss hfiberLoss
      aSource Mslot upper haSource hMslot conductorReserve hconductorReserve
      Sbad primeLoss hprimeLoss hprimeReserve Wkernel tailA targetLower plainBound₁ plainBound₂
      hplainBound₁ hplainBound₂ hplainNorm₁ hplainNorm₂
      Bdyad₁ Ldyad₁ Crdyad₁ Bdyad₂ Ldyad₂ Crdyad₂ dyadicLoss
      hBdyad₁ hLdyad₁ hCrdyad₁ hBdyad₂ hLdyad₂ hCrdyad₂ hdyadicLoss
      rowAbsorb hrowAbsorb haSource_eq
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,?_⟩
  filter_upwards [hhigh] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro value exponent hdata
  delta HighPacketSourceData at hdata
  refine Exists.elim hdata (fun d hdata => ?_)
  refine Exists.elim hdata (fun P hdata => ?_)
  refine Exists.elim hdata (fun W hdata => ?_)
  refine Exists.elim hdata (fun p hdata => ?_)
  refine Exists.elim hdata (fun i hdata => ?_)
  refine Exists.elim hdata (fun input hdata => ?_)
  refine Exists.elim hdata (fun puncture hdata => ?_)
  refine Exists.elim hdata (fun seed hdata => ?_)
  refine Exists.elim hdata (fun hpuncture hdata => ?_)
  refine Exists.elim hdata (fun hseed hdata => ?_)
  refine Exists.elim hdata (fun hz₁ hdata => ?_)
  refine Exists.elim hdata (fun hz₂ hdata => ?_)
  refine Exists.elim hdata (fun hinputη hdata => ?_)
  refine Exists.elim hdata (fun side hdata => ?_)
  refine Exists.elim hdata (fun ξ₁ hdata => ?_)
  refine Exists.elim hdata (fun ξ₂ hdata => ?_)
  refine Exists.elim hdata (fun fallback hdata => ?_)
  refine Exists.elim hdata (fun K₁ hdata => ?_)
  refine Exists.elim hdata (fun radius hdata => ?_)
  refine Exists.elim hdata (fun fallbackFirst hdata => ?_)
  refine Exists.elim hdata (fun K hdata => ?_)
  refine Exists.elim hdata (fun Radius hdata => ?_)
  refine Exists.elim hdata (fun Height hdata => ?_)
  refine Exists.elim hdata (fun X hdata => ?_)
  refine Exists.elim hdata (fun hzero hdata => ?_)
  refine Exists.elim hdata (fun R hdata => ?_)
  refine Exists.elim hdata (fun hR hdata => ?_)
  refine Exists.elim hdata (fun height hdata => ?_)
  refine Exists.elim hdata (fun tbase hdata => ?_)
  refine Exists.elim hdata (fun firstU hdata => ?_)
  refine Exists.elim hdata (fun firstTheta hdata => ?_)
  refine Exists.elim hdata (fun σ hdata => ?_)
  refine Exists.elim hdata (fun freq hdata => ?_)
  refine Exists.elim hdata (fun θ hdata => ?_)
  refine Exists.elim hdata (fun slotWidth hdata => ?_)
  refine Exists.elim hdata (fun Bmask hdata => ?_)
  refine Exists.elim hdata (fun A hdata => ?_)
  refine Exists.elim hdata (fun c hdata => ?_)
  refine Exists.elim hdata (fun d₁ hdata => ?_)
  refine Exists.elim hdata (fun π hdata => ?_)
  refine Exists.elim hdata (fun R₁ hdata => ?_)
  refine Exists.elim hdata (fun R₀ hdata => ?_)
  refine Exists.elim hdata (fun E hdata => ?_)
  refine Exists.elim hdata (fun Bc hdata => ?_)
  refine Exists.elim hdata (fun L hdata => ?_)
  refine Exists.elim hdata (fun b₂ hdata => ?_)
  refine Exists.elim hdata (fun g₂ hdata => ?_)
  refine Exists.elim hdata (fun t₂cost hdata => ?_)
  refine Exists.elim hdata (fun omegaLoss hdata => ?_)
  refine Exists.elim hdata (fun geometryLoss hdata => ?_)
  refine Exists.elim hdata (fun lengthLoss hdata => ?_)
  refine Exists.elim hdata (fun missingLoss hdata => ?_)
  refine Exists.elim hdata (fun c₂ hdata => ?_)
  refine Exists.elim hdata (fun d₂ hdata => ?_)
  refine Exists.elim hdata (fun supportLoss hdata => ?_)
  refine Exists.elim hdata (fun clipLoss hdata => ?_)
  refine Exists.elim hdata (fun commonLoss hdata => ?_)
  refine Exists.elim hdata (fun scalarLoss hdata => ?_)
  refine Exists.elim hdata (fun rowc hdata => ?_)
  refine Exists.elim hdata (fun rowd hdata => ?_)
  refine Exists.elim hdata (fun rowR hdata => ?_)
  refine Exists.elim hdata (fun rowe hdata => ?_)
  refine Exists.elim hdata (fun rowomega hdata => ?_)
  refine Exists.elim hdata (fun rowL hdata => ?_)
  refine Exists.elim hdata (fun sourceLoss hdata => ?_)
  refine Exists.elim hdata (fun subsetLoss hdata => ?_)
  refine Exists.elim hdata (fun ξ hdata => ?_)
  refine Exists.elim hdata (fun pMissing hdata => ?_)
  refine Exists.elim hdata (fun rMissing hdata => ?_)
  refine Exists.elim hdata (fun eMissing hdata => ?_)
  refine Exists.elim hdata (fun cancelMissing hdata => ?_)
  refine Exists.elim hdata (fun volumeLoss hdata => ?_)
  rcases hdata with ⟨hgates,hvalue,hexponent⟩
  rcases hgates with ⟨check_hd,check_hdmax',check_hbase,check_hT,check_hPB,check_hWB,check_hp,check_hi,check_hheightBin,check_hbin,check_hsourceRadius,check_hfirstDyadic,check_hsecondDyadic,check_hprofileCaps,check_hsourceIntervals,check_hphysicalX,check_hconductorBalance,check_hmaskNorm,check_hplain,check_hmatch,check_hscale,check_hprimeScale,check_hteq,check_hinputfreq,check_hσrange,check_hslotfreq,check_hb₂,check_hlengthLossSplit,check_hvolume,check_hcommonDyads,check_hsupport,check_hclip,check_hδ,check_hδtop,check_hAtop,check_hp₀,check_hpc,check_hpd,check_hRp,check_hR₀,check_hE,check_hBc,check_hL,check_hb₂₀,check_hg₂,check_ht₂,check_hgeometryLoss,check_hlengthLoss,check_hW,check_hP,check_htotal,check_htailA,check_htarget,check_hKactual,check_hcost,check_hsourceRow,check_hrowBudget,check_hmissingBudget,check_hfirstGeometry,check_hrowSupport,check_hVolumeLower⟩
  subst value; subst exponent
  exact hZ.2 d P W check_hd check_hdmax' check_hbase check_hT check_hPB check_hWB p
    check_hp i check_hi check_hheightBin input puncture seed hpuncture hseed hz₁
    hz₂ hinputη side ξ₁ ξ₂ fallback K₁ radius fallbackFirst K
    Radius Height X hzero R hR check_hbin check_hsourceRadius check_hfirstDyadic check_hsecondDyadic
    height tbase firstU firstTheta σ freq θ slotWidth check_hprofileCaps check_hsourceIntervals
    check_hphysicalX Bmask check_hconductorBalance check_hmaskNorm check_hplain check_hmatch check_hscale check_hprimeScale check_hteq check_hinputfreq
    check_hσrange check_hslotfreq A c d₁ π R₁ R₀ E Bc
    L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂
    check_hb₂ supportLoss clipLoss commonLoss check_hlengthLossSplit check_hvolume check_hcommonDyads check_hsupport check_hclip check_hδ
    check_hδtop check_hAtop check_hp₀ check_hpc check_hpd check_hRp check_hR₀ check_hE check_hBc check_hL
    check_hb₂₀ check_hg₂ check_ht₂ check_hgeometryLoss check_hlengthLoss check_hW check_hP check_htotal check_htailA check_htarget
    scalarLoss check_hKactual check_hcost rowc rowd rowR rowe rowomega rowL sourceLoss
    subsetLoss ξ pMissing rMissing eMissing cancelMissing check_hsourceRow check_hrowBudget check_hmissingBudget check_hfirstGeometry
    check_hrowSupport volumeLoss check_hVolumeLower

end FixedData
#print axioms actual_high_packet_data_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighPacketDataBound -/

/- BEGIN ORIGINAL MODULE Analytic.JointLiteralJoinGates ; sha256 04a90ee9029536401868ea5332228db1e8ac85325946148583902e5887d74fdd -/
section




/-! Exact common choices for joining the coherent literal terms to the
first annular amplifier. In particular, its prime average and enlarged
ball agree literally, and the first Fourier cube uses a smaller exponent. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstAmplificationChoice CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentFirstScale CenteredMomentFirstMixedRightTransport
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSecondRetainedRows HeckeDetectorDyadicGeometry
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One positive choice works simultaneously for the amplifier reserve,
first physical cutoff, and second cutoff in all four literal terms. -/
lemma literal_join_small_choices :
    0 < lowLocalTiny/4 ∧ 0 < lowLocalTiny/4 ∧
    lowLocalTiny/4+lowLocalTiny/4 ≤ lowLocalTiny ∧
    lowLocalTiny/4 ≤ lowLocalTiny := by norm_num [lowLocalTiny]

/-- The first Fourier cutoff must be strictly below every endpoint's
allowed height exponent. Both first signs are covered by one event. -/
theorem eventually_first_literal_shifted_heights (ν η : ℝ) (hgap : ν < η) :
    ∀ᶠ Z : ℝ in atTop, ∀ t u θ : ℝ,
      |t| ≤ Z^ν → |u| ≤ Z^ν → |θ| ≤ Z^ν →
      |t+2*Real.pi*(u-θ)| ≤ Z^η ∧ |t+2*Real.pi*(u-(-θ))| ≤ Z^η := by
  have hh := uniform_power_allowance (1+4*Real.pi) ν η 1 zero_le_one (by simpa using hgap)
  filter_upwards [hh] with Z hZ
  intro t u θ ht hu hθ
  have hp : (1+4*Real.pi)*Z^ν ≤ Z^η := by simpa using hZ η le_rfl
  exact ⟨(low_shifted_plain_height t u θ (Z^ν) ht hu hθ).trans hp,
    (low_shifted_plain_height t u (-θ) (Z^ν) ht hu (by simpa only [abs_neg] using hθ)).trans hp⟩

lemma actual_amplifier_prime_card (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (Sbad : Finset (Ideal O)) (Z : ℝ) :
    ((CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^((9/500:ℝ)/3))).card : ℝ) =
      actualHighPrimeCount M H Sbad Z := by
  norm_num [actualHighPrimeCount]

lemma FirstJointLabel.sideMainRadius_literal (q : FirstJointLabel ι) (left : Bool)
    (src : Input ι) (Z upper b₁ b₂ ξ reserve : ℝ) (hZ : 1 < Z) :
    q.sideMainRadius left Z Z (volume src.toData) (9/500)
      (frequencyLoss Z (32*(lowLiteralSupportConstant (Fintype.card ι) upper b₁ b₂)^2) ξ) reserve =
      firstLowMainScale q left Z (Real.logb Z (volume src.toData)) 1
        (lowLiteralOmega (Fintype.card ι) upper b₁ b₂ ξ reserve Z) := by
  have hh := q.sideMainRadius_eq_firstLowMainScale_of_volume left Z
    (Real.logb Z (volume src.toData)) 1 (volume src.toData)
    (frequencyLoss Z (32*(lowLiteralSupportConstant (Fintype.card ι) upper b₁ b₂)^2) ξ) reserve hZ
    (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (volume_pos src.toData)).symm
  simpa only [Real.rpow_one,lowLiteralOmega] using hh

/-- Moving the fixed source support factor into the amplifier's fixed
constant is valid on both sides, with the original first pair retained. -/
lemma FirstJointLabel.side_nominal_source_factor (q : FirstJointLabel ι) (left : Bool)
    (K X V C : ℝ) (hK : 0 < K) (hX : 0 ≤ X) (hXV : X ≤ C*V) :
    firstNominalScale q.C q.D (Ideal.span {q.puncture}) K X ≤
      C^2*firstNominalScale (q.sideCommon left) (q.sideCommon (!left))
        (Ideal.span {q.puncture}) K V := by
  have hh := q.nominal_scale_mono_source K X (C*V) hK hX hXV
  have heq : firstNominalScale q.C q.D (Ideal.span {q.puncture}) K (C*V) =
      C^2*firstNominalScale q.C q.D (Ideal.span {q.puncture}) K V := by
    unfold firstNominalScale
    ring
  rw [heq] at hh
  cases left
  · simpa only [FirstJointLabel.sideCommon,Bool.not_false,Bool.false_eq_true,if_false,if_true,nominal_swap] using hh
  · exact hh

/-- The true retained first dyad satisfies the amplifier's row-scale cap;
its exponent is fixed independently of the labels. -/
lemma actual_first_annular_amplifier_scale (src : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 1 ≤ K) (hZ : 32 ≤ Z) (hξ : ξ ≤ 1)
    (hsource₀ : 0 ≤ sourceRadius src) (hsource : sourceRadius src ≤ Z^(1:ℝ))
    (i : FirstSourceOuterIndex src R seed K (actualLowFirstRadius src R seed K Z ξ)) :
    0 < dyadicScale (i.2.2 1) ∧
    dyadicScale (i.2.2 1) ≤ 4*actualLowFirstRadius src R seed K Z ξ i.1 i.2.1.val ∧
    8*dyadicScale (i.2.2 1) ≤ Z^(4:ℝ) := by
  have hZ₁ : 1 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hh := first_dyadic_annular_radius _ _ _ _ i.2.2
  have hr := actualLowFirstRadius_le src R seed K Z ξ hK hZ₁ hξ hsource₀ hsource i.1 i.2.1.val
  refine ⟨hh.1,hh.2,?_⟩
  calc
    _ ≤ 32*actualLowFirstRadius src R seed K Z ξ i.1 i.2.1.val := by linarith only [hh.2]
    _ ≤ 32*Z^(3:ℝ) := by simpa only [one_mul] using mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 32)
    _ ≤ Z*Z^(3:ℝ) := mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg (by linarith) _)
    _ = Z^(4:ℝ) := by
      rw [show (4:ℝ)=1+3 by norm_num,Real.rpow_add (zero_lt_one.trans hZ₁),Real.rpow_one]

#print axioms eventually_first_literal_shifted_heights
#print axioms FirstJointLabel.sideMainRadius_literal
#print axioms FirstJointLabel.side_nominal_source_factor
#print axioms actual_first_annular_amplifier_scale
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLiteralJoinGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointLocalErrorTarget ; sha256 54188619e753b9672aef9cf3778032878e933af95903428c8d0ae37663645dbb -/
section




/-! The selected coherent amplifier errors on the literal local source. -/
set_option autoImplicit false
set_option maxHeartbeats 4800000
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
local instance localErrorTargetDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance localErrorTargetFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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


def firstCoherentErrorTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed : Ideal O) (Z : ℝ)
    (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (k : (i : FirstSourceOuterIndex src R seed Z radius) ×
      (firstSourceOuterLabel src R seed Z radius i).SourceIndex)
    (left : Bool) (upper delta reserve t : ℝ) (P : Finset (Ideal O))
    (τ : (J : Finset ι) → Character → elementPool P → Fin 3 → RayCharacter → Character) : ℝ :=
  let q := firstSourceOuterLabel src R seed Z radius k.1
  let v := q.sourceChild k.2
  allocatedExtractedErrors (Fintype.card ι) src (q.sideCommon left) R k.2.1.val
    (v.sideParent left) t upper Z (q.sideWidth (!left) Z)
    (nominalLog (q.sideCommon left) (q.sideCommon (!left)) (Ideal.span {q.puncture}) Z (volume src) Z)
    (q.sideWidth left Z) (9/500) delta reserve P
    (fun B => τ (CenteredMomentCommonProfile.liveIndices B.val) (v.sideParent left))

theorem actual_literal_first_extracted_error_target
    (Wslot : ℝ → ℂ) (aslot bslot a b σlo σhi Mslot lower upper bplain₁ bplain₂ BRmask : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b)
    (hMslot : 0 ≤ Mslot) (hlower : 0 < lower) (hupper : 1 ≤ upper) (hBRmask : 0 ≤ BRmask)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (lows highs : α → ℝ) (hhighs : ∀ i,0 ≤ highs i)
    (ηfirst : Character) (profile : Profiles a b) (Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes ⊆ Sbad) (τheight ξamp reserve : ℝ)
    (hτheight : 0 < τheight) (hξamp : 0 < ξamp) (hreserve : 0 ≤ reserve)
    (hamp : ξamp+reserve ≤ lowLocalTiny) :
    ∃ ν : ℝ, 0 < ν ∧ ν < τheight ∧
    ∀ (η₀ : Character) (Q : Ideal O), Q ≤ M → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72:O)} →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    let P := primePool M H Sbad (1/2) 1 (Z^((9/500:ℝ)/3))
    ∀ (τ : (J : Finset α) → Character → elementPool P → Fin 3 → RayCharacter → Character),
      (∀ J η (p : elementPool P) i χ, ((τ J η p i χ).modulus.absNorm : ℝ) ≤
        CenteredMomentAmplificationRadicalFamily.radicalBound (CenteredMomentChildRows.childCharacter η χ)
          fixedBadMask p.val (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))) →
    ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ lowLocalMesh) →
      (∀ i,σlo ≤ σ i) → (∀ i,σ i ≤ σhi) →
      0 ≤ height → height ≤ Z^ν → (∀ i,|freq i| ≤ height) →
    ∀ (src : Input α), Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      (∀ i,src.lo i = lows i) → (∀ i,src.hi i = highs i) →
      lower ≤ src.lower → src.upper ≤ upper →
      (∀ i,|src.hi i| ≤ upper) → |src.b₁| ≤ bplain₁ → |src.b₂| ≤ bplain₂ →
      0 ≤ src.b₁ → 0 ≤ src.b₂ → src.b₁ ≤ max 1 b → src.b₂ ≤ max 1 b →
      profile.profile 0 = src.W₁ → profile.profile 1 = src.W₂ → src.η = ηfirst →
      0 < sourceRadius src →
      Real.logb Z src.X₁ ≤ 423/1000 → Real.logb Z src.X₂ ≤ 423/1000 →
      Real.logb Z src.Y₁ ≤ 1 → Real.logb Z src.Y₂ ≤ 1 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z src.X₁) (Real.logb Z src.X₂) (∑ i,w i) →
      Z^(1/4:ℝ) ≤ src.X₁ → Z^(1/4:ℝ) ≤ src.X₂ →
      Z^(1/4:ℝ) ≤ src.Y₁ → Z^(1/4:ℝ) ≤ src.Y₂ →
    ∀ (R seed : Ideal O), R ≠ 0 → (R.absNorm : ℝ) ≤ Z^BRmask → Squarefree seed → seed ≠ 0 →
    let radius := actualLowFirstRadius src R seed Z Z ξamp
    let q := firstSourceOuterLabel src R seed Z radius
    let delta := frequencyLoss Z (32*(lowLiteralSupportConstant (Fintype.card α) upper bplain₁ bplain₂)^2) ξamp
    ∀ (labels : Finset (FirstSourceOuterIndex src R seed Z radius)) (ref : FirstJointLabel α),
      ref.parent = ηfirst →
      (∀ i ∈ labels,(q i).radicalWidth Z ≤ ref.radicalWidth Z+lowLocalTiny) →
      (∀ i ∈ labels,(q i).activeWidth Z+(q i).punctureWidth Z+(q i).leftAllowance Z-2*(q i).leftWidth Z ≤
        ref.activeWidth Z+ref.punctureWidth Z+ref.leftAllowance Z-2*ref.leftWidth Z+lowLocalTiny) →
      (∀ i ∈ labels,(q i).activeWidth Z+(q i).punctureWidth Z+(q i).rightAllowance Z-2*(q i).rightWidth Z ≤
        ref.activeWidth Z+ref.punctureWidth Z+ref.rightAllowance Z-2*ref.rightWidth Z+lowLocalTiny) →
    ∀ (t : ((i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex) → ℝ),
      (∀ k ∈ firstSourceLabels labels q,|t k| ≤ Z^ν) →
    ∀ left : Bool,
      (∑ k ∈ firstSideSourceLabels labels q (fun _ => sourceRadius src) left,
        firstCoherentErrorTerm src R seed Z radius k left upper delta reserve (t k) P τ) ≤
      (C/(seed.absNorm : ℝ))*(1/((ref.sideCommon left).absNorm : ℝ))*
        Z^(ref.sideTargetWidth left Z (Real.logb Z (volume src))-1/10000) := by
  obtain ⟨hε,hmask,hεsmall,hloss,hbudget,hpaid⟩ := error_local_parameters BRmask hBRmask
  have htiny : 0 < lowLocalTiny := by norm_num [lowLocalTiny]
  have hmesh0 : 0 ≤ lowLocalMesh := (low_local_parameter_choices (Fintype.card α)).1.le
  have hmesh : lowLocalMesh ≤ Cycle25.Energy.commonMesh 2 0 1 (lowLocalTiny/4) := min_le_left _ _
  have hmeshcap : lowLocalMesh ≤ lowLocalTiny/4 := min_le_right _ _
  let aSource := CenteredMomentSecondInputCapacitySource.lowerFactor (Fintype.card α) lower a
  have haSource : 0 < aSource := CenteredMomentSecondInputCapacitySource.lowerFactor_pos _ _ _ hlower ha
  let cost := max 1 CenteredMomentFirstSourceConductorCaps.rayCost
  obtain ⟨U,J,hmain⟩ := actual_first_independent_raw_errors_full M H hH Wslot aslot bslot 2
    (lowLocalTiny/4) σlo σhi (lowLocalTiny/4) a b Mslot (errorLocalMask BRmask)
    hMslot hmask ha haUpper hb 1 (by norm_num) haslot hWs hW hbslot (by norm_num)
    (by positivity) (by positivity) hbeta hbetaTop (Fintype.card α) lower upper aSource (lowLocalTiny/4)
    hlower hupper haSource (by positivity) lows highs hhighs
    (errorLocalEps BRmask) (errorLocalEps BRmask) (errorLocalEps BRmask) (BRmask+8) 1 (lowLocalTiny/4) 0
    hε hε hε (by linarith) (by positivity) Sbad hbad (9/500) cost (by norm_num)
    (by norm_num [lowLocalTiny]) (le_max_left _ _) rfl
    1 3 BRmask 4 1 (by norm_num) (hbudget _ (by linarith))
    (1/100000) (by norm_num) hloss le_rfl 1 3 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 1 (1/10) (by norm_num) (le_max_right _ _) (by norm_num)
    (1/100000) (by norm_num) le_rfl
  let ν := min (τheight/2) (1/(100000*((J:ℝ)+1)))
  have hν : 0 < ν := lt_min (by positivity) (by positivity)
  have hντ : ν < τheight := (min_le_left _ _).trans_lt (by linarith)
  have hνJ : ν*(J:ℝ) ≤ 1/100000 := by
    have hh := (le_div_iff₀ (show (0:ℝ) < 100000*((J:ℝ)+1) by positivity)).mp
      (min_le_right (τheight/2) (1/(100000*((J:ℝ)+1))))
    nlinarith
  refine ⟨ν,hν,hντ,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  let parentCost := (ηfirst.modulus.absNorm : ℝ)*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm
  let C := parentCost*(Cbound*profile.control U^2*(3:ℝ)^J*(Mslot^Fintype.card α)^2)
  have hC : 0 ≤ C := by dsimp only [C,parentCost]; positivity
  refine ⟨C+1,by positivity,?_⟩
  have hηpos := CenteredMomentFirstScale.norm_pos ηfirst.modulus ηfirst.modulus_ne_bot
  have hsep : lowLocalMesh < (9/500:ℝ)/6 := by
    norm_num [lowLocalTiny] at hmeshcap ⊢
    linarith
  have hsupport : 1 ≤ lowLiteralSupportConstant (Fintype.card α) upper bplain₁ bplain₂ := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  filter_upwards [hmain,eventually_actual_high_prime_ratio M H hH Sbad 1 (by norm_num),
    eventually_actual_amplifier_error_source_admissible (ι := α) M H hH Sbad hbad (9/500) upper lowLocalMesh
      (by norm_num) (zero_le_one.trans hupper) hsep,
    eventually_low_fixed_profile_gates (ι := α) upper bplain₁ bplain₂ b lowLocalTiny htiny,
    eventually_low_literal_omega (Fintype.card α) upper bplain₁ bplain₂ ξamp reserve hξamp hreserve hamp,
    eventually_fixed_logb_le (ηfirst.modulus.absNorm : ℝ) lowLocalTiny hηpos htiny,
    eventually_fixed_logb_le fixedPresentationCost (1/1000) fixedPresentationCost_pos (by norm_num)]
      with Z hmain hprime hadmit hfixed homega hηlog hfixedlog
  intro hZ P τ hτ θ w σ freq height hw hwmesh hσlo hσhi hheight hheightcap hfreq src hmatch hhi hMs hloSrc hhiSrc
    hlowerSrc hupperSrc hhiAbs hb₁ hb₂ hb10 hb20 hb1max hb2max hp₁ hp₂ hη hsource₀
    hn₁ hn₂ hm₁ hm₂ hwSum hcap hX₁ hX₂ hY₁ hY₂ R seed hR hRN hs hs0 radius q delta
    labels ref hrefParent hrad hleftWidth hrightWidth t ht
  have hz := zero_lt_one.trans hZ
  have hv : 0 < volume src := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  let A := Real.logb Z (volume src)
  have hvol : volume src = Z^A := (Real.rpow_logb hz hZ.ne' hv).symm
  have hAeq := original_volume_log src Z w hZ hmatch.scale
  have hA := (local_capacity_of_volume Z (Real.logb Z src.X₁) (Real.logb Z src.X₂) (∑ i,w i) A
    hAeq hn₁ hn₂ hwSum hcap).1
  have hvolCap : volume src ≤ Z^(1:ℝ) := by rw [hvol];exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hsourceLog := (hfixed.2.1 src hsource₀ hhiAbs hb₁ hb₂ hupperSrc).1
  have hsource : sourceRadius src ≤ Z^(1:ℝ) := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) := (Real.rpow_logb hz hZ.ne' hsource₀).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num [lowLocalTiny] at hsourceLog ⊢; linarith)
  have hzero₁ : src.W₁ 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt ha) (profile.support 0 (by simpa only [hp₁,Function.mem_support] using hh)).1
  have hzero₂ : src.W₂ 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt ha) (profile.support 1 (by simpa only [hp₂,Function.mem_support] using hh)).1
  have hηone : (1:ℝ) ≤ src.η.modulus.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
  have hηnonneg := Real.logb_nonneg hZ hηone
  have hηsmall : Real.logb Z (src.η.modulus.absNorm : ℝ) ≤ lowLocalTiny := by simpa only [hη] using hηlog.2
  have hηcap : (src.η.modulus.absNorm : ℝ) ≤ Z^(1:ℝ) := by
    rw [hη]
    calc
      _ = Z^(Real.logb Z (ηfirst.modulus.absNorm : ℝ)) := (Real.rpow_logb hz hZ.ne' hηpos).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (hηlog.2.trans (by norm_num [lowLocalTiny]))
  have homega : delta+reserve ≤ lowLocalTiny := homega.2.2
  have hdelta : 0 ≤ delta := by
    apply frequencyLoss_nonneg Z _ ξamp hZ (by nlinarith) hξamp.le
  have hxi : ξamp ≤ 1 := by norm_num [lowLocalTiny] at hamp;linarith
  have hradius := actualLowFirstRadius_le src R seed Z Z ξamp hZ.le hZ hxi hsource₀.le hsource
  have hP : P.Nonempty := by
    apply Finset.card_pos.mp
    have hh := hprime.2.1
    have hp : (0:ℝ) < (P.card : ℝ) := by
      simpa only [P,actualHighPrimeCount,show (9/500:ℝ)/3=3/500 by norm_num] using hh
    exact_mod_cast hp
  let Mdecl := max (Real.logb Z src.X₁+Real.logb Z src.X₂+(9/2)*(∑ i,w i))
    (1+Real.logb Z (src.η.modulus.absNorm : ℝ))
  have hdecl := error_local_declared_capacity (Real.logb Z src.X₁) (Real.logb Z src.X₂) (∑ i,w i)
    (Real.logb Z (src.η.modulus.absNorm : ℝ)) hwSum hcap hηnonneg
  have hXone : 1 ≤ src.X₁ := (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ) ≤ 1/4)).trans hX₁
  have hXtwo : 1 ≤ src.X₂ := (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ) ≤ 1/4)).trans hX₂
  have hcapacity : length Z src.X₁+length Z src.X₂+6*(3/4)*(∑ i,w i) ≤ Mdecl := by
    simpa only [length,max_eq_right hXone,max_eq_right hXtwo] using hdecl.1
  have hwidth : (1:ℝ) ≤ Real.logb Z Z+Real.logb Z (src.η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost := by
    rw [Real.logb_self_eq_one hZ]
    linarith [Real.logb_nonneg hZ coherent_exceptional_fixed_presentation_one]
  have hvolOne : 1 ≤ volume src := by
    unfold volume
    have hslots : 1 ≤ ∏ i,src.P i := Finset.one_le_prod₀ (fun i _ => by rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i))
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hXone hXtwo) hslots
  let leftRun := fun k : (i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex =>
    actualAmplifierErrorRun src (q k.1).C P τ ((q k.1).sourceChild k.2).pair.left (t k)
  let rightRun := fun k : (i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex =>
    actualAmplifierErrorRun src (q k.1).D P τ ((q k.1).sourceChild k.2).pair.right (t k)
  have hadm (k : (i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex) (hk : k ∈ firstSourceLabels labels q) :
      (leftRun k).SourceAdmissible (q k.1).D R (q k.1).E ((q k.1).sourceChild k.2).pair.left
        Z Z (9/500) delta reserve 3 (Z^ν) ∧
      (rightRun k).SourceAdmissible (q k.1).C R (swapSubset (q k.1).C (q k.1).D (q k.1).E)
        ((q k.1).sourceChild k.2).pair.right Z Z (9/500) delta reserve 3 (Z^ν) := by
    have hn := actual_first_label_norm_caps src R seed hs hzero₁ hzero₂ Z 1 hsource k.1.1
    have hh := hadmit.2 τ hτ src
    constructor
    · exact hh (q k.1).C (q k.1).D R (q k.1).hC (q k.1).hD (q k.1).hCD (q k.1).E
        ((q k.1).sourceChild k.2).pair.left (t k) Z delta reserve 3 (Z^ν) 1 1 1
        hz hvolOne (ht k hk) hupperSrc w hwmesh hmatch.scale hn.1 hn.2 (by simp) hdelta hreserve (by norm_num)
    · exact hh (q k.1).D (q k.1).C R (q k.1).hD (q k.1).hC (q k.1).hCD.symm (swapSubset _ _ (q k.1).E)
        ((q k.1).sourceChild k.2).pair.right (t k) Z delta reserve 3 (Z^ν) 1 1 1
        hz hvolOne (ht k hk) hupperSrc w hwmesh hmatch.scale hn.2 hn.1 (by simp) hdelta hreserve (by norm_num)
  let p := ref.radicalWidth Z+lowLocalTiny
  have hradical (i) (hi : i ∈ labels) : ((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^p := by
    have hn := CenteredMomentFirstScale.norm_pos _ (commonRadical_ne_zero i.1.val.1 i.1.val.2)
    calc
      _ = Z^((q i).radicalWidth Z) := (Real.rpow_logb hz hZ.ne' hn).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (hrad i hi)
  have hbound := hmain.2 θ w σ freq height lowLocalMesh hmesh0 hw hwmesh (fun i => (hwmesh i).trans hmesh)
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc le_rfl hlowerSrc hupperSrc hb10 hb20 hb1max hb2max hηcap
    R seed hR hs hs0 hzero₁ hzero₂ hvolCap hRN hsource₀ hsource profile hp₁ hp₂
    (plain_scale_le_base _ _ src.X₁_pos hZ hn₁) (plain_scale_le_base _ _ src.X₂_pos hZ hn₂)
    (by calc
      src.Y₁ = Z^(Real.logb Z src.Y₁) := (Real.rpow_logb hz hZ.ne' src.Y₁_pos).symm
      _ ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le hm₁)
    (by calc
      src.Y₂ = Z^(Real.logb Z src.Y₂) := (Real.rpow_logb hz hZ.ne' src.Y₂_pos).symm
      _ ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le hm₂)
    Z delta reserve aSource hz haSource hdelta hreserve le_rfl hP Mdecl
    (1+Real.logb Z (src.η.modulus.absNorm : ℝ)) lowLocalTiny htiny.le hcapacity
    (by simpa only [Real.logb_self_eq_one hZ] using hdecl.2.1) (by rw [Real.logb_self_eq_one hZ])
    (by norm_num [lowLocalTiny] at hηsmall ⊢;linarith) hfixed.2.2.1 le_rfl
    1 1 (Z^ν) le_rfl (by positivity) hX₁ hX₂ hY₁ hY₂ hwidth (by linarith) (by linarith)
    hfixedlog.2 (by simpa only [Real.logb_self_eq_one hZ] using hdecl.2.2)
    (hpaid delta reserve lowLocalMesh homega hmeshcap) (homega.trans (by norm_num [lowLocalTiny]))
    (by simpa using hεsmall) radius hradius labels p hradical leftRun rightRun
    (fun k hk => (hadm k (Finset.mem_filter.mp hk).1).1)
    (fun k hk => (hadm k (Finset.mem_filter.mp hk).1).2)
    ref A lowLocalTiny lowLocalTiny (hrefParent.trans hη.symm) hvol le_rfl hleftWidth hrightWidth
  have hmass : mass src ≤ Mslot^Fintype.card α := input_profile_mass_le src Mslot hMslot hMs
  have hheightPower : (1+Z^ν+height)^J ≤ (3:ℝ)^J*Z^(ν*(J:ℝ)) := by
    have hone := Real.one_le_rpow hZ.le hν.le
    calc
      _ ≤ (3*Z^ν)^J := by gcongr;nlinarith
      _ = _ := by rw [mul_pow,←Real.rpow_natCast (Z^ν) J,←Real.rpow_mul hz.le]
  have hfront : ref.parentCost*(Cbound*profile.control U^2*(1+Z^ν+height)^J*mass src^2) ≤ C*Z^(ν*(J:ℝ)) := by
    have hpc : ref.parentCost = parentCost := by simp only [FirstJointLabel.parentCost,hrefParent,parentCost]
    rw [hpc]
    calc
      _ ≤ parentCost*(Cbound*profile.control U^2*((3:ℝ)^J*Z^(ν*(J:ℝ)))*(Mslot^Fintype.card α)^2) := by
        have hm0 := CenteredMomentFirstChildProfileControl.mass_nonneg src
        have hpc0 : 0 ≤ parentCost := by dsimp only [parentCost];positivity
        gcongr
      _ = _ := by dsimp only [C];ring
  have hremaining : -(1/2500:ℝ)+1/100000+lowLocalTiny+lowLocalTiny+ν*(J:ℝ) ≤ -1/10000 := by
    norm_num [lowLocalTiny] at ⊢
    linarith
  intro side
  have hside : volume src*(∑ k ∈ firstSideSourceLabels labels q (fun _ => sourceRadius src) side,
      firstCoherentErrorTerm src R seed Z radius k side upper delta reserve (t k) P τ) ≤
      (volume src/((ref.sideCommon side).absNorm : ℝ))*ref.parentCost*
        (Cbound*profile.control U^2*(1+Z^ν+height)^J*mass src^2)*
        Z^(ref.sideTargetWidth side Z A-1/2500+1/100000+lowLocalTiny+lowLocalTiny)/(seed.absNorm : ℝ) := by
    cases side
    · have hid : (∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
          firstCoherentErrorTerm src R seed Z radius k false upper delta reserve (t k) P τ) =
        ∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
          (rightRun k).value (Fintype.card α) (q k.1).C R k.2.1.val
            (swapSubset (q k.1).C (q k.1).D (q k.1).E)
            ((q k.1).sourceChild k.2).pair.right upper Z Z (9/500) delta reserve := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (((q k.1).sourceChild k.2).actual_amplifier_error_value src false P τ _ R k.2.1.val
          (t k) upper Z Z (9/500) delta reserve).symm
      change volume src*(∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
        firstCoherentErrorTerm src R seed Z radius k false upper delta reserve (t k) P τ) ≤ _
      rw [hid]
      exact hbound.2
    · have hid : (∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
          firstCoherentErrorTerm src R seed Z radius k true upper delta reserve (t k) P τ) =
        ∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
          (leftRun k).value (Fintype.card α) (q k.1).D R k.2.1.val (q k.1).E
            ((q k.1).sourceChild k.2).pair.left upper Z Z (9/500) delta reserve := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (((q k.1).sourceChild k.2).actual_amplifier_error_value src true P τ _ R k.2.1.val
          (t k) upper Z Z (9/500) delta reserve).symm
      change volume src*(∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
        firstCoherentErrorTerm src R seed Z radius k true upper delta reserve (t k) P τ) ≤ _
      rw [hid]
      exact hbound.1
  have hNC : 0 < ((ref.sideCommon side).absNorm : ℝ) := CenteredMomentFirstScale.norm_pos _ (ref.sideCommon_supported side).1
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le (show
    ref.sideTargetWidth side Z A-1/2500+1/100000+lowLocalTiny+lowLocalTiny+ν*(J:ℝ) ≤
      ref.sideTargetWidth side Z A-1/10000 by linarith)
  have hh : volume src*(∑ k ∈ firstSideSourceLabels labels q (fun _ => sourceRadius src) side,
      firstCoherentErrorTerm src R seed Z radius k side upper delta reserve (t k) P τ) ≤
      volume src*((C+1)/(seed.absNorm : ℝ))*(1/((ref.sideCommon side).absNorm : ℝ))*
        Z^(ref.sideTargetWidth side Z A-1/10000) := by
    apply hside.trans
    calc
      _ ≤ (volume src/((ref.sideCommon side).absNorm : ℝ))*(C*Z^(ν*(J:ℝ)))*
          Z^(ref.sideTargetWidth side Z A-1/2500+1/100000+lowLocalTiny+lowLocalTiny)/(seed.absNorm : ℝ) := by
        have hh := mul_le_mul_of_nonneg_left hfront (show 0 ≤ volume src/((ref.sideCommon side).absNorm : ℝ) by positivity)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by simpa only [mul_assoc] using hh)
          (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _)
      _ = (volume src/((ref.sideCommon side).absNorm : ℝ))*C*
          Z^(ref.sideTargetWidth side Z A-1/2500+1/100000+lowLocalTiny+lowLocalTiny+ν*(J:ℝ))/(seed.absNorm : ℝ) := by
        rw [Real.rpow_add hz (ref.sideTargetWidth side Z A-1/2500+1/100000+lowLocalTiny+lowLocalTiny) (ν*(J:ℝ))];ring
      _ ≤ (volume src/((ref.sideCommon side).absNorm : ℝ))*(C+1)*
          Z^(ref.sideTargetWidth side Z A-1/10000)/(seed.absNorm : ℝ) := by gcongr <;> linarith
      _ = _ := by ring
  apply (mul_le_mul_iff_right₀ hv).mp
  convert hh using 1 <;> dsimp only [A] <;> ring

#print axioms actual_literal_first_extracted_error_target
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLocalErrorTarget -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstFourierTargetJoin ; sha256 be3f836ad6737ce6b4d5f590ac862c10ba599eb536db0953324452bb51007735 -/
section



/-! Uniform actual annular targets give the two first Fourier targets.
A strict height gap absorbs all fixed 2*pi factors before the live scale. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentFirstAnnularMajorant

theorem eventually_first_fourier_targets_of_annular (ν η : ℝ) (hgap : ν < η) :
    ∀ᶠ Z : ℝ in atTop,
    ∀ {Λ Slot : Type*} [DecidableEq Λ] [Fintype Slot]
      (labels : Finset Λ) (q : Λ → FirstJointLabel Slot) (ref : FirstJointLabel Slot)
      (t H : Λ → ℝ) (V A Ch : ℝ),
      (∀ i ∈ labels,|t i| ≤ Z^ν) →
      (∀ u : Bool → ((i : Λ) × (q i).SourceIndex) → ℝ,
        (∀ left,∀ k ∈ firstSourceLabels labels q,|u left k| ≤ Z^η) →
        ∀ left,
          (∑ k ∈ firstSourceLabels labels q,
            ((q k.1).sourceChild k.2).sideEnergy left (u left k) profile (H k.1)) ≤
          (V/((ref.sideCommon left).absNorm : ℝ))*(Ch*Z^(ref.sideTargetWidth left Z A))) →
      ∀ θ w : ℝ,‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
        (∑ k ∈ firstSourceLabels labels q,
          ((q k.1).sourceChild k.2).leftEnergy (t k.1+2*Real.pi*(w-θ)) profile (H k.1)) ≤
          (V/(ref.C.absNorm : ℝ))*(Ch*Z^(ref.leftTargetWidth Z A)) ∧
        (∑ k ∈ firstSourceLabels labels q,
          ((q k.1).sourceChild k.2).rightEnergy (t k.1+2*Real.pi*(w-(-θ))) profile (H k.1)) ≤
          (V/(ref.D.absNorm : ℝ))*(Ch*Z^(ref.rightTargetWidth Z A)) := by
  filter_upwards [eventually_first_literal_shifted_heights ν η hgap] with Z hshift
  intro Λ Slot inst inst' labels q ref t H V A Ch ht hannular θ w hθ hw
  let u : Bool → ((i : Λ) × (q i).SourceIndex) → ℝ :=
    fun left k => if left then t k.1+2*Real.pi*(w-θ) else t k.1+2*Real.pi*(w-(-θ))
  have hu (left) (k) (hk : k ∈ firstSourceLabels labels q) : |u left k| ≤ Z^η := by
    have hi : k.1 ∈ labels := by
      simpa only [firstSourceLabels,Finset.mem_sigma,Finset.mem_univ,and_true] using hk
    have hh := hshift (t k.1) w θ (ht k.1 hi)
      (by simpa only [Real.norm_eq_abs] using hw) (by simpa only [Real.norm_eq_abs] using hθ)
    cases left
    · exact hh.2
    · exact hh.1
  exact ⟨hannular u hu true,hannular u hu false⟩

#print axioms eventually_first_fourier_targets_of_annular
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstFourierTargetJoin -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstFullSectorSum ; sha256 274ad5d1592492ed3ae8fd6db4d73893ef0c730b0f6d4777112979d58019143a -/
section


/-! Uniform first-sector estimates sum over a number of cells fixed
before the scale and arithmetic labels. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic

theorem uniform_first_full_sector_sum (B e : ℝ) (hB : 0 ≤ B) (he : 0 < e) :
    ∃ Ccells : ℝ, 0 < Ccells ∧
    ∀ {Row Slot : Type*} [DecidableEq Row] [Fintype Slot]
      (labels : Finset Row) (q : Row → FirstJointLabel Slot) (Z : ℝ), 1 < Z →
      (∀ u ∈ labels,(q u).C.absNorm ≤ (Z^B : ℝ) ∧ (q u).D.absNorm ≤ (Z^B : ℝ)) →
      ∀ (f : Row → ℝ) (H : ℝ), 0 ≤ H →
      (∀ (cell : Finset Row),cell ⊆ labels → ∀ ref ∈ cell,
        (∀ u ∈ cell,∀ j,|(q u).fullWidthCoordinates Z j-(q ref).fullWidthCoordinates Z j| < e) →
        (∀ u ∈ cell,(q ref).activeWidth Z/2+(q ref).punctureWidth Z ≤
          (q u).activeWidth Z/2+(q u).punctureWidth Z) →
        (∑ u ∈ cell,f u) ≤ H) →
      (∑ u ∈ labels,f u) ≤ Ccells*H := by
  obtain ⟨N,hN⟩ := uniform_first_full_sectors B e hB he
  let Code := Fin 11 → Fin (N+1)
  refine ⟨(Fintype.card Code : ℝ),?_,?_⟩
  · exact_mod_cast Fintype.card_pos
  intro Row Slot inst inst' labels q Z hZ hcap f H hH hsector
  obtain ⟨bin,hclose,href⟩ := hN labels q Z hZ hcap
  let code (u : {u : Row // u ∈ labels}) : Code := bin u.val u.property
  have hcell (b : Code) :
      (∑ u ∈ labels.attach.filter (fun u => code u = b),f u.val) ≤ H := by
    let cell := labels.attach.filter (fun u => code u = b)
    by_cases hn : cell.Nonempty
    · obtain ⟨r,hr,hmin⟩ := href b hn
      let actual := cell.image Subtype.val
      have ha : actual ⊆ labels := by
        intro u hu
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
        exact v.property
      have hr' : r.val ∈ actual := Finset.mem_image.mpr ⟨r,hr,rfl⟩
      have hh := hsector actual ha r.val hr' (by
        intro u hu j
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
        exact hclose v.val r.val v.property r.property
          ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hr).2.symm) j) (by
        intro u hu
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
        exact hmin v hv)
      simpa only [actual,Finset.sum_image (fun x _ y _ h => Subtype.ext h)] using hh
    · have hz : cell = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      change (∑ u ∈ cell,f u.val) ≤ H
      simpa only [hz,Finset.sum_empty] using hH
  calc
    (∑ u ∈ labels,f u) = ∑ u ∈ labels.attach,f u.val := (Finset.sum_attach _ _).symm
    _ = ∑ b : Code,∑ u ∈ labels.attach.filter (fun u => code u = b),f u.val := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
    _ ≤ ∑ _b : Code,H := Finset.sum_le_sum (fun b _ => hcell b)
    _ = _ := by simp

#print axioms uniform_first_full_sector_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstFullSectorSum -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstHighCellBound ; sha256 09a012fdfa3ce7f8f1f83e2c1fb741d89156f2e71503398f62af82a865f3f30a -/
section






/-! The genuine high-source estimate summed over both actual dyadic block
families. Maximization pays their subpower mass without recounting arithmetic rows. -/
set_option autoImplicit false
set_option maxRecDepth 8192
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
open NonzeroJointSourceRow CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentActive CenteredMomentCompleteCommon
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSourceRow CenteredMomentSecondLiveBlock
open CanonicalRowCompletion CenteredMomentRankinRadical ActualEisensteinCubic
open ActualFirstSecondSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstPhysicalDyadicAssembly
local notation "O" => HeckeFamily.O

variable {Cell κbin : Type*} [Fintype Cell] [DecidableEq Cell] [DecidableEq κbin]
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

theorem actual_first_high_cell_bound
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
    (hdyadicLoss : 0 < dyadicLoss)
    (rowAbsorb : ℝ) (hrowAbsorb : 0 < rowAbsorb)
    (haSource_eq : aSource = (∏ j, lo j)*a₁*a₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N Nkernel : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (src : Input Slot) (Rmask seed : Ideal O) (hs : Squarefree seed)
        (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0) (Kfirst : ℝ)
        (radius : (p : Labels src Rmask seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
        (side : Bool) (A Mparent omega ξ : ℝ)
        (bin : NonzeroElement → Option κbin) (bidx : κbin)
        (height : First src Rmask seed Kfirst radius → ℝ)
        (labels : Finset (FirstSourceOuterIndex src Rmask seed Kfirst radius))
        (cell : LivePacket src Rmask seed Kfirst radius side Z A Mparent omega ξ → Cell)
        (target : ℝ),
      0 < actualHighPrimeCount M H Sbad Z →
      let X := liveBinPackets src Rmask seed Kfirst radius side Z A Mparent omega ξ hs hz₁ hz₂
        bin bidx height Wkernel labels;
      (∀ c : Cell, ∀ χ₁ ξ₁ : RayCharacter,
        (rayPackets (X.filter (fun x => cell x=c)) χ₁ ξ₁).Nonempty →
        ∃ actualExponent : ℝ, HighPacketSourceData η η₀ Q hQ72 M H hH hQM hQη₀ ηcommon Wslot bslot Rwidth dmax e σmin σmax loss B dmin heightLoss I W₁ W₂ b₁ b₂plain lo hi fiberLoss Mslot upper conductorReserve Sbad Wkernel tailA targetLower Bdyad₁ Ldyad₁ Crdyad₁ Bdyad₂ Ldyad₂ Crdyad₂ dyadicLoss rowAbsorb Z τ ν
          (∑ x∈rayPackets (X.filter (fun x => cell x=c)) χ₁ ξ₁,
            packetValue hs hz₁ hz₂ (CenteredMomentExceptionalAmplitudePair.volume src.toData)
              (actualHighPrimeCount M H Sbad Z) height Wkernel x) actualExponent ∧ actualExponent ≤ target) →
      (∑ k∈firstSideSourceLabels labels (firstSourceOuterLabel src Rmask seed Kfirst radius)
        (fun _ => sourceRadius src) side,
        ‖firstLowBinBlock src Rmask seed hs hz₁ hz₂ Kfirst radius k side Z A Mparent omega ξ
          (height k) Wkernel bin bidx‖ /
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*actualHighPrimeCount M H Sbad Z)) ≤
        (Fintype.card Cell : ℝ)*(Fintype.card RayCharacter : ℝ)^2*C*Z^target := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_high_packet_data_bound η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV ηcommon hanchor Wslot hVslot bslot hBslot
      Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B
      hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget hproductLoss hpopulationLoss hB hloss
      τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi fiberLoss hfiberLoss
      aSource Mslot upper haSource hMslot conductorReserve hconductorReserve
      Sbad primeLoss hprimeLoss hprimeReserve Wkernel tailA targetLower plainBound₁ plainBound₂
      hplainBound₁ hplainBound₂ hplainNorm₁ hplainNorm₂
      Bdyad₁ Ldyad₁ Crdyad₁ Bdyad₂ Ldyad₂ Crdyad₂ dyadicLoss
      hBdyad₁ hLdyad₁ hCrdyad₁ hBdyad₂ hLdyad₂ hCrdyad₂ hdyadicLoss
      rowAbsorb hrowAbsorb haSource_eq
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,?_⟩
  filter_upwards [hhigh] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro src Rmask seed hs hz₁ hz₂ Kfirst radius side A Mparent omega ξ bin bidx height labels cell target hP X hdata
  apply (actual_first_high_cell_majorant src Rmask seed Kfirst radius side Z A Mparent omega ξ
    hs hz₁ hz₂ bin bidx height Wkernel (zero_lt_one.trans hZ.1) labels
    (actualHighPrimeCount M H Sbad Z) hP cell).trans
  have hpiece : ∀ c : Cell, ∀ χ₁ ξ₁ : RayCharacter,
      (∑ x∈rayPackets (X.filter (fun x => cell x=c)) χ₁ ξ₁,
        packetValue hs hz₁ hz₂ (CenteredMomentExceptionalAmplitudePair.volume src.toData)
          (actualHighPrimeCount M H Sbad Z) height Wkernel x) ≤ C*Z^target := by
    intro c χ₁ ξ₁
    by_cases hn : (rayPackets (X.filter (fun x => cell x=c)) χ₁ ξ₁).Nonempty
    · obtain ⟨actualExponent,hd,he⟩ := hdata c χ₁ ξ₁ hn
      exact (hZ.2 _ actualExponent hd).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.1.le he) hC.le)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty]
      exact mul_nonneg hC.le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  calc
    _ ≤ ∑ c : Cell,∑ χ₁ : RayCharacter,∑ ξ₁ : RayCharacter,C*Z^target := by
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro χ₁ hχ₁
      apply Finset.sum_le_sum
      intro ξ₁ hξ₁
      exact hpiece c χ₁ ξ₁
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end FixedData
#print axioms actual_first_high_cell_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstHighCellBound -/
