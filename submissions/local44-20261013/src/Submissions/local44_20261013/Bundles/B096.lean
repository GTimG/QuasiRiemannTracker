/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.local44_20261013.Bundles.B033
import Submissions.local44_20261013.Bundles.B047
import Submissions.local44_20261013.Bundles.B065
import Submissions.local44_20261013.Bundles.B066
import Submissions.local44_20261013.Bundles.B071
import Submissions.local44_20261013.Bundles.B075
import Submissions.local44_20261013.Bundles.B081
import Submissions.local44_20261013.Bundles.B082
import Submissions.local44_20261013.Bundles.B083
import Submissions.local44_20261013.Bundles.B085
import Submissions.local44_20261013.Bundles.B087
import Submissions.local44_20261013.Bundles.B089
import Submissions.local44_20261013.Bundles.B092
import Submissions.local44_20261013.Bundles.B093
import Submissions.local44_20261013.Bundles.B094
import Submissions.local44_20261013.Bundles.B095
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGaussianCentral
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalHeight

/- BEGIN ORIGINAL MODULE Analytic.JointLowSelectedKernel ; sha256 2a80b19920162c55071cd2bf7c35ef8941a4ce69b1fa77d9810a143ba2ee555a -/
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
local instance selectedLowKernelFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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
theorem actual_selected_second_low_kernel_of_common_bin
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
      ∀ (P₁ Q₁ : Ideal O) (hP₁ : Supported P₁),
      ∀ (C₁ D₁ Rmask seed Lproj Lfirst : Ideal O) (hC₁ : Supported C₁) (hD₁ : D₁ ≠ 0)
        (p₂ : ActiveLabel (commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁)
          (commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst)),
      let C₂ := p₂.val.1
      let D₂ := p₂.val.2
      let hC₂ := lowActiveLeftSupported p₂
      let hD₂ := lowActiveRightSupported p₂
      primeSupport C₂ = primeSupport D₂ →
      ∀ (E₁ : Finset (CommonIndex P₁ Q₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂),
      let u := firstSideDictionaryUnit ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F
      activeConductor P₁ Q₁ = (u : O)*∏ i,activePrimary P₁ Q₁ i ∧
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
      let r₁ := Real.logb Z (normValue (activeConductor P₁ Q₁))
      let e₁ := Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex P₁ Q₁ => P.val) E₁))
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
          (secondReconstructedRow P₁ Q₁ hP₁ E₁ u C₂ D₂ hC₂ U left z (sL.row_ne_zero z hz.1))) →
      (∀ z, ∀ hz : (supportedNaturalState sR).radial.keep z, low (-z) →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (holes (-z)) (hholes (-z)) abin (abin+e) (3*(k+1 : ℕ)*Z^τ)
          (secondReconstructedRow P₁ Q₁ hP₁ E₁ u C₂ D₂ hC₂ U left (-z) (neg_ne_zero.mpr (sR.row_ne_zero z hz.1)))) →
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
  obtain ⟨degree,S,hmain⟩ := actual_selected_second_low_paired_values_of_common_bin M H hH W
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
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ Rmask seed Lproj Lfirst hC₁ hD₁ p₂ C₂ D₂ hC₂ hD₂ hCD₂
    E₁ ξ₁ ξ₂ F
  let u := firstSideDictionaryUnit ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F
  have hbase (vL vR : ℝ) := hmain hZ θ w σ freq vL vR height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ Rmask seed Lproj Lfirst hC₁ hD₁ p₂ hCD₂ E₁ ξ₁ ξ₂ F
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

#print axioms actual_selected_second_low_kernel_of_common_bin
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSelectedKernel -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceExtension ; sha256 8404708b6b41fb59f0523754dffa6cd98bc2371ed992933a99f03f83ae053329 -/
section


/-! A concrete extension of nonzero actual source rows to the full arithmetic
label type. On the source image it is an inverse, so all canonical data and
finite sums transport exactly. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve
open CenteredMomentFirstAmplificationChoice RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot]

abbrev NonzeroJointSourceRow (s : OriginalData Slot) (side : Bool) :=
  {q : ActualJointSourceRow s side // q.z ≠ 0}

namespace NonzeroJointSourceRow
variable {s : OriginalData Slot} {side : Bool}

def label (q : NonzeroJointSourceRow s side) := q.val.label

theorem label_injective : Function.Injective (label (s := s) (side := side)) := by
  intro q r h
  exact Subtype.ext (ActualJointSourceRow.label_injective h)

/-- A default source row is needed only outside the finite image. All data
there remains actual and nonzero, which also discharges global source identities. -/
def recover (fallback : NonzeroJointSourceRow s side) :
    JointReconstructionLabel → NonzeroJointSourceRow s side :=
  Function.extend label id (fun _ => fallback)

@[simp] theorem recover_label (fallback q : NonzeroJointSourceRow s side) :
    recover fallback q.label = q := label_injective.extend_apply id (fun _ => fallback) q

theorem recover_mem (fallback : NonzeroJointSourceRow s side)
    (rows : Finset (NonzeroJointSourceRow s side)) (v : JointReconstructionLabel)
    (hv : v ∈ rows.image label) : recover fallback v ∈ rows := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  simpa only [recover_label] using hq

theorem label_recover (fallback : NonzeroJointSourceRow s side)
    (rows : Finset (NonzeroJointSourceRow s side)) (v : JointReconstructionLabel)
    (hv : v ∈ rows.image label) : (recover fallback v).label = v := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  rw [recover_label]

def sourceUnit (fallback : NonzeroJointSourceRow s side) (η : Character)
    (ξ₁ ξ₂ : RayCharacter) (v : JointReconstructionLabel) : Oˣ :=
  (recover fallback v).val.unit η ξ₁ ξ₂

def sourceRow (fallback : NonzeroJointSourceRow s side) (η : Character)
    (ξ₁ ξ₂ : RayCharacter) (v : JointReconstructionLabel) : NonzeroElement :=
  (recover fallback v).val.reconstructed η ξ₁ ξ₂ (recover fallback v).property

theorem sourceRow_canonical (fallback : NonzeroJointSourceRow s side) (η : Character)
    (ξ₁ ξ₂ : RayCharacter) (rows : Finset (NonzeroJointSourceRow s side))
    (v : JointReconstructionLabel) (hv : v ∈ rows.image label) :
    (sourceRow fallback η ξ₁ ξ₂ v).val = v.row (sourceUnit fallback η ξ₁ ξ₂ v) := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  simp only [sourceRow,sourceUnit,recover_label]
  exact (q.val.label_row η ξ₁ ξ₂ q.property).symm

theorem sourceImage_gates (rows : Finset (NonzeroJointSourceRow s side))
    (hL : ∀ q ∈ rows, Squarefree q.val.L) :
    ∀ v ∈ rows.image label,
      (Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) ∧
      (CompletedGauss.primeSupport v.C₁ = CompletedGauss.primeSupport v.D₁ ∧
        CompletedGauss.primeSupport v.C₂ = CompletedGauss.primeSupport v.D₂) ∧
      (Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) := by
  intro v hv
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  refine ⟨q.val.label_supported,q.val.label_equal_support,?_,q.val.label_projector_dvd⟩
  have hh := hL q hq
  cases side <;> exact hh

theorem sum_recover {M : Type*} [AddCommMonoid M]
    (fallback : NonzeroJointSourceRow s side) (rows : Finset (NonzeroJointSourceRow s side))
    (f : NonzeroJointSourceRow s side → M) :
    (∑ v ∈ rows.image label, f (recover fallback v)) = ∑ q ∈ rows, f q := by
  rw [Finset.sum_image (fun _ _ _ _ h => label_injective h)]
  simp only [recover_label]

theorem card_image (rows : Finset (NonzeroJointSourceRow s side)) :
    (rows.image label).card = rows.card := Finset.card_image_of_injective _ label_injective

def sourceFirst (fallback : NonzeroJointSourceRow s side) (η : Character)
    (ξ₁ ξ₂ : RayCharacter) (v : JointReconstructionLabel) : FirstSidePresentation η :=
  (recover fallback v).val.firstPresentation η ξ₁ ξ₂

def sourceFrequency (fallback : NonzeroJointSourceRow s side) (v : JointReconstructionLabel) : O :=
  (recover fallback v).val.z

theorem sourceFrequency_nonzero (fallback : NonzeroJointSourceRow s side)
    (v : JointReconstructionLabel) : sourceFrequency fallback v ≠ 0 := (recover fallback v).property

def sourceKernel (input : Input Slot) (puncture seed : Ideal O) (side : Bool)
    (hseed : Squarefree seed) (hz₁ : input.W₁ 0 = 0) (hz₂ : input.W₂ 0 = 0)
    (fallback : NonzeroJointSourceRow (original input puncture seed) side)
    (η : Character) (ξ₁ ξ₂ χ₁ χ₂ : RayCharacter) (v : JointReconstructionLabel) :
    CommonSecondKernelLabel Slot :=
  (recover fallback v).val.kernelLabel input puncture seed η ξ₁ ξ₂ χ₁ χ₂ 1
    ((recover fallback v).val.seed_dvd_first input puncture seed hseed hz₁ hz₂)

theorem sourceKernel_parent (input : Input Slot) (puncture seed : Ideal O) (side : Bool)
    (hseed : Squarefree seed) (hz₁ : input.W₁ 0 = 0) (hz₂ : input.W₂ 0 = 0)
    (fallback : NonzeroJointSourceRow (original input puncture seed) side)
    (η : Character) (ξ₁ ξ₂ χ₁ χ₂ : RayCharacter) (v : JointReconstructionLabel) :
    (sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ χ₁ χ₂ v).parent =
      (sourceFirst fallback η ξ₁ ξ₂ v).sourceParent := rfl

theorem sourceKernel_row (input : Input Slot) (puncture seed : Ideal O) (side : Bool)
    (hseed : Squarefree seed) (hz₁ : input.W₁ 0 = 0) (hz₂ : input.W₂ 0 = 0)
    (fallback : NonzeroJointSourceRow (original input puncture seed) side)
    (η : Character) (ξ₁ ξ₂ χ₁ χ₂ : RayCharacter) (v : JointReconstructionLabel) :
    sourceRow fallback η ξ₁ ξ₂ v =
      (sourceFirst fallback η ξ₁ ξ₂ v).row
        (sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ χ₁ χ₂ v)
        (sourceFrequency fallback v) (sourceFrequency_nonzero fallback v) := rfl

end NonzeroJointSourceRow
#print axioms NonzeroJointSourceRow.sourceRow_canonical
#print axioms NonzeroJointSourceRow.sourceImage_gates
#print axioms NonzeroJointSourceRow.sum_recover
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceExtension -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowGaussianCentral ; sha256 0f6fefcc272318de44d71093f5c0546cba527dde684d30a7d4574375eae881aa -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowGaussianCentral.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace LowProbe
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma not_lowRemote_bounds (Z ell ε U : ℝ) (hZ : 0< Z)
    (h : ¬lowRemote Z ell ε U) :
    Z^(1+ell-ε/2)≤ U ∧ U≤ Z^(1+ell+ε/2) := by
  simp only [lowRemote,not_or,not_le] at h
  apply lowCentral_ratio_bounds Z U ell ε hZ
  · have he : Z^(-ε/2)=(Z^(ε/2))⁻¹ := by
      rw [show -ε/2=-(ε/2) by ring,Real.rpow_neg hZ.le]
    rw [he]
    exact h.1.le
  · exact h.2.le

theorem low_central_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Submission20261012.Global.ell)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hM : 0≤ M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤ M) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=> if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
          W (fun i=> Z^(ell i)) J (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖
      Summable f ∧ (∑'j : ℕ,f j)≤ C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+256*ε) := by
  obtain ⟨degree,C,hC,he⟩ := low_central_gaussian_dyad η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  obtain ⟨Cm,hCm,hm⟩ := gaussianJointMoment_summed V hV degree ε hε
  refine ⟨C*Cm,mul_pos hC hCm,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  let R := Z^(1+lowSelectedLength ell J)
  let f := fun j : ℕ=> if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
    ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
      W (fun i=> Z^(ell i)) J (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) ((2:ℝ)^j) R V hV‖
  have hz : 0< Z := lt_trans zero_lt_one hZ.1
  obtain ⟨hsm,hmb⟩ := hm R (by dsimp [R];positivity)
  have hb (j : ℕ) : f j≤(C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε))*
      (((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := by
    dsimp only [f]
    split_ifs with hj
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (gaussianJointMoment_nonneg V hV degree _))
    · obtain ⟨hlo,hhi⟩ := not_lowRemote_bounds Z (lowSelectedLength ell J) ε ((2:ℝ)^j) hz hj
      apply (hZ.2 T hT hout hdis hnorm J ((2:ℝ)^j) (by positivity) hlo hhi W hW V hV).trans
      have hp : 1≤((2:ℝ)^j)^ε := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hε.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_mul_of_one_le_left (gaussianJointMoment_nonneg V hV degree _) hp
  have hn (j : ℕ) : 0≤ f j := by dsimp [f];split_ifs <;> positivity
  have hsumf := Summable.of_nonneg_of_le hn hb (hsm.mul_left (C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε)))
  refine ⟨hsumf,?_⟩
  calc
    _≤∑'j : ℕ,(C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε))*(((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) :=
      hsumf.tsum_le_tsum hb (hsm.mul_left _)
    _=(C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε))*(∑'j : ℕ,((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := tsum_mul_left
    _≤(C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε))*(Cm*R^ε) := mul_le_mul_of_nonneg_left hmb (by positivity)
    _≤_ := by
      dsimp only [R]
      rw [←Real.rpow_mul hz.le]
      calc
        _=(C*Cm)*(Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε)*Z^((1+lowSelectedLength ell J)*ε)) := by ring
        _≤_ := by
          rw [←Real.rpow_add hz]
          apply mul_le_mul_of_nonneg_left _ (mul_pos hC hCm).le
          have hh := lowLength_bounds ell hell hsum J
          exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by nlinarith [Submission20261012.Global.ell_lt_one_fifth])

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowGaussianCentral -/

/- BEGIN ORIGINAL MODULE Analytic.ActualAllocatedErrorUniformFull ; sha256 ff04347669abd586a5ebcc215500c8f034a5ed2a94790841192bdf442a956f21 -/
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
local instance actualAllocatedErrorUniformDecEqFull {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance actualAllocatedErrorUniformFiniteFull : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem actual_allocated_extracted_errors_uniform_full
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
  obtain ⟨Dalloc,hDalloc,Uprofile,Jheight,hactual⟩ := actual_allocated_extracted_errors_full (α := α) M H hH
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
  intro θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    C D R0 hC hD hCD E τ t hmod K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hP hslot family hrad hfamily
  intro hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv hconductorCap seed hseed hseed0 hseedcap
    profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip
    hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂ hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
  intro Bfirst heightCap hheightCap ht hCcap hallocSmall hpaid hfrequency hepsSmall
  have hh := hZ.2 θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
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

#print axioms actual_allocated_extracted_errors_uniform_full
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualAllocatedErrorUniformFull -/

/- BEGIN ORIGINAL MODULE Analytic.ActualFirstExtractedErrors ; sha256 5eef7887f63007fd01a89b30361a56d544c07286d5948b917c82f10ad792ab84 -/
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
local instance actualFirstExtractedErrorsDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance actualFirstExtractedErrorsFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

/-- An actual extracted-error source run, including its full family of
second allocations and amplification primes. -/
structure ExtractedErrorRun {Slot : Type*} [Fintype Slot]
    (s : Input Slot) (C : Ideal O) (P : Finset (Ideal O)) where
  height : ℝ
  family : actualAllocations s.pools C → elementPool P → Fin 3 → RayCharacter → Character

namespace ExtractedErrorRun
variable {Slot : Type*} [Fintype Slot]

def normalizedValue {s : Input Slot} {C : Ideal O} {P : Finset (Ideal O)}
    (x : ExtractedErrorRun s C P) (N : ℕ) (D R seed : Ideal O)
    (E : Finset (CommonIndex C D)) (τ : Character) (upper Z K sigma delta reserve : ℝ) : ℝ :=
  allocatedExtractedErrors N s C R seed τ x.height upper Z
    (Real.logb Z (D.absNorm : ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s)))
    (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve P x.family /
    ((τ.modulus.absNorm : ℝ)*(volume s/(C.absNorm : ℝ)^2)*Z^(allowance C D Z))

/-- Only literal support, conductor and scalar geometric caps are kept
in this packet. Its normalized error estimate is proved analytically. -/
structure Admissible {s : Input Slot} {C : Ideal O} {P : Finset (Ideal O)}
    (x : ExtractedErrorRun s C P) (D R : Ideal O) (E : Finset (CommonIndex C D))
    (τ : Character) (Z K sigma delta reserve cost Dscale qmoving Bfirst heightCap : ℝ) : Prop where
  height_le : |x.height| ≤ heightCap
  common_cap : (C.absNorm : ℝ) ≤ Z^Bfirst
  slot_coprime : ∀ B : actualAllocations s.pools C,
    frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 →
    ∀ (prime : elementPool P) i, ∀ I ∈ (activeInput (child s C R B τ x.height)).slots i,
      IsCoprime (Ideal.span {prime.val}) I
  radical_cap : ∀ B : actualAllocations s.pools C,
    frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 →
    ∀ prime i χ, (x.family B prime i χ).modulus.absNorm ≤
      CenteredMomentAmplificationRadicalFamily.radicalBound
        (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime
        (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))
  moving_cap : ∀ B : actualAllocations s.pools C,
    frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 →
    ∀ prime i χ, ((x.family B prime i χ).modulus.absNorm : ℝ) ≤
      cost*(τ.modulus.absNorm : ℝ)*Z^(errorMoving prime Z (errorIndex i+1))
  radius_inv : ∀ (prime : elementPool P) i,
    (errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s)))
      (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve prime (errorIndex i+1))⁻¹ ≤ Z^Dscale
  conductor_cap : ∀ B : actualAllocations s.pools C,
    frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 →
    ∀ prime i χ, ((x.family B prime i χ).modulus.absNorm : ℝ) ≤ Z^qmoving
end ExtractedErrorRun

theorem actual_first_allocated_extracted_error_sum
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
    (hCrfirst : 0 < Crfirst) (hallocSmall : εalloc*Bfirst ≤ 1/10000):
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
    ∀ (R seedOuter seed : Ideal O), R ≠ 0 →
    Squarefree seedOuter → seedOuter ≠ 0 → Squarefree seed → seed ≠ 0 →
    (seed.absNorm : ℝ) ≤ Z^Bseed →
    src.W₁ 0=0 → src.W₂ 0=0 → volume src≤ Z^Avol → (R.absNorm : ℝ)≤ Z^Pmask →
    0 < sourceRadius src → sourceRadius src ≤ Z^Bfirst →
    ∀ profile : Profiles a b, profile.profile 0=src.W₁ → profile.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀ (m A : O) (t₀ : ℝ) (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
      (K a₁ a₂ win delta reserve asource : ℝ),
    0 < K → 0 < a₁ → 0 < a₂ → 0 < asource →
    0 ≤ delta → 0 ≤ reserve → a0 ≤ asource →
    (∀ y, src.W₁ y ≠ 0 → a₁ ≤ y) → (∀ y, src.W₂ y ≠ 0 → a₂ ≤ y) →
    (∀ i y, V i y ≠ 0 → |y| ≤ win) →
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
    ∀ (ξ₁ ξ₂ : RayCharacter) (F : Families src R seedOuter ξ₁ ξ₂),
    ∀ left : (p : Labels src R seedOuter) → (E : Finset (CommonIndex p.val.1 p.val.2)) →
      Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (sourceRadius src/p.val.1.absNorm) (sourceRadius src/p.val.2.absNorm) →
      ExtractedErrorRun src p.val.1 P,
    ∀ right : (p : Labels src R seedOuter) → (E : Finset (CommonIndex p.val.1 p.val.2)) →
      Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (sourceRadius src/p.val.1.absNorm) (sourceRadius src/p.val.2.absNorm) →
      ExtractedErrorRun src p.val.2 P,
    (∀ (p : Labels src R seedOuter) (E : Finset (CommonIndex p.val.1 p.val.2)),
      E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2 → ∀ n,
      (left p E n).Admissible p.val.2 R E (F p E).left Z K sigma delta reserve cost Dscale qmoving Bfirst heightCap ∧
      (right p E n).Admissible p.val.1 R (swapSubset p.val.1 p.val.2 E) (F p E).right
        Z K sigma delta reserve cost Dscale qmoving Bfirst heightCap) →
    (∑ p : Labels src R seedOuter,
      ∑ E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
      ∑ n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (sourceRadius src/p.val.1.absNorm) (sourceRadius src/p.val.2.absNorm),
        allowanceWeight src R seedOuter m A t₀ W V K (radius p E) Z p E (F p E).left (F p E).right n *
          (Real.sqrt ((left p E n).normalizedValue N p.val.2 R seed E (F p E).left upper Z K sigma delta reserve)*
           Real.sqrt ((right p E n).normalizedValue N p.val.1 R seed
             (swapSubset p.val.1 p.val.2 E) (F p E).right upper Z K sigma delta reserve))) ≤
    Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2*
      ((Real.exp win/((∏i,src.lo i)*a₁*a₂))*fixedPresentationCost*K*(src.η.modulus.absNorm : ℝ))*
      Z^(-3/10000 : ℝ)/((seedOuter.absNorm : ℝ)*(seed.absNorm : ℝ)) := by
  obtain ⟨Calloc,hCalloc,Uprofile,Jheight,hactual⟩ := actual_allocated_extracted_errors_uniform (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ Sbad hbad sigma cost hsigma hξsmall hcost hsigma_eq
    Avol Dscale Pmask qmoving εgeo hεgeo hbudget εalloc hεalloc hloss hsaving
  obtain ⟨Cweight,hCweight,hweight⟩ := original_fixed_allowance_weight_sum
    Bfirst Lfirst Crfirst (1/10000) hBfirst hLfirst hCrfirst (by norm_num)
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Calloc*Cbound*Cweight,mul_pos (mul_pos hCalloc hCbound) hCweight,?_⟩
  filter_upwards [hactualZ,hweight] with Z hZ hweight
  refine ⟨hZ.1,?_⟩
  intro Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    R seedOuter seed hR hseedOuter hseedOuter0 hseed hseed0 hseedcap
    hzero1 hzero2 hvolumeCap hmaskCap hH hHcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    m A t₀ W V K a₁ a₂ win delta reserve asource hK ha₁ ha₂ hasource hdelta hreserve haSource
    hs₁ hs₂ hwin
  dsimp only
  intro hP Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
    Mgeom Mvolume heightCap hgeom hheightCap hplainX₁ hplainX₂ hplainY₁ hplainY₂
    hwidth hvolGeom hvolCap hfixed hdef hpaid hfrequency hepsSmall radius hr ξ₁ ξ₂ F left right hruns
  let bound := Calloc*Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2*
    Z^(-1/2500 : ℝ)/(seed.absNorm : ℝ)
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  have hbound : 0 ≤ bound := by dsimp [bound]; positivity
  have hsingle (C D : Ideal O) (hC : Supported C) (hD : Supported D)
      (hCD : primeSupport C=primeSupport D) (E : Finset (CommonIndex C D)) (τ : Character)
      (hmod : τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
        Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E*activeConductor C D})
      (x : ExtractedErrorRun src C (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
      (hx : x.Admissible D R E τ Z K sigma delta reserve cost Dscale qmoving Bfirst heightCap) :
      x.normalizedValue N D R seed E τ upper Z K sigma delta reserve ≤ bound := by
    exact hZ.2 Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
      C D R hC hD hCD E τ x.height hmod K delta reserve asource hK hasource hdelta hreserve haSource
      hP hx.slot_coprime x.family hx.radical_cap hx.moving_cap
      hzero1 hzero2 hvolumeCap hmaskCap hR hx.radius_inv hx.conductor_cap
      seed hseed hseed0 hseedcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂
      hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
      Bfirst heightCap hheightCap hx.height_le hx.common_cap hallocSmall hpaid hfrequency hepsSmall
  have hpair (p : Labels src R seedOuter) (E : Finset (CommonIndex p.val.1 p.val.2))
      (hE : E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2)
      (n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (sourceRadius src/p.val.1.absNorm) (sourceRadius src/p.val.2.absNorm)) :
      Real.sqrt ((left p E n).normalizedValue N p.val.2 R seed E (F p E).left upper Z K sigma delta reserve)*
        Real.sqrt ((right p E n).normalizedValue N p.val.1 R seed
          (swapSubset p.val.1 p.val.2 E) (F p E).right upper Z K sigma delta reserve) ≤ bound := by
    have hp := commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset src.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient src R seedOuter)) _ _ p.property
    have hCD := first_label_equal_support src R seedOuter p
    obtain ⟨hl,hr⟩ := hruns p E hE n
    have hleft := hsingle p.val.1 p.val.2 hp.1 hp.2 hCD E (F p E).left
      (F p E).left_modulus (left p E n) hl
    have hright := hsingle p.val.2 p.val.1 hp.2 hp.1 hCD.symm (swapSubset p.val.1 p.val.2 E)
      (F p E).right (right_modulus src.η p.val.1 p.val.2 hp.1 E ξ₁ ξ₂ (F p E)) (right p E n) hr
    exact (mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt hbound)
  have hw := hweight Aorig src R seedOuter hseedOuter hseedOuter0 hzero1 hzero2 hH hHcap
    m A t₀ W V K a₁ a₂ win hK ha₁ ha₂ hs₁ hs₂ hwin radius hr ξ₁ ξ₂ F
  calc
    _ ≤ bound*sumAllowanceWeight src R seedOuter m A t₀ W V K Z radius
        (fun p E => (F p E).left) (fun p E => (F p E).right) := by
      unfold sumAllowanceWeight
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro E hE
      apply Finset.sum_le_sum
      intro n _
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hpair p E hE n)
        (allowanceWeight_nonneg src R seedOuter m A t₀ W V K (radius p E) Z hz.le
          p E (F p E).left (F p E).right n)
    _ ≤ bound*(((Real.exp win/((∏i,src.lo i)*a₁*a₂))*fixedPresentationCost*K*(src.η.modulus.absNorm : ℝ))*
        (Cweight*Z^(1/10000 : ℝ)/(seedOuter.absNorm : ℝ))) := mul_le_mul_of_nonneg_left hw hbound
    _ = _ := by
      have hpow : Z^(-1/2500 : ℝ)*Z^(1/10000 : ℝ)=Z^(-3/10000 : ℝ) := by
        rw [←Real.rpow_add hz]
        norm_num
      dsimp only [bound]
      calc
        _ = (Calloc*Cbound*Cweight)*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2*
          ((Real.exp win/((∏i,src.lo i)*a₁*a₂))*fixedPresentationCost*K*(src.η.modulus.absNorm : ℝ))*
          (Z^(-1/2500 : ℝ)*Z^(1/10000 : ℝ))/((seedOuter.absNorm : ℝ)*(seed.absNorm : ℝ)) := by ring
        _ = _ := by rw [hpow]

#print axioms actual_first_allocated_extracted_error_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualFirstExtractedErrors -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalKernel ; sha256 e2349dbb33c32c2eaab522b943fc8e08ad168e2f398a381990ad1c8f4408337b -/
section




/-! The counted coherent exceptional amplitudes pass through both Mellin
windows and the whole second Fourier kernel, without truncating heights. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
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
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSectorLocalization
open CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentChildRows
open CenteredMomentFixedQForcingCount CenteredMomentForcing CenteredMomentRankinRadical
open RayFourExpansion UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local instance coherentExceptionalKernelDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _


def coherentProjectorKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁) (hseed : seed ∣ C₁)
    (p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁))
    (η : Character) (U : Finset (CommonIndex p.val.1 p.val.2))
    (L : Ideal O) (χL χR : RayCharacter) : CommonSecondKernelLabel ι where
  input := src
  puncture := R
  seed := seed
  firstCommon := C₁
  firstProjector := L₁
  hfirst := hC₁
  hseed := hseed
  parent := η
  second := p
  partition := U
  projector := L
  leftRay := χL
  rightRay := χR⁻¹

lemma coherentProjectorKernel_values {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁) (hseed : seed ∣ C₁)
    (p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁))
    (η : Character) (U : Finset (CommonIndex p.val.1 p.val.2))
    (χL χR : RayCharacter) (vL vR HL HR : ℝ) (Ds : Finset (Ideal O)) (rows : Finset O) :
    (∑ k ∈ Ds ×ˢ rows, ‖(moebius k.1 : ℂ)‖ *
      ‖(coherentProjectorKernel src R seed C₁ L₁ hC₁ hseed p η U k.1 χL χR).toKernelLabel.leftValue vL k.2 HL‖ *
      ‖(coherentProjectorKernel src R seed C₁ L₁ hC₁ hseed p η U k.1 χL χR).toKernelLabel.rightValue vR k.2 HR‖) =
      commonSecondValuePair src R seed C₁ L₁ hC₁ p η U χL χR vL vR HL HR Ds rows := by
  simp only [Finset.sum_product,coherentProjectorKernel,CommonSecondKernelLabel.toKernelLabel,
    SecondKernelLabel.leftValue,SecondKernelLabel.rightValue,SecondKernelLabel.frequency,
    inv_inv,secondChildValue_active,commonSecondValuePair,Finset.mul_sum,mul_assoc]

lemma coherent_exceptional_shifted_profile
    {ι : Type*} [Fintype ι] [DecidableEq ι] {wlo whi : ℝ}
    (Sprofile : Finset (ℕ×ℕ)) (src : Input ι) (profile : Profiles wlo whi)
    (η ψ τ : Character) (t θ u v : ℝ) (J : ℕ) :
    profileMass Sprofile (withHeight src ψ (t+2*Real.pi*(u-θ))).toData
      (withHeight src τ (t+2*Real.pi*(v-(-θ)))).toData profile profile J ≤
    ((1+2*Real.pi)^(4*J)*profileMass Sprofile (withHeight src η t).toData
      (withHeight src η t).toData profile profile J*(1+‖θ‖)^(2*J))*(1+‖u‖)^J*(1+‖v‖)^J := by
  have hs := shifted_mass Sprofile src src ψ τ profile profile t t θ (-θ) u v J
  have hm := mass_phase Sprofile (withHeight src η t) (withHeight src η t) profile profile θ J
  have hm' : mass Sprofile src src profile profile t t θ (-θ) J ≤
      (1+2*Real.pi)^(4*J)*profileMass Sprofile (withHeight src η t).toData
        (withHeight src η t).toData profile profile J*(1+‖θ‖)^(2*J) := hm
  exact hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hm' (by positivity)) (by positivity))

theorem actual_coherent_exceptional_kernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi) (lo hi : ι → ℝ)
    (ε δ θ B Lbound : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ)
    (hB : 0 ≤ B) (hL : 0 ≤ Lbound) (W : 𝓢(ℝ,ℂ)) (decay : ℕ) :
    ∃ J : ℕ, ∃ Sprofile : Finset (ℕ×ℕ), (0,0) ∈ Sprofile ∧
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
    ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} → ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (src : Input ι) (profile : Profiles wlo whi),
    (∀ i, src.lo i = lo i) → (∀ i, src.hi i = hi i) → (∀ i, 1 ≤ src.P i) →
    src.W₁ = profile.profile 0 → src.W₂ = profile.profile 1 →
    ∀ (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁), R ≠ 0 → ∀ hseed : seed ∣ C₁,
    ∀ p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁),
    ∀ (η : Character) (U : Finset (CommonIndex p.val.1 p.val.2))
      (family : RayCharacter → Character),
    Family η p.val.1 p.val.2 (lowActiveLeftSupported p) (lowActiveRightSupported p) U family →
    ∀ (χL χR : RayCharacter) (t Kphys Radius r : ℝ) (n : Fin 4 → ℤ),
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
    (∑ L ∈ Ds, ∑ z ∈ rows,
      ‖(((1+SecondKernelLabel.kernelScale n)^decay : ℝ) : ℂ)*(moebius L : ℂ)*
        (coherentProjectorKernel src R seed C₁ L₁ hC₁ hseed p η U L χL χR).toKernelLabel.kernelRow
          t z W Kphys Radius n‖) ≤
      Ckernel*((volume src.toData/Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
        (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((rowExponent-4*Real.logb Z ((forcingIdeal (fun P : CommonIndex p.val.1 p.val.2 => P.val)
            (leftExponent p.val.1 p.val.2) (rightExponent p.val.1 p.val.2)
            (nonunitPartitionSet p.val.1 p.val.2 U)).absNorm : ℝ))/6+2*ε+δ-max (max (r-Real.logb Z ((C₁*p.val.1).absNorm : ℝ)) 0)
          (max (r-Real.logb Z ((C₁*p.val.2).absNorm : ℝ)) 0))*
          (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass Sprofile (withHeight src η t).toData
            (withHeight src η t).toData profile profile J*
              frozenProfile src*frozenProfile src/
                (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)))) := by
  obtain ⟨J,Sprofile,hSprofile,hbound⟩ := actual_coherent_exceptional_counted_values
    wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  obtain ⟨Ckernel,hCkernel,hkernel⟩ := joint_second_kernel_norm_sum_from_values W decay (2*J) J J
  refine ⟨J,Sprofile,hSprofile,Ckernel,hCkernel,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩ := hbound Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro src profile hlo hhi hP hW₁ hW₂ R seed C₁ L₁ hC₁ hR hseed
    p η U family hfamily χL χR t Kphys Radius r n hX₁ hX₂ hY₁ hY₂ hη m hm hml hm2
    rows hn hex Cr rowExponent hCr hN hcondL hcondR Ds hDs
  let F : ℝ := (volume src.toData/Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
      (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        Z^((rowExponent-4*Real.logb Z ((forcingIdeal (fun P : CommonIndex p.val.1 p.val.2 => P.val)
          (leftExponent p.val.1 p.val.2) (rightExponent p.val.1 p.val.2)
          (nonunitPartitionSet p.val.1 p.val.2 U)).absNorm : ℝ))/6+2*ε+δ-
          max (max (r-Real.logb Z ((C₁*p.val.1).absNorm : ℝ)) 0)
            (max (r-Real.logb Z ((C₁*p.val.2).absNorm : ℝ)) 0)) *
        (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)^θ*
        (frozenProfile src*frozenProfile src/(((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)))
  have hz := zero_lt_one.trans hZ.1
  have hF : 0 ≤ F := by
    have hV := (CenteredMomentExceptionalAmplitudePair.volume_pos src.toData).le
    have hfr := frozenProfile_nonneg src
    dsimp only [F]
    positivity
  have hv (φ u v : ℝ) :
      commonSecondValuePair src R seed C₁ L₁ hC₁ p η U χL χR
        (t+2*Real.pi*(u-φ)) (t+2*Real.pi*(v-(-φ)))
        (dyadicScale (n 2)) (dyadicScale (n 3)) Ds rows ≤
      (F*((1+2*Real.pi)^(4*J)*profileMass Sprofile (withHeight src η t).toData
        (withHeight src η t).toData profile profile J)*(1+‖φ‖)^(2*J))*(1+‖u‖)^J*(1+‖v‖)^J := by
    have hb := hZ.2 src profile hlo hhi hP hW₁ hW₂ R seed C₁ L₁ hC₁ hR hseed
      p η U family hfamily χL χR (t+2*Real.pi*(u-φ)) (t+2*Real.pi*(v-(-φ)))
      (dyadicScale (n 2)) (dyadicScale (n 3)) r (dyadicScale_pos _) (dyadicScale_pos _)
      hX₁ hX₂ hY₁ hY₂ hη m hm hml hm2 rows hn hex Cr rowExponent hCr hN hcondL hcondR Ds hDs
    have hs := coherent_exceptional_shifted_profile Sprofile src profile η (family χL)
      (reflected (family χR)) t φ u v J
    apply hb.trans
    calc
      _ = F*profileMass Sprofile (withHeight src (family χL) (t+2*Real.pi*(u-φ))).toData
          (withHeight src (reflected (family χR)) (t+2*Real.pi*(v-(-φ)))).toData profile profile J := by
        dsimp only [F]
        ring
      _ ≤ F*(((1+2*Real.pi)^(4*J)*profileMass Sprofile (withHeight src η t).toData
          (withHeight src η t).toData profile profile J*(1+‖φ‖)^(2*J))*(1+‖u‖)^J*(1+‖v‖)^J) :=
        mul_le_mul_of_nonneg_left hs hF
      _ = _ := by ring
  have hk := hkernel (Ds ×ˢ rows)
    (fun k => (coherentProjectorKernel src R seed C₁ L₁ hC₁ hseed p η U k.1 χL χR).toKernelLabel)
    (fun _ => t) (fun _ => Kphys) (fun _ => Radius) (fun _ => n) (fun k => k.2)
    (fun k => (moebius k.1 : ℂ))
    (F*((1+2*Real.pi)^(4*J)*profileMass Sprofile (withHeight src η t).toData
      (withHeight src η t).toData profile profile J)) (by
        intro φ u v
        rw [coherentProjectorKernel_values]
        exact hv φ u v)
  simp only [Finset.sum_product] at hk
  apply hk.trans_eq
  dsimp only [F]
  ring

#print axioms coherentProjectorKernel_values
#print axioms coherent_exceptional_shifted_profile
#print axioms actual_coherent_exceptional_kernel
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalKernel -/
