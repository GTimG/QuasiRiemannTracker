/- Asymmetric reserve and endpoint refinement: Zhongpai Gao, with AI assistance. Adapts Kari Roegnvaldsson’s affine/reserve source at 14ab1618c5133a7d12e06aa76661bbcb34e843cd, following accepted c707738a659786b9a44a79c629bed8c801cca8f3. Original notices below are retained. -/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B001
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B005
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B033
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B047
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B058
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B065
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B071
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B075
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B081
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B082
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B083
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B085
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B087
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B089
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B090
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGaussianDyad
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondBlockCount

/- BEGIN ORIGINAL MODULE Analytic.JointLowPairedValues ; sha256 bab9fb3f50276c249667c492c4dffe61a182e7e9710859e757eafe03c50d1a13 -/
section


/-! Finite Cauchy for the literal two second children. Both the reflected
row predicate and the selected cumulative common ideals remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst
open CenteredMomentActiveSource CenteredMomentSecondRetainedAggregate
open CenteredMomentRowNorm CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly RayFourExpansion
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentSecondMaskedWindow CenteredMomentSecondSectorEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonRadialSource
open CenteredMomentCommonHeightEnvelope CenteredMomentRadialEligibleEnergy
open CenteredMomentFirstAmplificationChoice CenteredMomentExceptionalAmplitudePair
open CenteredMomentCompleteCommon CenteredMomentSecondBlockAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
local notation "O" => HeckeFamily.O
local instance lowPairedValuesDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma second_value_volume_root (V HL HR EL ER : ℝ)
    (hV : 0 ≤ V) (hHL : 0 < HL) (hHR : 0 < HR) :
    Real.sqrt ((V/HL)*EL)*Real.sqrt ((V/HR)*ER) =
      (V/Real.sqrt (HL*HR))*(Real.sqrt EL*Real.sqrt ER) := by
  rw [Real.sqrt_mul (div_nonneg hV hHL.le),Real.sqrt_mul (div_nonneg hV hHR.le)]
  have hh : Real.sqrt (V/HL)*Real.sqrt (V/HR) = V/Real.sqrt (HL*HR) := by
    rw [←Real.sqrt_mul (div_nonneg hV hHL.le),
      show (V/HL)*(V/HR)=V^2/(HL*HR) by ring,
      Real.sqrt_div (sq_nonneg V),Real.sqrt_sq hV]
  calc
    _ = (Real.sqrt (V/HL)*Real.sqrt (V/HR))*(Real.sqrt EL*Real.sqrt ER) := by ring
    _ = _ := by rw [hh]

/-- The right radial source is tested at `-z`, with its own keep
predicate. Its common ideal is `C₁*D₂`; the same actual second family and
frequency generator are retained on both sides. -/
theorem actual_common_second_paired_values
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (src : Input ι) (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁)
    (p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁))
    (η : Character) (U : Finset (CommonIndex p.val.1 p.val.2))
    (family : RayCharacter → Character)
    (hfamily : Family η p.val.1 p.val.2 (lowActiveLeftSupported p) (lowActiveRightSupported p) U family)
    (χL χR : RayCharacter) (vL vR HL HR : ℝ) (hHL : 0 < HL) (hHR : 0 < HR)
    (L : Ideal O) (rL rR : Radial) (rows : Finset O)
    (hkeepL : ∀ z ∈ rows,rL.keep z) (hkeepR : ∀ z ∈ rows,rR.keep (-z))
    (hmajorL : ∀ z ∈ rows,1 ≤ (rL.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/rL.scale)).re)
    (hmajorR : ∀ z ∈ rows,1 ≤ (rR.profile (‖ConcreteTraceCRT.eisEmbedding (-z)‖^2/rR.scale)).re) :
    (∑ z ∈ rows,
      ‖secondChildValue η vL
        (commonSecondColumns (original src R seed) C₁ hC₁)
        (commonSecondBeta (original src R seed) C₁ L₁) p.val.1 (lowActiveLeftSupported p)
        (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)
        L χL z HL‖ *
      ‖secondChildValue η vR
        (commonSecondColumns (original src R seed) C₁ hC₁)
        (commonSecondBeta (original src R seed) C₁ L₁) p.val.2 (lowActiveRightSupported p)
        (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)
        L χR (-z) HR‖) ≤
      (volume src.toData/Real.sqrt (HL*HR))*
        (Real.sqrt (sourceEnergy (withHeight src (family χL) vL) rL (C₁*p.val.1)
          ((supported_mul_iff _ _).mpr ⟨hC₁,lowActiveLeftSupported p⟩) R seed L)*
         Real.sqrt (sourceEnergy (withHeight src (family χR) vR) rR (C₁*p.val.2)
          ((supported_mul_iff _ _).mpr ⟨hC₁,lowActiveRightSupported p⟩) R seed L)) := by
  have hleft := actual_common_second_left_l2 src R seed C₁ L₁ hC₁ p η U family hfamily
    χL vL HL hHL L rL rows hkeepL hmajorL
  have hright := actual_common_second_right_l2 src R seed C₁ L₁ hC₁ p η U family hfamily
    χR vR HR hHR L rR (rows.image (fun z : O => -z))
    (by intro y hy; obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy; exact hkeepR z hz)
    (by intro y hy; obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy; exact hmajorR z hz)
  rw [Finset.sum_image (fun x _ y _ hxy => neg_injective hxy)] at hright
  have hc := Real.sum_mul_le_sqrt_mul_sqrt rows
    (fun z => ‖secondChildValue η vL
      (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.1 (lowActiveLeftSupported p)
      (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) L χL z HL‖)
    (fun z => ‖secondChildValue η vR
      (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.2 (lowActiveRightSupported p)
      (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) L χR (-z) HR‖)
  apply hc.trans
  apply (mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq
  exact second_value_volume_root _ _ _ _ _ (volume_pos src.toData).le hHL hHR

#print axioms actual_common_second_paired_values
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowPairedValues -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSelectedCommonBinSource ; sha256 7b22056464ce3908cdd0b9500d92794cb56684eb20d2c30ffa8bb51510e915f1 -/
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
local instance selectedLowCommonBinSourceFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem actual_selected_second_low_source_of_common_bin
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
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → ∀ hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)},
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
        (F : FixedPair ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂),
      let u := firstSideDictionaryUnit ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F
      activeConductor P₁ Q₁ = (u : O)*∏ i,activePrimary P₁ Q₁ i ∧
      ∀ left : Bool, let parent := firstSideCharacter F left
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
      0 ≤ g → g ≤ 1/241 → 0 ≤ omegaLoss → 3/500 ≤ allowance →
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
      pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 1/2000000 →
      ∀ hne : physicalBlock parent t columns β C₂ D₂ hC₂ hD₂ U radius rows Wrad Kcut n ≠ 0,
      ∀ χ : RayCharacter,
      let s := actualState (τ := family) t columns β radius rows Wrad Kcut n hne Z Bmask hZ
        χ (internalQ Q η₀) 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hmask)
      ∀ (reflect : Bool) (low : O → Prop) (abin : ℝ) (k : ℕ),
      ∀ (holes : O → JointRelativeLabel ηfirst (Option (α × RayQuotient.Characters M H)) → Ideal O)
        (hholes : ∀ z label,holes z label ≠ 0),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : (supportedNaturalState s).radial.keep z, low z →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (holes z) (hholes z) abin (abin+e) (3*(k+1 : ℕ)*Z^τ)
          (secondReconstructedRow P₁ Q₁ hP₁ E₁ u C₂ D₂ hC₂ U left (lowSignedRow reflect z)
            (lowSignedRow_ne_zero reflect z (s.row_ne_zero z hz.1)))) →
      (∀ i, |v+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      sourceEnergy (withHeight src s.character v) (restrictedLowRadial s.radial low)
        (C₁*T) ((supported_mul_iff _ _).mpr ⟨hC₁,second_selected_supported hC₂ hD₂ hTpick⟩) Rmask seed Lproj ≤
        Cbound*((Rmask*(C₁*T)).radical.absNorm : ℝ)^εmask*profileCost src*diagonalControl s.radial.profile*
          (p.control S)^2*(1+|v|+height)^degree *
          Z^(δcommon+(nominal+allowance-1/48000))/(((C₁*T).absNorm : ℝ)*Lproj.absNorm) := by
  obtain ⟨degree,S,hmain⟩ := actual_selected_second_low_source M H hH W
    aslot bslot a b Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon ηfirst parentLoss hparentLoss
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hmain,eventually_actual_second_signed_low_gate (Slot := α) M H hH η₀ 2 ξconductor hξconductor,
    eventually_selected_low_state_width ηfirst parentLoss hparentLoss] with Z hmain hgate hwidth
  intro hZ θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ C₂ D₂ Rmask seed Lproj hC₁ hD₁ hC₂ hD₂ hCD₂
    E₁ ξ₁ ξ₂ F
  let u := firstSideDictionaryUnit ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F
  obtain ⟨hu,hgate⟩ := hgate.2 ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F
  refine ⟨hu,?_⟩
  intro left parent U family hfamily T hTpick hR hseed hLproj hCcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    c d₁ r₁ e₁ radius nominal pad hpad hMcapSource hconductorSource hbudgetSource hne χ s reflect low abin k holes hholes
    habin habinTop hbase hT hbin hfreqGate hheightSource
  have hparent : parent = F.left ∨ parent = F.right := by cases left <;> simp [parent,firstSideCharacter]
  have hswidth : s.width ≤ nominal+pad := hwidth hZ P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F parent hparent
    C₁ D₁ hC₁ C₂ D₂ hC₂ hD₂ U family hfamily t columns β rows Wrad Kcut n Hsource A Mparent omegaLoss ξ sourceLoss Bmask
    hKcut hHsource hmask hsource hne χ (internalQ Q η₀)
  have hlow : ∀ z, ∀ hz : (supportedNaturalState s).radial.keep z, low z →
      NaturalLowGate M H hH (supportedNaturalState s) η₀ Q hQM rfl d τ e abin k z hz := by
    intro z hz hl
    exact hgate left C₂ D₂ hC₂ hD₂ hCD₂ U family hfamily (Rmask*(C₁*T))
      (mul_ne_zero hR (mul_ne_zero hC₁.1 (second_selected_supported hC₂ hD₂ hTpick).1))
      (by rcases hTpick with rfl | rfl
          · exact Or.inl ((dvd_mul_left _ C₁).trans (dvd_mul_left _ Rmask))
          · exact Or.inr ((dvd_mul_left _ C₁).trans (dvd_mul_left _ Rmask))) χ Bmask d s rfl rfl
      (by linarith) Q hQM rfl hQ72 reflect z hz τ e abin k he (holes z) (hholes z) (hbin z hz hl)
  exact hmain hZ θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ C₂ D₂ Rmask seed Lproj hC₁ hD₁ hC₂ hD₂ hCD₂
    E₁ ξ₁ ξ₂ F parent hparent U family hfamily T hTpick hR hseed hLproj hCcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    hpad hMcapSource hbudgetSource hne χ low abin k habin habinTop hbase hT hlow hfreqGate hheightSource

#print axioms actual_selected_second_low_source_of_common_bin
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSelectedCommonBinSource -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceBins ; sha256 19036085bf14487e796dc12a3db8bacce88395c1f58efcd4b071737930476c93 -/
section



/-! The total common classifier partitions the actual retained physical
rows. Its exceptional class equals the source's existing exceptional
part, while the remaining classes are inserted only after the transform. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve ConcretePrimeRowBridge
open RayFourExpansion CenteredExceptionalProfile CenteredMomentChildRows
open CenteredMomentSecondEnergySplit CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondLiveBlock CenteredMomentSecondRetainedRows
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

namespace FirstSidePresentation
variable {η : Character} {Slot κ : Type*} [Fintype Slot]

def sourceBin (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (bin : NonzeroElement → Option κ) (z : O) : Option κ :=
  if hz : z ≠ 0 then bin (F.row s z hz) else none

theorem sourceBin_withProjector (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (bin : NonzeroElement → Option κ) (L : Ideal O) (z : O) :
    F.sourceBin (s.withProjector L) bin z = F.sourceBin s bin z := rfl

theorem sourceBin_none_iff (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (hs : s.parent = F.sourceParent) (bin : NonzeroElement → Option κ)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hbin : ∀ w, bin w = none ↔ FixedInducingRow η Q fixedBadMask 1 w.val)
    (χ : RayCharacter) (m z : O) (hm : m ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m) (hz : z ≠ 0) :
    F.sourceBin s bin z = none ↔
      FixedInducingRow (childCharacter s.parent χ) Q m s.toKernelLabel.frequency z := by
  rw [sourceBin,dif_pos hz,hbin]
  exact (F.inducing_iff s hs χ z hz Q hQ72 m hm hmLam hm2).symm

theorem partRows_true_eq_bin_none (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (hs : s.parent = F.sourceParent) (bin : NonzeroElement → Option κ)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hbin : ∀ w, bin w = none ↔ FixedInducingRow η Q fixedBadMask 1 w.val)
    (χ : RayCharacter) (m : O) (hm : m ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m) (R : ℝ) :
    partRows true s.parent χ Q m s.second.val.1 s.second.val.2 s.partition R =
      (sourceRows s.second.val.1 s.second.val.2 s.partition R).filter
        (fun z => F.sourceBin s bin z = none) := by
  ext z
  simp only [partRows,ite_true,Finset.mem_filter]
  constructor
  · rintro ⟨hz,he⟩
    exact ⟨hz,(F.sourceBin_none_iff s hs bin Q hQ72 hbin χ m z hm hmLam hm2
      (sourceRows_nonzero _ _ _ _ _ hz)).mpr he⟩
  · rintro ⟨hz,he⟩
    exact ⟨hz,(F.sourceBin_none_iff s hs bin Q hQ72 hbin χ m z hm hmLam hm2
      (sourceRows_nonzero _ _ _ _ _ hz)).mp he⟩

theorem partRows_false_eq_bin_some (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (hs : s.parent = F.sourceParent) (bin : NonzeroElement → Option κ)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hbin : ∀ w, bin w = none ↔ FixedInducingRow η Q fixedBadMask 1 w.val)
    (χ : RayCharacter) (m : O) (hm : m ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m) (R : ℝ) :
    partRows false s.parent χ Q m s.second.val.1 s.second.val.2 s.partition R =
      (sourceRows s.second.val.1 s.second.val.2 s.partition R).filter
        (fun z => F.sourceBin s bin z ≠ none) := by
  rw [partRows_false]
  ext z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz,he⟩
    exact ⟨hz,fun hb => he ((F.sourceBin_none_iff s hs bin Q hQ72 hbin χ m z hm hmLam hm2
      (sourceRows_nonzero _ _ _ _ _ hz)).mp hb)⟩
  · rintro ⟨hz,he⟩
    exact ⟨hz,fun hb => he ((F.sourceBin_none_iff s hs bin Q hQ72 hbin χ m z hm hmLam hm2
      (sourceRows_nonzero _ _ _ _ _ hz)).mpr hb)⟩

end FirstSidePresentation

theorem physicalBlock_complete_bin_partition {κ : Type*} [Fintype κ]
    (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
    (bin : O → Option κ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) :
    physicalBlock η t S β C D hC hD U R rows W K n =
      physicalBlock η t S β C D hC hD U R (rows.filter (fun z => bin z = none)) W K n +
      ∑ b : κ, physicalBlock η t S β C D hC hD U R
        (rows.filter (fun z => bin z = some b)) W K n := by
  unfold physicalBlock
  exact finite_row_option_bin_partition rows bin _

theorem actual_physicalBlock_exceptional_bin_partition {Slot κ : Type*}
    [Fintype Slot] [Fintype κ] {η : Character}
    (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (hs : s.parent = F.sourceParent) (bin : NonzeroElement → Option κ)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hbin : ∀ w, bin w = none ↔ FixedInducingRow η Q fixedBadMask 1 w.val)
    (χ : RayCharacter) (m : O) (hm : m ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (R : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) :
    physicalBlock s.parent t S β s.second.val.1 s.second.val.2
      s.toKernelLabel.hC s.toKernelLabel.hD s.partition R
      (sourceRows s.second.val.1 s.second.val.2 s.partition R) W K n =
    physicalBlock s.parent t S β s.second.val.1 s.second.val.2
      s.toKernelLabel.hC s.toKernelLabel.hD s.partition R
      (partRows true s.parent χ Q m s.second.val.1 s.second.val.2 s.partition R) W K n +
    ∑ b : κ, physicalBlock s.parent t S β s.second.val.1 s.second.val.2
      s.toKernelLabel.hC s.toKernelLabel.hD s.partition R
      ((sourceRows s.second.val.1 s.second.val.2 s.partition R).filter
        (fun z => F.sourceBin s bin z = some b)) W K n := by
  rw [F.partRows_true_eq_bin_none s hs bin Q hQ72 hbin χ m hm hmLam hm2 R]
  exact physicalBlock_complete_bin_partition _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem actual_retained_physicalBlock_exceptional_bin_partition {Slot κ : Type*}
    [Fintype Slot] [Fintype κ] {η : Character}
    (F : FirstSidePresentation η) (s : CommonSecondKernelLabel Slot)
    (hs : s.parent = F.sourceParent) (bin : NonzeroElement → Option κ)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hbin : ∀ w, bin w = none ↔ FixedInducingRow η Q fixedBadMask 1 w.val)
    (χ : RayCharacter) (m : O) (hm : m ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (R : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ) :
    physicalBlock s.parent t S β s.second.val.1 s.second.val.2
      s.toKernelLabel.hC s.toKernelLabel.hD s.partition R
      (retainedRows R s.toKernelLabel.frequency) W K n =
    physicalBlock s.parent t S β s.second.val.1 s.second.val.2
      s.toKernelLabel.hC s.toKernelLabel.hD s.partition R
      (partRows true s.parent χ Q m s.second.val.1 s.second.val.2 s.partition R) W K n +
    ∑ b : κ, physicalBlock s.parent t S β s.second.val.1 s.second.val.2
      s.toKernelLabel.hC s.toKernelLabel.hD s.partition R
      ((sourceRows s.second.val.1 s.second.val.2 s.partition R).filter
        (fun z => F.sourceBin s bin z = some b)) W K n := by
  exact (physicalBlock_live_rows s.parent t S β s.second.val.1 s.second.val.2
    s.toKernelLabel.hC s.toKernelLabel.hD s.partition R
    (retainedRows R s.toKernelLabel.frequency) W K n).trans
      (actual_physicalBlock_exceptional_bin_partition F s hs bin Q hQ72 hbin χ m hm hmLam hm2
        t S β R W K n)

#print axioms FirstSidePresentation.partRows_true_eq_bin_none
#print axioms FirstSidePresentation.partRows_false_eq_bin_some
#print axioms actual_physicalBlock_exceptional_bin_partition
#print axioms actual_retained_physicalBlock_exceptional_bin_partition
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceBins -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceCanonical ; sha256 b5075eae5a99fce5178997aa73d9971f42713e7b71abf0e1efe6aedc5b03edc5 -/
section



/-! Canonical fixed-parent rows and literal second kernel labels for the
injective active source domain. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeInverseAmplification
open ConcretePrimeRowBridge CenteredMomentCommonRadialData
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ActualEisensteinCubic
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationChildInput
open CenteredMomentCanonicalFirst CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentFixedRay RayFourExpansion CenteredMomentFirstPhysicalSource
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot]

namespace ActualJointSourceRow
variable {s : OriginalData Slot} {side : Bool}

def firstPresentation (q : ActualJointSourceRow s side) (η : Character)
    (ξ₁ ξ₂ : RayCharacter) : FirstSidePresentation η where
  C := q.first.val.1
  D := q.first.val.2
  supported := (commonLabels_supported (activeSource s.columns s.beta) _ _ q.first.property).1
  active := q.E
  leftRay := ξ₁
  rightRay := ξ₂
  pair := fixedPair η _ _ _ q.E ξ₁ ξ₂
  side := side

def unit (q : ActualJointSourceRow s side) (η : Character) (ξ₁ ξ₂ : RayCharacter) : Oˣ :=
  firstSideDictionaryUnit η q.first.val.1 q.first.val.2
    (q.firstPresentation η ξ₁ ξ₂).supported q.E ξ₁ ξ₂ (q.firstPresentation η ξ₁ ξ₂).pair

def reconstructed (q : ActualJointSourceRow s side) (η : Character) (ξ₁ ξ₂ : RayCharacter)
    (hz : q.z ≠ 0) : NonzeroElement :=
  secondReconstructedRow q.first.val.1 q.first.val.2
    (q.firstPresentation η ξ₁ ξ₂).supported q.E (q.unit η ξ₁ ξ₂)
    q.second.val.1 q.second.val.2
    (commonLabels_supported (activeSource _ _) _ _ q.second.property).1 q.U side q.z hz

theorem label_row (q : ActualJointSourceRow s side) (η : Character) (ξ₁ ξ₂ : RayCharacter)
    (hz : q.z ≠ 0) :
    q.label.row (q.unit η ξ₁ ξ₂) = (q.reconstructed η ξ₁ ξ₂ hz).val := by
  cases side
  · rw [label,if_neg Bool.false_ne_true,JointReconstructionLabel.swapFirst_row]
    rfl
  · rfl

theorem label_row_nonzero (q : ActualJointSourceRow s side) (η : Character)
    (ξ₁ ξ₂ : RayCharacter) (hz : q.z ≠ 0) : q.label.row (q.unit η ξ₁ ξ₂) ≠ 0 := by
  rw [q.label_row η ξ₁ ξ₂ hz]
  exact (q.reconstructed η ξ₁ ξ₂ hz).property

/-- The first-projector divisibilities follow from the nonzero second-source
columns; they are not independent support hypotheses on the joint label. -/
theorem label_projector_dvd (q : ActualJointSourceRow s side) :
    q.label.L ∣ q.label.C₂ ∧ q.label.L ∣ q.label.D₂ := by
  have hh := actual_second_common_first_projector s (sourceFirstCommon side q.first.val) q.L
    (sourceFirstCommon_supported s side q.first) q.second
  cases side <;> exact ⟨hh.1,hh.2.1⟩

theorem label_missing (q : ActualJointSourceRow s side) (w : O) :
    jointMissingRadical q.label.C₁ w = jointMissingRadical q.first.val.1 w := by
  cases side
  · exact q.baseLabel.swapFirst_missing w ((commonLabels_data _ _ _ _ q.first.property).2.2)
  · rfl

variable (input : Input Slot) (puncture seed : Ideal O)

theorem seed_dvd_first (q : ActualJointSourceRow (original input puncture seed) side)
    (hseed : Squarefree seed) (hz₁ : input.W₁ 0 = 0) (hz₂ : input.W₂ 0 = 0) :
    seed ∣ sourceFirstCommon side q.first.val := by
  have hh := CenteredMomentOriginalCommonHarmonic.actual_common_gates input puncture seed
    hseed hz₁ hz₂ q.first.val.1 q.first.val.2 q.first.property
  cases side
  · exact hh.2.2.2.2.1
  · exact hh.2.2.2.1

/-- Literal source data; second projectors and rays are still free extraction
indices, while their arithmetic labels are already fixed by q. -/
def kernelLabel (q : ActualJointSourceRow (original input puncture seed) side)
    (η : Character) (ξ₁ ξ₂ χ₁ χ₂ : RayCharacter) (projector : Ideal O)
    (hseed : seed ∣ sourceFirstCommon side q.first.val) : CommonSecondKernelLabel Slot where
  input := input
  puncture := puncture
  seed := seed
  firstCommon := sourceFirstCommon side q.first.val
  firstProjector := q.L
  hfirst := sourceFirstCommon_supported _ side q.first
  hseed := hseed
  parent := (q.firstPresentation η ξ₁ ξ₂).sourceParent
  second := q.second
  partition := q.U
  projector := projector
  leftRay := χ₁
  rightRay := χ₂

theorem kernelLabel_row (q : ActualJointSourceRow (original input puncture seed) side)
    (η : Character) (ξ₁ ξ₂ χ₁ χ₂ : RayCharacter) (projector : Ideal O)
    (hseed : seed ∣ sourceFirstCommon side q.first.val) (hz : q.z ≠ 0) :
    (q.firstPresentation η ξ₁ ξ₂).row
      (q.kernelLabel input puncture seed η ξ₁ ξ₂ χ₁ χ₂ projector hseed) q.z hz =
        q.reconstructed η ξ₁ ξ₂ hz := rfl

theorem kernelLabel_canonical_row (q : ActualJointSourceRow (original input puncture seed) side)
    (η : Character) (ξ₁ ξ₂ χ₁ χ₂ : RayCharacter) (projector : Ideal O)
    (hseed : seed ∣ sourceFirstCommon side q.first.val) (hz : q.z ≠ 0) :
    ((q.firstPresentation η ξ₁ ξ₂).row
      (q.kernelLabel input puncture seed η ξ₁ ξ₂ χ₁ χ₂ projector hseed) q.z hz).val =
        q.label.row (q.unit η ξ₁ ξ₂) := (q.label_row η ξ₁ ξ₂ hz).symm

end ActualJointSourceRow
#print axioms ActualJointSourceRow.label_row
#print axioms ActualJointSourceRow.label_projector_dvd
#print axioms ActualJointSourceRow.kernelLabel_canonical_row
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceCanonical -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceDyadicFibers ; sha256 77eed442936742d67f04105fe9db80576c40e09bffb8447830a0231c63eac137 -/
section





/-! Dyadic blocks are finite fibers over the actual joint arithmetic row,
not additional injective arithmetic labels. Their genuine source counts
are subpower, uniformly even when the second scales depend on the first block. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate
open CenteredMomentSourceRow CenteredMomentActiveSource CenteredMomentFirstSectors
local notation "O" => HeckeFamily.O

namespace ActualJointSourceRow
variable {Slot : Type*} [Fintype Slot] {s : OriginalData Slot} {side : Bool}

abbrev FirstDyadic (q : ActualJointSourceRow s side) (K R H : ℝ) :=
  CenteredMomentFirstPhysicalDyadicAssembly.Blocks
    (CenteredMomentFirstPhysicalDyadicAssembly.effectiveScale
      q.first.val.1 q.first.val.2 q.E K) R
    (H/(q.first.val.1.absNorm : ℝ)) (H/(q.first.val.2.absNorm : ℝ))

abbrev SecondDyadic (q : ActualJointSourceRow s side) (K R H : ℝ) :=
  SourceBlocks q.second.val.1 q.second.val.2 q.U K R H

abbrev DyadicFiber (q : ActualJointSourceRow s side) (K₁ R₁ H₁ : ℝ)
    (K₂ R₂ H₂ : FirstDyadic q K₁ R₁ H₁ → ℝ) :=
  (n₁ : FirstDyadic q K₁ R₁ H₁) × SecondDyadic q (K₂ n₁) (R₂ n₁) (H₂ n₁)

end ActualJointSourceRow

theorem actual_source_dyadic_card_subpower
    (B₁ L₁ Cr₁ B₂ L₂ Cr₂ ε : ℝ)
    (hB₁ : 0 ≤ B₁) (hL₁ : 0 ≤ L₁) (hCr₁ : 0 < Cr₁)
    (hB₂ : 0 ≤ B₂) (hL₂ : 0 ≤ L₂) (hCr₂ : 0 < Cr₂) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {Slot : Type*} [Fintype Slot] (s : OriginalData Slot) (side : Bool)
        (q : ActualJointSourceRow s side) (K₁ R₁ H₁ : ℝ),
      0 < K₁ → 0 < H₁ → R₁ ≤ Cr₁*Z^L₁ → H₁ ≤ Z^B₁ →
      ∀ K₂ R₂ H₂ : q.FirstDyadic K₁ R₁ H₁ → ℝ,
      (∀ n₁, 0 < K₂ n₁ ∧ R₂ n₁ ≤ Cr₂*Z^L₂ ∧ H₂ n₁ ≤ Z^B₂) →
      (Fintype.card (q.DyadicFiber K₁ R₁ H₁ K₂ R₂ H₂) : ℝ) ≤ C*Z^ε := by
  obtain ⟨C₁,hC₁,hfirst⟩ := CenteredMomentFirstPhysicalDyadicCount.original_blocks_subpower
    B₁ L₁ Cr₁ (ε/2) hB₁ hL₁ hCr₁ (by positivity)
  obtain ⟨C₂,hC₂,hsecond⟩ := CenteredMomentSecondBlockCount.sourceBlocks_subpower
    B₂ L₂ Cr₂ (ε/2) hB₂ hL₂ hCr₂ (by positivity)
  refine ⟨C₁*C₂,by positivity,?_⟩
  filter_upwards [hfirst,hsecond,eventually_gt_atTop (1 : ℝ)] with Z hf hs hZ
  refine ⟨hZ,?_⟩
  intro Slot inst s side q K₁ R₁ H₁ hK₁ hH₁ hR₁ hHcap₁ K₂ R₂ H₂ hgates
  have hfirstSupport := commonLabels_supported (activeSource s.columns s.beta)
    _ _ q.first.property
  have hsecondSupport := commonLabels_supported (activeSource _ _) _ _ q.second.property
  have hc₁ := hf q.first.val.1 q.first.val.2 hfirstSupport.1.1 hfirstSupport.2.1
    q.E K₁ R₁ H₁ hK₁ hH₁ hR₁ hHcap₁
  have hc₂ (n₁ : q.FirstDyadic K₁ R₁ H₁) := hs q.second.val.1 q.second.val.2
    hsecondSupport.1 hsecondSupport.2 q.U (K₂ n₁) (R₂ n₁) (H₂ n₁)
    (hgates n₁).1 (hgates n₁).2.1 (hgates n₁).2.2
  calc
    _ = ∑ n₁ : q.FirstDyadic K₁ R₁ H₁,
        (Fintype.card (q.SecondDyadic (K₂ n₁) (R₂ n₁) (H₂ n₁)) : ℝ) := by
      exact_mod_cast Fintype.card_sigma
        (ι := q.FirstDyadic K₁ R₁ H₁)
        (α := fun n₁ => q.SecondDyadic (K₂ n₁) (R₂ n₁) (H₂ n₁))
    _ ≤ ∑ _n₁ : q.FirstDyadic K₁ R₁ H₁, C₂*Z^(ε/2) :=
      Finset.sum_le_sum (fun n₁ _ => hc₂ n₁)
    _ = (Fintype.card (q.FirstDyadic K₁ R₁ H₁) : ℝ)*(C₂*Z^(ε/2)) := by simp
    _ ≤ (C₁*Z^(ε/2))*(C₂*Z^(ε/2)) :=
      mul_le_mul_of_nonneg_right hc₁ (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm,←Real.rpow_add (zero_lt_one.trans hZ)]
      congr 2
      ring

/-- Uniformly selecting one genuine dyadic fiber element is enough for the
joint high theorem. No cardinality hypothesis is supplied by the caller. -/
theorem actual_source_dyadic_sum_bound
    (B₁ L₁ Cr₁ B₂ L₂ Cr₂ ε : ℝ)
    (hB₁ : 0 ≤ B₁) (hL₁ : 0 ≤ L₁) (hCr₁ : 0 < Cr₁)
    (hB₂ : 0 ≤ B₂) (hL₂ : 0 ≤ L₂) (hCr₂ : 0 < Cr₂) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {α Slot : Type*} [Fintype Slot] (s : OriginalData Slot) (side : Bool)
        (labels : Finset α) (q : α → ActualJointSourceRow s side)
        (K₁ R₁ H₁ : α → ℝ),
      (∀ a ∈ labels, 0 < K₁ a ∧ 0 < H₁ a ∧ R₁ a ≤ Cr₁*Z^L₁ ∧ H₁ a ≤ Z^B₁) →
      ∀ K₂ R₂ H₂ : (a : α) → (q a).FirstDyadic (K₁ a) (R₁ a) (H₁ a) → ℝ,
      (∀ a ∈ labels, ∀ n₁, 0 < K₂ a n₁ ∧ R₂ a n₁ ≤ Cr₂*Z^L₂ ∧ H₂ a n₁ ≤ Z^B₂) →
      ∀ value : (a : α) → (q a).DyadicFiber (K₁ a) (R₁ a) (H₁ a) (K₂ a) (R₂ a) (H₂ a) → ℝ,
      (∀ a ∈ labels, ∀ n, 0 ≤ value a n) →
      ∀ E : ℝ,
      (∀ S : Finset α, S ⊆ labels →
        ∀ pick : (a : S) → (q a).DyadicFiber (K₁ a) (R₁ a) (H₁ a) (K₂ a) (R₂ a) (H₂ a),
        (∑ a : S, value a (pick a)) ≤ E) →
      (∑ a ∈ labels, ∑ n₁ : (q a).FirstDyadic (K₁ a) (R₁ a) (H₁ a),
        ∑ n₂ : (q a).SecondDyadic (K₂ a n₁) (R₂ a n₁) (H₂ a n₁),
          value a ⟨n₁,n₂⟩) ≤ (C*Z^ε)*E := by
  obtain ⟨C,hC,hcount⟩ := actual_source_dyadic_card_subpower B₁ L₁ Cr₁ B₂ L₂ Cr₂ ε
    hB₁ hL₁ hCr₁ hB₂ hL₂ hCr₂ hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α Slot inst s side labels q K₁ R₁ H₁ hfirst K₂ R₂ H₂ hsecond value hvalue E hchoice
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  let fiber (a : α) : Finset ((q a).DyadicFiber (K₁ a) (R₁ a) (H₁ a) (K₂ a) (R₂ a) (H₂ a)) :=
    Finset.univ
  have hmass (a : α) (ha : a ∈ labels) :
      (∑ _n ∈ fiber a, (1 : ℝ)) ≤ C*Z^ε := by
    simpa only [fiber,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using
      hZ.2 s side (q a) (K₁ a) (R₁ a) (H₁ a)
        (hfirst a ha).1 (hfirst a ha).2.1 (hfirst a ha).2.2.1 (hfirst a ha).2.2.2
        (K₂ a) (R₂ a) (H₂ a) (hsecond a ha)
  have hb := joint_weighted_fibers labels fiber (fun _ _ => 1) value (C*Z^ε) E
    (by positivity) (fun _ _ _ _ => by norm_num)
    (fun a ha n _ => hvalue a ha n) hmass
    (fun S hS pick _ => hchoice S hS pick)
  simpa only [fiber,one_mul,Fintype.sum_sigma] using hb

/-- A literal support or bin indicator stays on its dyadic fiber. The
maximizer therefore inherits the actual source gates on that fiber. -/
theorem actual_source_live_dyadic_sum_bound
    (B₁ L₁ Cr₁ B₂ L₂ Cr₂ ε : ℝ)
    (hB₁ : 0 ≤ B₁) (hL₁ : 0 ≤ L₁) (hCr₁ : 0 < Cr₁)
    (hB₂ : 0 ≤ B₂) (hL₂ : 0 ≤ L₂) (hCr₂ : 0 < Cr₂) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ {α Slot : Type*} [Fintype Slot] (s : OriginalData Slot) (side : Bool)
        (labels : Finset α) (q : α → ActualJointSourceRow s side)
        (K₁ R₁ H₁ : α → ℝ),
      (∀ a ∈ labels, 0 < K₁ a ∧ 0 < H₁ a ∧ R₁ a ≤ Cr₁*Z^L₁ ∧ H₁ a ≤ Z^B₁) →
      ∀ K₂ R₂ H₂ : (a : α) → (q a).FirstDyadic (K₁ a) (R₁ a) (H₁ a) → ℝ,
      (∀ a ∈ labels, ∀ n₁, 0 < K₂ a n₁ ∧ R₂ a n₁ ≤ Cr₂*Z^L₂ ∧ H₂ a n₁ ≤ Z^B₂) →
      ∀ (good : (a : α) → (q a).DyadicFiber (K₁ a) (R₁ a) (H₁ a) (K₂ a) (R₂ a) (H₂ a) → Prop)
        (value : (a : α) → (q a).DyadicFiber (K₁ a) (R₁ a) (H₁ a) (K₂ a) (R₂ a) (H₂ a) → ℝ),
      (∀ a ∈ labels, ∀ n, good a n → 0 ≤ value a n) →
      ∀ E : ℝ,
      (∀ S : Finset α, S ⊆ labels →
        ∀ pick : (a : S) → (q a).DyadicFiber (K₁ a) (R₁ a) (H₁ a) (K₂ a) (R₂ a) (H₂ a),
        (∀ a : S, good a (pick a)) → (∑ a : S, value a (pick a)) ≤ E) →
      (∑ a ∈ labels, ∑ n₁ : (q a).FirstDyadic (K₁ a) (R₁ a) (H₁ a),
        ∑ n₂ : (q a).SecondDyadic (K₂ a n₁) (R₂ a n₁) (H₂ a n₁),
          if good a ⟨n₁,n₂⟩ then value a ⟨n₁,n₂⟩ else 0) ≤ (C*Z^ε)*E := by
  obtain ⟨C,hC,hcount⟩ := actual_source_dyadic_card_subpower B₁ L₁ Cr₁ B₂ L₂ Cr₂ ε
    hB₁ hL₁ hCr₁ hB₂ hL₂ hCr₂ hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α Slot inst s side labels q K₁ R₁ H₁ hfirst K₂ R₂ H₂ hsecond good value hvalue E hchoice
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  let fiber (a : α) : Finset ((q a).DyadicFiber (K₁ a) (R₁ a) (H₁ a) (K₂ a) (R₂ a) (H₂ a)) :=
    Finset.univ.filter (good a)
  have hmass (a : α) (ha : a ∈ labels) :
      (∑ _n ∈ fiber a, (1 : ℝ)) ≤ C*Z^ε := by
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    apply (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))).trans
    simpa only [Finset.card_univ] using hZ.2 s side (q a) (K₁ a) (R₁ a) (H₁ a)
      (hfirst a ha).1 (hfirst a ha).2.1 (hfirst a ha).2.2.1 (hfirst a ha).2.2.2
      (K₂ a) (R₂ a) (H₂ a) (hsecond a ha)
  have hb := joint_weighted_fibers labels fiber (fun _ _ => 1) value (C*Z^ε) E
    (by positivity) (fun _ _ _ _ => by norm_num)
    (fun a ha n hn => hvalue a ha n (Finset.mem_filter.mp hn).2) hmass
    (fun S hS pick hpick => hchoice S hS pick
      (fun a => (Finset.mem_filter.mp (hpick a)).2))
  simpa only [fiber,one_mul,Finset.sum_filter,Fintype.sum_sigma] using hb

#print axioms actual_source_dyadic_card_subpower
#print axioms actual_source_dyadic_sum_bound
#print axioms actual_source_live_dyadic_sum_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceDyadicFibers -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowGaussianDyad ; sha256 c46b50688778da0a2e18fd1ffb46ed657409901f90418765f3b6cd0b1e454ff0 -/
section




/-! Adapted from OpenAI/math family003, pinned original module Detector.LowGaussianDyad.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory
namespace LowProbe
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowCommonDyad {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R : ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) : ℂ :=
  ∫t : ℝ,(∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
    compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
      selectedSlotFactor W Yp (fun i=>(p i).val) J t)*gaussianJointDensity V hV (U/R) t

lemma lowCommonDyad_eq_family {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R : ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) :
    lowCommonDyad η C W0 W1 slots W Yp J X Y U R V hV=
    gaussianPhysicalFamilyIntegral η C W0 W1 (Finset.univ : Finset (∀i,slots i))
      (fun p=> compensationSubsetWeight η W Yp (fun i=>(p i).val) J)
      (fun p=> Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
      (fun p=> X/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=> Y/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=> W i.val)
      (fun p i=> elementNorm (p i.val).val/Yp i.val) V hV U R := rfl

lemma lowCommonDyad_norm_of_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R B : ℝ) (degree : ℕ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ))
    (hb : ∀t : ℝ,‖∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
      compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
        selectedSlotFactor W Yp (fun i=>(p i).val) J t‖≤ B*(1+‖t‖)^degree) :
    ‖lowCommonDyad η C W0 W1 slots W Yp J X Y U R V hV‖≤
      B*gaussianJointMoment V hV degree (U/R) := by
  let f := fun t : ℝ=>(∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
      compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
        selectedSlotFactor W Yp (fun i=>(p i).val) J t)*gaussianJointDensity V hV (U/R) t
  have hi := (JointLogSeparation.weighted_schwartz_integrable (gaussianJointDensity V hV (U/R)) degree).const_mul B
  have hmajor (t : ℝ) : ‖f t‖≤ B*((1+‖t‖)^degree*‖gaussianJointDensity V hV (U/R) t‖) := by
    dsimp only [f]
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hb t)
      (norm_nonneg (gaussianJointDensity V hV (U/R) t))
  have hh := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hmajor)
  simpa only [f,lowCommonDyad,gaussianJointMoment,integral_const_mul] using hh

theorem low_central_gaussian_dyad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Submission20261012.Global.ell)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hM : 0≤ M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤ M) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(U : ℝ),0< U→
      Z^(1+lowSelectedLength ell J-ε/2)≤ U→U≤ Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
    ∀(V : SchwartzMap ℝ ℂ)(hV : HasCompactSupport (V:ℝ→ℂ)),
      ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
        W (fun i=> Z^(ell i)) J (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) U
          (Z^(1+lowSelectedLength ell J)) V hV‖≤
        C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+254*ε)*gaussianJointMoment V hV degree (U/Z^(1+lowSelectedLength ell J)) := by
  obtain ⟨degree,C,hC,he⟩ := low_central_compensated_tuple η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J U hU hlo hhi W hW V hV
  apply lowCommonDyad_norm_of_bound
  intro t
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hZ.2 T hT hout hdis hnorm J U hU hlo hhi W hW t

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowGaussianDyad -/
