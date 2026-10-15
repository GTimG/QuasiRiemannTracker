/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B001
import Submissions.reserve_local_20261013.Bundles.B029
import Submissions.reserve_local_20261013.Bundles.B043
import Submissions.reserve_local_20261013.Bundles.B075
import Submissions.reserve_local_20261013.Bundles.B096
import Submissions.reserve_local_20261013.Bundles.B102
import Submissions.reserve_local_20261013.Bundles.B103
import Submissions.reserve_local_20261013.Bundles.B104
import Submissions.reserve_local_20261013.Bundles.B106

/- BEGIN ORIGINAL MODULE Analytic.JointFirstSecondFibers ; sha256 81d52279e76c8e1f413b639a5e2c01608544b098c8f9860913fcdcc7320d7df3 -/
section


/-! Canonical recovery of the actual first source index from an arithmetic
row, the two first rays, and its first dyadic block. The second block scales
therefore depend only on the first fiber index, as required by the high
source theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentCanonicalFirst CenteredMomentSecondPhysicalBlock
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualFirstSecondSource
variable {src : Input ι} {R seed : Ideal O} {Kfirst : ℝ}
  {radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ}

abbrev FirstCoordinate := (Ideal O × Ideal O) × Finset (Ideal O) × Ideal O ×
  RayCharacter × RayCharacter × (Fin 4 → ℤ)

def firstKey (k : First src R seed Kfirst radius) : FirstCoordinate :=
  (k.1.1.val,k.1.2.1.val.image Subtype.val,k.2.1.val,k.2.2.1,k.2.2.2,fun j => (k.1.2.2 j : ℤ))

theorem firstKey_injective : Function.Injective
    (firstKey (src := src) (R := R) (seed := seed) (Kfirst := Kfirst) (radius := radius)) := by
  rintro ⟨⟨p,E,n⟩,L,χ,ξ⟩ ⟨⟨p',E',n'⟩,L',χ',ξ'⟩ he
  have hp : p=p' := Subtype.ext (congrArg (fun k => k.1) he)
  subst p'
  have hE : E=E' := Subtype.ext
    (Finset.image_injective Subtype.val_injective (congrArg (fun k => k.2.1) he))
  subst E'
  have hn : n=n' := funext (fun j => Subtype.ext (congrFun (congrArg (fun k => k.2.2.2.2.2) he) j))
  subst n'
  have hL : L=L' := Subtype.ext (congrArg (fun k => k.2.2.1) he)
  subst L'
  have hχ : χ=χ' := congrArg (fun k => k.2.2.2.1) he
  subst χ'
  have hξ : ξ=ξ' := congrArg (fun k => k.2.2.2.2.1) he
  subst ξ'
  rfl

def recoverFirst (fallback : First src R seed Kfirst radius) : FirstCoordinate → First src R seed Kfirst radius :=
  Function.extend firstKey id (fun _ => fallback)

@[simp] theorem recoverFirst_key (fallback k : First src R seed Kfirst radius) :
    recoverFirst fallback (firstKey k) = k := firstKey_injective.extend_apply id (fun _ => fallback) k

def firstAt (fallback : First src R seed Kfirst radius) {side : Bool}
    (q : ActualJointSourceRow (original src R seed) side) (χ ξ : RayCharacter)
    (n : q.FirstDyadic Kfirst (radius q.first q.E) (sourceRadius src)) : First src R seed Kfirst radius :=
  recoverFirst fallback (q.first.val,q.E.image Subtype.val,q.L,χ,ξ,fun j => (n j : ℤ))

variable {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

@[simp] theorem firstAt_packet (fallback : First src R seed Kfirst radius)
    (x : Packet src R seed Kfirst radius side K Radius H) :
    firstAt fallback (row x) x.1.2.2.1 x.1.2.2.2 x.1.1.2.2 = x.1 := by
  exact recoverFirst_key fallback x.1

def secondScale (fallback : First src R seed Kfirst radius)
    (K : First src R seed Kfirst radius → ℝ) (χ ξ : RayCharacter)
    (q : ActualJointSourceRow (original src R seed) side)
    (n : q.FirstDyadic Kfirst (radius q.first q.E) (sourceRadius src)) : ℝ :=
  K (firstAt fallback q χ ξ n)

def packetFiber (fallback : First src R seed Kfirst radius)
    (x : Packet src R seed Kfirst radius side K Radius H) :
    (row x).DyadicFiber Kfirst (radius (row x).first (row x).E) (sourceRadius src)
      (secondScale fallback K x.1.2.2.1 x.1.2.2.2 (row x))
      (secondScale fallback Radius x.1.2.2.1 x.1.2.2.2 (row x))
      (secondScale fallback H x.1.2.2.1 x.1.2.2.2 (row x)) :=
  ⟨x.1.1.2.2,fun j => ⟨(x.2.1.2 j : ℤ),by
    simp only [secondScale,firstAt_packet]
    exact (x.2.1.2 j).property⟩⟩

@[simp] theorem packetFiber_first (fallback : First src R seed Kfirst radius)
    (x : Packet src R seed Kfirst radius side K Radius H) :
    (packetFiber fallback x).1 = x.1.1.2.2 := rfl

@[simp] theorem packetFiber_second_val (fallback : First src R seed Kfirst radius)
    (x : Packet src R seed Kfirst radius side K Radius H) (j : Fin 4) :
    ((packetFiber fallback x).2 j : ℤ) = (x.2.1.2 j : ℤ) := rfl

end ActualFirstSecondSource
#print axioms ActualFirstSecondSource.firstKey_injective
#print axioms ActualFirstSecondSource.firstAt_packet
#print axioms ActualFirstSecondSource.packetFiber_second_val
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstSecondFibers -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSelectedSeededSource ; sha256 ba2e38a56c27fdf8050303ba7ea51791b0964777362a5bba484ae74a06202857 -/
section



/-! The actual original-volume low contribution with all Fourier frequency
and bin-height gates derived from the original source height. The finite
bin count is chosen before the eventual threshold. -/
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
local instance selectedLowSeededSourceFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

open CenteredMomentOriginalCommonHarmonic
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
open CenteredMomentSecondBlockHarmonicMass
theorem actual_selected_common_low_original_source
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
    ∀ (I : ℕ) (Wkernel : 𝓢(ℝ,ℂ)) (ν tailRows tailV lower tailSaving upper bplain₁ bplain₂ BRmask : ℝ)
      (Sbad : Finset (Ideal O)) (primeLoss Bsource Lrad Cr εsum : ℝ),
      0 < ν → ν < τ → 2*τ < d*ηheight → 0 ≤ tailRows → 0 < primeLoss → 0 ≤ Bsource → Bsource ≤ Bcommon →
      0 ≤ Lrad → 0 < Cr → 0 < εsum → Lrad+1 ≤ tailRows →
    ∃ (Nkernel : ℕ) (Ckernel Csum : ℝ), 0 ≤ Ckernel ∧ 0 < Csum ∧
    ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      ∀ hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)},
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) → (∀ i,lo ≤ σ i) → (∀ i,σ i ≤ hi) →
      0 ≤ height → (∀ i,|freq i| ≤ height) →
      ∀ (p : Profiles a b) (src : Input α), Matches M H hH src η₀ θ w σ freq W bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      p.profile 0 = src.W₁ → p.profile 1 = src.W₂ →
      (∀ i,src.lo i = loInput i) → (∀ i,src.hi i = hiInput i) →
      src.X₁ ≤ Z^L → src.X₂ ≤ Z^L → src.Y₁ ≤ Z^L → src.Y₂ ≤ Z^L →
      ∀ (P₁ Q₁ : Ideal O) (hP₁ : Supported P₁),
      ∀ (C₁ D₁ Rmask seed Lfirst : Ideal O) (hC₁ : Supported C₁) (hD₁ : D₁ ≠ 0)
        (E₁ : Finset (CommonIndex P₁ Q₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂) (left : Bool),
      Rmask ≠ 0 → Squarefree Lfirst → ∀ hseed : seed ∣ C₁,
      ∀ (t Hsource A volumeLoss Mparent g omegaLoss ξ sourceLoss profileLoss clip : ℝ),
      0 < Hsource → sourceRadius src ≤ Hsource → Real.logb Z Hsource ≤ A+sourceLoss →
      A+(7/2)*(∑ i,w i) ≤ Mparent+g → Real.logb Z (volume src.toData) ≤ A →
      A-volumeLoss ≤ Real.logb Z (volume src.toData) →
      (Fintype.card α : ℝ)*Real.logb Z (max 1 src.upper) ≤ profileLoss →
      0 ≤ g → g ≤ 1/250 → 0 ≤ omegaLoss → 0 ≤ profileLoss → 0 ≤ clip →
      Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      let c := Real.logb Z (C₁.absNorm : ℝ)
      let d₁ := Real.logb Z (D₁.absNorm : ℝ)
      let r₁ := Real.logb Z (normValue (activeConductor P₁ Q₁))
      let e₁ := Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex P₁ Q₁ => P.val) E₁))
      let Kmain := Z^(2*A-c-d₁+r₁+e₁-Mparent+max (d₁-c) 0+6*(3/500)+omegaLoss)
      let Radius := frequencyRadius (jointSecondNominal C₁ Hsource Z A c d₁ r₁ e₁ Mparent (3/500) omegaLoss) Z ξ
      let pad := 2*sourceLoss+parentLoss+ξ/2+Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))
      0 ≤ pad → pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 1/45000 →
      Mparent+pad ≤ Mcap → Mparent+pad+Bmask+ξconductor ≤ d → A+sourceLoss ≤ Bcommon →
      lower ≤ δcommon+(Mparent-max (c-d₁) 0-6*(3/500)-omegaLoss-Bsource)+(3/500)-1/45000 →
      sourceRadius src/(C₁.absNorm : ℝ) ≤ Z^Bsource → Hsource/(C₁.absNorm : ℝ) ≤ Z^Bsource →
      Radius ≤ Cr*Z^Lrad →
      let columns := commonSecondColumns (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ hC₁
      let β := commonSecondBeta (CenteredMomentAmplificationChildInput.original src Rmask seed) C₁ Lfirst
      let parent := firstSideCharacter F left
      let first : FirstSidePresentation ηfirst := ⟨P₁,Q₁,hP₁,E₁,ξ₁,ξ₂,F,left⟩
      let labels := fun q : ActiveBlocks columns β Kmain Radius (Hsource/(C₁.absNorm : ℝ)) =>
        actualCommonBlockKernelLabel src Rmask seed C₁ Lfirst hC₁ hseed parent Kmain Radius (Hsource/(C₁.absNorm : ℝ)) q 1 1 1
      ∀ (bin : HeckeInverseAmplification.NonzeroElement → Option (Fin (I+1) × Fin (I+1))),
      (∀ w,bin w = none ↔ CenteredExceptionalProfile.FixedInducingRow ηfirst (internalQ Q η₀) fixedBadMask 1 w.val) →
      (∀ w bidx,bin w = some bidx →
        jointRelativeSourceZeroBin ηfirst (relativeSlotTranslate M H hH (fun _ : α => η₀))
          (internalQ Q η₀) hQ72
          (relativeSlotTranslate_fixedQ M H hH (fun _ : α => η₀) (internalQ Q η₀)
            (inf_le_left.trans hQM) (fun _ => inf_le_right))
          (fun _ => 1) (fun _ => one_ne_zero)
          (51/100+(e/2)*(bidx.2.val : ℝ)) (51/100+(e/2)*(bidx.2.val : ℝ)+e)
          (3*(bidx.1.val+1 : ℕ)*Z^τ) w) →
      ∀ bidx : Fin (I+1) × Fin (I+1),
      let abin := 51/100+(e/2)*(bidx.2.val : ℝ)
      abin ≤ 167/200 →
      ∀ (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ →
      let aSource := (∏ i,loInput i)*a*a
      |t| ≤ Z^ν →
      src.W₁ 0 = 0 → src.W₂ 0 = 0 →
      (∀ x,‖src.W₁ x‖ ≤ B₁) → (∀ x,‖src.W₂ x‖ ≤ B₂) → A ≤ tailV →
      src.upper ≤ upper → src.b₁ ≤ bplain₁ → src.b₂ ≤ bplain₂ →
      (Rmask.absNorm : ℝ) ≤ Z^BRmask → height ≤ Z^ν →
      let smallLoss := (BRmask+Bcommon)*εmask+ν*(degree : ℝ)
      Bsource ≤ tailSaving+smallLoss →
      let Elow := lowFixedCoefficient (ι := α) Cbound Mslot upper bplain₁ bplain₂ p S degree
      let Eabs := 2*128^(Fintype.card α+2)*Mslot^Fintype.card α*B₁*B₂*
        (max 1 upper)^Fintype.card α*max 1 bplain₁*max 1 bplain₂
      ‖actualSecondRowBlocks parent t columns β Wkernel Kmain Radius (Hsource/(C₁.absNorm : ℝ))
        (fun q => (CenteredMomentSecondEnergySplit.sourceRows q.1.1.val.1 q.1.1.val.2 q.1.2 Radius).filter
          (fun z => first.sourceBin (labels q) bin z = some bidx))‖ /
          (volume src.toData*actualHighPrimeCount M H Sbad Z) ≤
        (Csum*(Ckernel*Elow/aSource+Ckernel*(128/aSource)*Eabs^2)/(Lfirst.absNorm : ℝ))*
          Z^(A-2*c+r₁+e₁+δcommon-1/45000+smallLoss+primeLoss+εsum+volumeLoss) := by
  obtain ⟨degree,S,hlow⟩ := actual_selected_common_low_bin_bound M H hH W
    aslot bslot a b Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon ηfirst parentLoss hparentLoss ξconductor hξconductor
  refine ⟨degree,S,?_⟩
  intro I Wkernel ν tailRows tailV lower tailSaving upper bplain₁ bplain₂ BRmask Sbad primeLoss Bsource Lrad Cr εsum
    hν hgap hheightBudget htailRows hprimeLoss hBsource hBcommonSource hLrad hCr hεsum htailRowsCap
  obtain ⟨Nkernel,Ckernel,Csum,hCkernel,hCsum,hlow⟩ := hlow Wkernel ν tailRows tailV lower tailSaving
    upper bplain₁ bplain₂ BRmask Sbad primeLoss Bsource Lrad Cr εsum
    hν htailRows hprimeLoss hBsource hBcommonSource hLrad hCr hεsum htailRowsCap
  refine ⟨Nkernel,Ckernel,Csum,hCkernel,hCsum,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hlow⟩ := hlow η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hlow,eventually_low_source_heights τ ν d ηheight I hτ hd hgap hη hheightBudget]
    with Z hlow hheights
  intro hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ Rmask seed Lfirst hC₁ hD₁ E₁ ξ₁ ξ₂ F left hR hLfirst hseed
    t Hsource A volumeLoss Mparent g omegaLoss ξ sourceLoss profileLoss clip hHsource hsourceH hsource hcapacity hvolume hvolumeLower hprofile
    hg hgCap homega hprofile0 hclip hclipCost c d₁ r₁ e₁ Kmain Radius pad hpad hbudgetSource
    hMparentCap hMparentConductor hcommonBudget htargetLower
    hsourceB hHcap hRadius columns β parent first labels bin hbinNone hbins bidx abin habinTop
    B₁ B₂ hB₁ hB₂ aSource ht hz₁ hz₂ hW₁ hW₂ hAtail
    hupper hbplain₁ hbplain₂ hRN hhSmall smallLoss htailSaving Elow Eabs
  let vBound := (1+4*Real.pi)*Z^ν
  have hvBound : 0 ≤ vBound := by dsimp only [vBound]; positivity
  have hvCube (θ u v : ℝ) (hθ : ‖θ‖ ≤ Z^ν) (hu : ‖u‖ ≤ Z^ν) (hv : ‖v‖ ≤ Z^ν) :
      |t+2*Real.pi*(u-θ)| ≤ vBound ∧ |t+2*Real.pi*(v-(-θ))| ≤ vBound := by
    simp only [Real.norm_eq_abs] at hθ hu hv
    exact ⟨low_shifted_plain_height t u θ _ ht hu hθ,
      low_shifted_plain_height t v (-θ) _ ht hv (by simpa only [abs_neg] using hθ)⟩
  have hfreqGate (θ u v : ℝ) (hθ : ‖θ‖ ≤ Z^ν) (hu : ‖u‖ ≤ Z^ν) (hv : ‖v‖ ≤ Z^ν) (i : α) :
      |(t+2*Real.pi*(u-θ))+freq i|+Z^τ/2 ≤ (3*bidx.1.val+2 : ℕ)*Z^τ ∧
      |(t+2*Real.pi*(v-(-θ)))+freq i|+Z^τ/2 ≤ (3*bidx.1.val+2 : ℕ)*Z^τ := by
    simp only [Real.norm_eq_abs] at hθ hu hv
    exact ⟨hheights.2.2.1 t (freq i) u θ ht ((hfreq i).trans hhSmall) hu hθ bidx.1.val,
      hheights.2.2.1 t (freq i) v (-θ) ht ((hfreq i).trans hhSmall) hv
        (by simpa only [abs_neg] using hθ) bidx.1.val⟩
  exact hlow hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ Rmask seed Lfirst hC₁ hD₁ E₁ ξ₁ ξ₂ F left hR hLfirst hseed
    t Hsource A volumeLoss Mparent g omegaLoss ξ sourceLoss profileLoss clip hHsource hsourceH hsource hcapacity hvolume hvolumeLower hprofile
    hg hgCap homega hprofile0 hclip hclipCost hpad hbudgetSource
    hMparentCap hMparentConductor hcommonBudget htargetLower hsourceB hHcap hRadius
    I bin hbinNone hbins bidx habinTop hheights.1 hheights.2.1 hfreqGate
    (hheights.2.2.2 bidx.1.val (Nat.le_of_lt_succ bidx.1.is_lt))
    vBound B₁ B₂ hvBound hB₁ hB₂ hvCube hz₁ hz₂ hW₁ hW₂ hAtail
    hupper hbplain₁ hbplain₂ hRN le_rfl hhSmall htailSaving

#print axioms actual_selected_common_low_original_source
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSelectedSeededSource -/

/- BEGIN ORIGINAL MODULE Global.Final.FixedHigh ; sha256 2dd45198262dad74d25eb3785e3ebcf5b8353afeb1eaf6bd87a24aef911caec7 -/
section





/-! Fixed-data specialization of the genuine high transport and mixed cell
estimate. Adapted from weighted upstream HighRows/FixedHigh, revision
2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0 attribution retained. -/
namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace ProbeAssembly
open ProbeFinalAssembly Cycle25ProbeFinalAssembly Submission20261012.Global.HighRowFamily
open Submission20261012.Global.FinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary

theorem fixed_high_bound_of_fullW (hβ : Submission20261012.Global.theta < HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (D : Submission20261012.Global.HighParameters.HighData (HeckeZeroSupremum.beta-Submission20261012.Global.theta))
    (F : WeightedSourceData D.toMomentData)
    (counts : CountParameters F.modulus ⊤ D.t) (τ : ℝ)
    (hτ : 0<τ) (hτd : τ<(1/200:ℝ)/2) (hτcost : 4*τ<(1/200:ℝ)*D.cost)
    (hτt : τ < D.t) (hτ2 : 2*τ ≤ D.t) (hτeps : τ*(2+4*D.eps) < D.t) :
    ∃n : ℕ,0 < n ∧ ∃C : ℝ,0 < C ∧ ∀η : Character,∃Ct : ℝ,0 < Ct ∧ ∀ᶠZ : ℝ in atTop,
      ∀C0 : ℝ,1 ≤ C0 → ∀weightedC : ℝ,0 ≤ weightedC → old_sourceMomentBound F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      FullWCellsAt D F η Z τ n weightedC C0 →
      ‖sourceProbe D F η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (-(4+Submission20261012.Global.b)/6) Z‖≤
        (Ct+C*(2+weightedC)*C0*(η.modulus.absNorm:ℝ)^(2*D.eps))*Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-D.sigma) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  have ht := D.t_pos
  have ht1 := D.t_small
  have hconductor : Submission20261012.Global.h+D.t+2*D.t≤7/8 := by linarith [Submission20261012.Global.h_interval.2]
  have hcoeff : (16-6*Submission20261012.Global.ly)*D.e ≤ ((13243:ℝ)/1000+1)*D.e := by
    nlinarith [Submission20261012.Global.ly_coarse.1,D.e_pos]
  have hfinal : (159*D.ε+D.t+D.t+7*D.t)+(12*D.e+D.eps*(D.N+8))+
      (D.t+2*τ+D.t+D.t+D.t*Submission20261012.Global.ell+(16-6*Submission20261012.Global.ly)*D.e)+2*D.t ≤ 1/4000 := by
    have hbase := D.central_budget
    have hdet := D.detector_budget
    have heps := D.epsilon_small
    have hcost := D.cost_pos
    have hkap := D.kappa_pos
    have htheta := Submission20261012.Global.LowGeometry.theta_coarse
    nlinarith only [hbase,hdet,heps,hcost,hkap,hβhi,hcoeff,hτ2,htheta]
  obtain ⟨n,hn,C,hC,hbound⟩ := actual_high_probe_from_moments_and_fullW F.modulus ⊤ le_top D.N
    D.e D.eps 1 2 1 D.t (1/200) (7/8) D.rmin τ D.ε D.κ D.cost D.t D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    ht.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.kappa_pos
    D.cost_pos.le ht D.phase_budget D.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j=>(D.slots_bounds j).2.1) (fun j=>(D.slots_bounds j).2.2)
    (fun _=> F.w) (fun _=> F.support) (fun _=> F.smooth) (fun _=> F.bounded)
    (fun _=> F.compact) (fun _=> F.nonzero) D.slots_sum
    (by norm_num) D.epsilon_small D.kappa_small hτd hτcost (by nlinarith [D.detector_budget])
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.t D.t D.t (2*τ) D.t ht ht ht (by linarith)
    D.t (2*D.t) ht (by linarith)
    (by linarith only [D.weighted_top])
    hfinal
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    Submission20261012.Global.weightedTarget (D.t/8) (Submission20261012.Global.FinalAssembly.weighted_target_lower hβ.le)
    (by positivity) (D.t/8) (by positivity) (by norm_num) hconductor (by linarith) hβ.le hβhi
    D.sigma D.sigma_pos D.geometric_budget D.principal_budget D.window_budget D.floor_budget
    (Submission20261012.Global.FinalAssembly.weighted_target_saving D hβ) counts
  refine ⟨n,hn,C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,hb⟩ := hbound η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hb,sourceDyad_geometry_eventually (1/200) (7/8) D.t (Submission20261012.Global.h+D.t)
    (by norm_num) (by norm_num) ht hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hb hgeo hnheight hZ
  intro C0 hC0 weightedC hweightedC hmom hcells
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,hestimate⟩ := hb
  apply hestimate C0 hC0 weightedC hweightedC
  · intro k hk i hi j hj
    dsimp only
    intro hne t htheight
    let rows := supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^(Submission20261012.Global.h+D.t))) grid
    let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
    have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
    have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
    have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ Z^(Submission20261012.Global.h+D.t) := by
      intro u hu
      have hh := mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1
      exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
    have hg := hgeo rows hrows k (hne.mono hsub)
    obtain ⟨u,hu⟩ := hne
    have huj : grid u=j := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
    have hjne : j≠0 := huj ▸ ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsubr hu)).2.2
    have ha : (51/100:ℝ)<51/100+D.e*j := by
      have hjp : (0:ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hjne
      nlinarith [D.e_pos]
    have ha' : (51/100:ℝ)+D.e*j≤7/8 := by simpa only [huj] using (hbins u).2.1
    have hrow' : ∀v∈rows',v.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm v ∧
        (calibrationForSet F.S F.maximal).residueMonoid v.val≠0 ∧
        rowNorm v ≤ Z^(sourceDyadConductor Z D.t k-D.t) := by
      intro v hv
      exact ⟨(hrows v (hsubr hv)).1,(hrows v (hsubr hv)).2.1,
        ((mem_supportedNonfloorRows F.S F.maximal _ grid v).mp (hsubr hv)).2.1,hg.2.2.2.2.2 v (hsub hv)⟩
    have hi' : (i:ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hheight : (3*i+1:ℕ)*Z^τ ≤ Z^(2*τ) := by
      have hZp : 0 < Z := zero_lt_one.trans hZ
      calc
        _≤(3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
        _ ≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hnheight (by positivity)
        _=Z^(2*τ) := by rw [←Real.rpow_add hZp];congr 1;ring
    have hdelta : 2*((51/100:ℝ)+D.e*j)-1 ≤ 5/6 := by linarith only [ha']
    simp only [ite_eq_left hdelta]
    apply hmom rows' (sourceDyadConductor Z D.t k) (51/100+D.e*j) hg.2.2.1 hg.2.2.2.1 ha ha' hrow' i
      ((17/50:ℂ)+t.1.2*Complex.I)
    · simp
    · simpa using htheight.2.trans hheight
  · have hc := hcells idx grid
      (by
        intro u hu
        exact ⟨(hlabels u).2.1,(hlabels u).2.2.1,(hbins u).2.1⟩)
      (by
        intro u hu
        exact (hbins u).2.2.2.2.1)
      (by
        intro u hu
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbins u).2.2.1)
    intro k hk i hi j hj
    dsimp only
    intro hne hd hdelta hcap
    exact hc k hk i hi j hj hne hd hdelta (by linarith only [hcap])

end ProbeAssembly

end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Final.FixedHigh -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalSides ; sha256 b9f7af670a3ca850ec54ddefdd163c93411e7c87e14e559951ed156ba0379e69 -/
section




/-! Both first-source orientations for the coherent exceptional endpoint. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCanonicalFirst
open CenteredMomentFirstMixedRightTransport CenteredMomentFirstMixedAllowance
open CenteredMomentFirstScale CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentFiniteProfileExceptionalCommon CenteredMomentExceptionalAmplitudePair
open CenteredMomentFiniteProfileExceptional CenteredMomentReflectedSource
open CenteredMomentCommonAllocationSum CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentCommonHeightEnvelope
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
namespace FirstJointLabel

def sideCharacter (q : FirstJointLabel ι) (left : Bool) : Character :=
  if left then q.pair.left else q.pair.right

def sideSubset (q : FirstJointLabel ι) (left : Bool) :
    Finset (CommonIndex (q.sideCommon left) (q.sideCommon (!left))) :=
  match left with
  | true => q.E
  | false => swapSubset q.C q.D q.E

theorem side_equal_support (q : FirstJointLabel ι) (left : Bool) :
    CompletedGauss.primeSupport (q.sideCommon left) = CompletedGauss.primeSupport (q.sideCommon (!left)) := by
  cases left <;> simp only [sideCommon,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
  · exact q.hCD.symm
  · exact q.hCD

theorem side_modulus (q : FirstJointLabel ι) (left : Bool) :
    (q.sideCharacter left).modulus = q.parent.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex (q.sideCommon left) (q.sideCommon (!left)) => P.val)
        (q.sideSubset left)*activeConductor (q.sideCommon left) (q.sideCommon (!left))} := by
  cases left
  · exact right_modulus q.parent q.C q.D q.hC q.E q.leftRay q.rightRay q.pair
  · exact q.pair.left_modulus

def sideReference (q : FirstJointLabel ι) (left : Bool) (Z A : ℝ) : ℝ :=
  if left then q.leftErrorReference Z A else q.rightErrorReference Z A

theorem side_reference_powers (q : FirstJointLabel ι) (left : Bool) (Z A : ℝ) (hZ : 1 < Z) :
    q.sideReference left Z A = q.parentCost*Z^(A-2*Real.logb Z ((q.sideCommon left).absNorm : ℝ)+
      q.activeWidth Z+q.punctureWidth Z+allowance (q.sideCommon left) (q.sideCommon (!left)) Z) := by
  cases left
  · simpa only [sideReference,sideCommon,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,
      q.allowances_eq Z,rightWidth] using (q.error_reference_powers Z A hZ).2
  · simpa only [sideReference,sideCommon,ite_true,ite_false,Bool.not_true,Bool.false_eq_true,
      q.allowances_eq Z,leftWidth] using (q.error_reference_powers Z A hZ).1

theorem sideReference_literal (q : FirstJointLabel ι) (left : Bool) (Z A : ℝ) :
    q.sideReference left Z A = ((q.sideCharacter left).modulus.absNorm : ℝ)*
      (Z^A/((q.sideCommon left).absNorm : ℝ)^2)*
        Z^(allowance (q.sideCommon left) (q.sideCommon (!left)) Z) := by
  cases left <;> rfl

theorem sourceChild_sideReference (q : FirstJointLabel ι) (i : q.SourceIndex)
    (left : Bool) (Z A : ℝ) (hZ : 1 < Z) :
    (q.sourceChild i).sideReference left Z A = q.sideReference left Z A := by
  rw [(q.sourceChild i).side_reference_powers left Z A hZ,q.side_reference_powers left Z A hZ]
  rfl

end FirstJointLabel

lemma coherentExceptionalProfile_height_le [DecidableEq ι] {wlo whi : ℝ}
    (Sprofile : Finset (ℕ×ℕ)) (src : Input ι) (profile : Profiles wlo whi)
    (J : ℕ) (Q : Ideal O) (K t T : ℝ) (hK : 0 ≤ K) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    coherentExceptionalProfile Sprofile src profile J Q K t ≤
      coherentExceptionalProfile Sprofile src profile J Q K T := by
  have hp := Profiles.control_nonneg profile Sprofile
  have hs := slotControl_nonneg src.toData
  have hv := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  unfold coherentExceptionalProfile profileMass
  simp only [withHeight,Real.norm_eq_abs,abs_of_nonneg hT]
  gcongr <;> exact le_rfl

#print axioms FirstJointLabel.side_modulus
#print axioms coherentExceptionalProfile_height_le
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalSides -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstSecondJointSum ; sha256 0a9a0761ef2d7d355d25b3c0426b12c9fc3b61ff951eaef59d8f1c79c1307d6d -/
section



/-! Exact conversion of literal source packets to the finite arithmetic
row and dyadic-fiber sum consumed by the analytic high theorem. The good
predicate is membership in the actual packet image, so it retains every
source/bin/sector restriction and introduces no spurious active branch. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentCanonicalFirst CenteredMomentSecondPhysicalBlock
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ActualFirstSecondSource
variable {src : Input ι} {R seed : Ideal O} {Kfirst : ℝ}
  {radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ}
  {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

def rayPackets (X : Finset (Packet src R seed Kfirst radius side K Radius H))
    (χ ξ : RayCharacter) := X.filter fun x => x.1.2.2.1=χ ∧ x.1.2.2.2=ξ

abbrev FiberTarget (fallback : First src R seed Kfirst radius) (χ ξ : RayCharacter)
    (K Radius H : First src R seed Kfirst radius → ℝ) (side : Bool) :=
  (q : NonzeroJointSourceRow (original src R seed) side) ×
    q.val.DyadicFiber Kfirst (radius q.val.first q.val.E) (sourceRadius src)
      (secondScale fallback K χ ξ q.val) (secondScale fallback Radius χ ξ q.val)
      (secondScale fallback H χ ξ q.val)

def liftPacket (fallback : First src R seed Kfirst radius) (χ ξ : RayCharacter)
    (x : Packet src R seed Kfirst radius side K Radius H)
    (hχ : x.1.2.2.1=χ) (hξ : x.1.2.2.2=ξ) (hz : (row x).z≠0) :
    FiberTarget fallback χ ξ K Radius H side :=
  ⟨⟨row x,hz⟩,x.1.1.2.2,fun j => ⟨(x.2.1.2 j : ℤ),by
    simp only [secondScale,←hχ,←hξ,firstAt_packet]
    exact (x.2.1.2 j).property⟩⟩

def forgetFiber (fallback : First src R seed Kfirst radius) (χ ξ : RayCharacter)
    (y : FiberTarget fallback χ ξ K Radius H side) :
    ActualJointSourceRow (original src R seed) side × RayCharacter × RayCharacter ×
      (Fin 4 → ℤ) × (Fin 4 → ℤ) :=
  (y.1.val,χ,ξ,(fun j => (y.2.1 j : ℤ)),(fun j => (y.2.2 j : ℤ)))

theorem forget_lift (fallback : First src R seed Kfirst radius) (χ ξ : RayCharacter)
    (x : Packet src R seed Kfirst radius side K Radius H)
    (hχ : x.1.2.2.1=χ) (hξ : x.1.2.2.2=ξ) (hz : (row x).z≠0) :
    forgetFiber fallback χ ξ (liftPacket fallback χ ξ x hχ hξ hz) = key x := by
  simp only [forgetFiber,liftPacket,key,hχ,hξ]

def rayTarget (fallback : First src R seed Kfirst radius)
    (X : Finset (Packet src R seed Kfirst radius side K Radius H))
    (hzero : ∀ x∈X,(row x).z≠0) (χ ξ : RayCharacter) :
    Finset (FiberTarget fallback χ ξ K Radius H side) :=
  (rayPackets X χ ξ).attach.image fun x => liftPacket fallback χ ξ x.val
    (Finset.mem_filter.mp x.property).2.1 (Finset.mem_filter.mp x.property).2.2
    (hzero x.val (Finset.mem_filter.mp x.property).1)

def rayRows (fallback : First src R seed Kfirst radius)
    (X : Finset (Packet src R seed Kfirst radius side K Radius H))
    (hzero : ∀ x∈X,(row x).z≠0) (χ ξ : RayCharacter) :
    Finset (NonzeroJointSourceRow (original src R seed) side) :=
  (rayTarget fallback X hzero χ ξ).image Sigma.fst

variable (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)

def fiberValue (fallback : First src R seed Kfirst radius) (χ ξ : RayCharacter)
    (V P : ℝ) (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
    (y : FiberTarget fallback χ ξ K Radius H side) : ℝ :=
  let q := y.1.val
  let s := q.kernelLabel src R seed src.η χ ξ⁻¹ 1 1 1 (q.seed_dvd_first src R seed hs hz₁ hz₂)
  let k := firstAt fallback q χ ξ y.2.1
  ∑ χ₂ : RayCharacter, ∑ ξ₂ : RayCharacter, ∑ D∈s.physicalProjectors,
    ‖(s.withRays χ₂ ξ₂).physicalRowTerm V P (t k) q.z W (K k) (Radius k) (fun j => (y.2.2 j : ℤ)) D‖

theorem liftPacket_value (fallback : First src R seed Kfirst radius) (χ ξ : RayCharacter)
    (V P : ℝ) (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
    (x : Packet src R seed Kfirst radius side K Radius H)
    (hχ : x.1.2.2.1=χ) (hξ : x.1.2.2.2=ξ) (hz : (row x).z≠0) :
    fiberValue hs hz₁ hz₂ fallback χ ξ V P t W (liftPacket fallback χ ξ x hχ hξ hz) =
      packetValue hs hz₁ hz₂ V P t W x := by
  subst χ; subst ξ
  simp only [fiberValue,liftPacket,firstAt_packet]
  rfl

theorem sum_rayTarget (fallback : First src R seed Kfirst radius)
    (X : Finset (Packet src R seed Kfirst radius side K Radius H))
    (hzero : ∀ x∈X,(row x).z≠0) (χ ξ : RayCharacter)
    (V P : ℝ) (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ)) :
    (∑ y∈rayTarget fallback X hzero χ ξ,fiberValue hs hz₁ hz₂ fallback χ ξ V P t W y) =
      ∑ x∈rayPackets X χ ξ,packetValue hs hz₁ hz₂ V P t W x := by
  unfold rayTarget
  rw [Finset.sum_image]
  · simp only [liftPacket_value]
    exact Finset.sum_attach _ _
  · intro x hx y hy he
    apply Subtype.ext
    apply key_injective
    exact (forget_lift fallback χ ξ x.val _ _ _).symm.trans
      ((congrArg (forgetFiber fallback χ ξ) he).trans (forget_lift fallback χ ξ y.val _ _ _))

theorem sum_ray_fibers (fallback : First src R seed Kfirst radius)
    (X : Finset (Packet src R seed Kfirst radius side K Radius H))
    (hzero : ∀ x∈X,(row x).z≠0) (χ ξ : RayCharacter)
    (V P : ℝ) (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ)) :
    (∑ x∈rayPackets X χ ξ,packetValue hs hz₁ hz₂ V P t W x) =
      ∑ q∈rayRows fallback X hzero χ ξ,
        ∑ n₁ : q.val.FirstDyadic Kfirst (radius q.val.first q.val.E) (sourceRadius src),
        ∑ n₂ : q.val.SecondDyadic (secondScale fallback K χ ξ q.val n₁)
          (secondScale fallback Radius χ ξ q.val n₁) (secondScale fallback H χ ξ q.val n₁),
        if (⟨q,n₁,n₂⟩ : FiberTarget fallback χ ξ K Radius H side)∈rayTarget fallback X hzero χ ξ
        then fiberValue hs hz₁ hz₂ fallback χ ξ V P t W ⟨q,n₁,n₂⟩ else 0 := by
  rw [←sum_rayTarget hs hz₁ hz₂ fallback X hzero χ ξ V P t W]
  let T := rayTarget fallback X hzero χ ξ
  have hsub : T ⊆ (rayRows fallback X hzero χ ξ).sigma (fun _ => Finset.univ) := by
    intro y hy
    exact Finset.mem_sigma.mpr ⟨Finset.mem_image.mpr ⟨y,hy,rfl⟩,Finset.mem_univ _⟩
  have he := Finset.sum_subset hsub (f := fun y =>
    if y∈T then fiberValue hs hz₁ hz₂ fallback χ ξ V P t W y else 0)
    (fun _ _ hn => if_neg hn)
  simp only [Finset.sum_sigma,Fintype.sum_sigma] at he
  simpa only [T,Finset.sum_ite_mem,Finset.inter_self] using he

theorem sum_ray_partition
    (X : Finset (Packet src R seed Kfirst radius side K Radius H))
    (V P : ℝ) (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ)) :
    (∑ x∈X,packetValue hs hz₁ hz₂ V P t W x) =
      ∑ χ : RayCharacter,∑ ξ : RayCharacter,
        ∑ x∈rayPackets X χ ξ,packetValue hs hz₁ hz₂ V P t W x := by
  simp only [rayPackets,Finset.sum_filter]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := X)]
  apply Finset.sum_congr rfl
  intro x hx
  simp [ite_and]

theorem mem_rayRows_witness (fallback : First src R seed Kfirst radius)
    (X : Finset (Packet src R seed Kfirst radius side K Radius H))
    (hzero : ∀ x∈X,(row x).z≠0) (χ ξ : RayCharacter)
    (q : NonzeroJointSourceRow (original src R seed) side)
    (hq : q∈rayRows fallback X hzero χ ξ) :
    ∃ x∈X,x.1.2.2.1=χ ∧ x.1.2.2.2=ξ ∧ row x=q.val := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact ⟨x.val,(Finset.mem_filter.mp x.property).1,
    (Finset.mem_filter.mp x.property).2.1,(Finset.mem_filter.mp x.property).2.2,rfl⟩

theorem mem_rayTarget_witness (fallback : First src R seed Kfirst radius)
    (X : Finset (Packet src R seed Kfirst radius side K Radius H))
    (hzero : ∀ x∈X,(row x).z≠0) (χ ξ : RayCharacter)
    (y : FiberTarget fallback χ ξ K Radius H side)
    (hy : y∈rayTarget fallback X hzero χ ξ) :
    ∃ x∈X, ∃ hχ : x.1.2.2.1=χ, ∃ hξ : x.1.2.2.2=ξ, ∃ hz : (row x).z≠0,
      y=liftPacket fallback χ ξ x hχ hξ hz := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact ⟨x.val,(Finset.mem_filter.mp x.property).1,
    (Finset.mem_filter.mp x.property).2.1,(Finset.mem_filter.mp x.property).2.2,_,rfl⟩

end ActualFirstSecondSource
#print axioms ActualFirstSecondSource.sum_rayTarget
#print axioms ActualFirstSecondSource.sum_ray_fibers
#print axioms ActualFirstSecondSource.sum_ray_partition
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstSecondJointSum -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowFirstBlocks ; sha256 f87ec0237e65be9f755352ac240670dbaeca80bb901bb3b61ad742b18788c454 -/
section



/-! Literal coherent low bins at either first side. The first character
presentation keeps its original order; only the physical common is selected. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentSecondBlockAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockHarmonicMass
open ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem first_source_selected_seed (src : Input ι) (R seed : Ideal O)
    (hs : Squarefree seed) (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0)
    (K : ℝ) (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (i : FirstSourceOuterIndex src R seed K radius) (left : Bool) :
    seed ∣ (firstSourceOuterLabel src R seed K radius i).sideCommon left := by
  have hh := actual_common_gates src R seed hs hz₁ hz₂ i.1.val.1 i.1.val.2 i.1.property
  cases left
  · exact hh.2.2.2.2.1
  · exact hh.2.2.2.1

lemma FirstJointLabel.activeWidth_normValue (q : FirstJointLabel ι) (Z : ℝ) :
    q.activeWidth Z = Real.logb Z (normValue (activeConductor q.C q.D)) := by
  rfl

lemma FirstJointLabel.punctureWidth_normValue (q : FirstJointLabel ι) (Z : ℝ) :
    q.punctureWidth Z = Real.logb Z
      (normValue (primeSubsetGenerator (fun P : CommonIndex q.C q.D => P.val) q.E)) := by
  simp only [FirstJointLabel.punctureWidth, FirstJointLabel.puncture, normValue, eisEmbedding_norm_sq_eq_absNorm_span]

def firstLowMainScale (q : FirstJointLabel ι) (left : Bool) (Z A M omega : ℝ) : ℝ :=
  let c := Real.logb Z ((q.sideCommon left).absNorm : ℝ)
  let d := Real.logb Z ((q.sideCommon (!left)).absNorm : ℝ)
  Z^(2*A-c-d+Real.logb Z (normValue (activeConductor q.C q.D))+
    Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex q.C q.D => P.val) q.E))-M+max (d-c) 0+6*(3/500)+omega)

def firstLowRadius (q : FirstJointLabel ι) (left : Bool) (Hsource Z A M omega ξ : ℝ) : ℝ :=
  let c := Real.logb Z ((q.sideCommon left).absNorm : ℝ)
  let d := Real.logb Z ((q.sideCommon (!left)).absNorm : ℝ)
  frequencyRadius (jointSecondNominal (q.sideCommon left) Hsource Z A c d
    (Real.logb Z (normValue (activeConductor q.C q.D)))
    (Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex q.C q.D => P.val) q.E))) M (3/500) omega) Z ξ

def firstLowBinBlock {κ : Type*} [DecidableEq κ]
    (src : Input ι) (R seed : Ideal O) (hs : Squarefree seed)
    (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0)
    (Kfirst : ℝ) (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (k : (i : FirstSourceOuterIndex src R seed Kfirst radius) ×
      (firstSourceOuterLabel src R seed Kfirst radius i).SourceIndex)
    (left : Bool) (Z A M omega ξ t : ℝ) (W : 𝓢(ℝ,ℂ))
    (bin : HeckeInverseAmplification.NonzeroElement → Option κ) (b : κ) : ℂ :=
  let q := firstSourceOuterLabel src R seed Kfirst radius k.1
  let child := q.sourceChild k.2
  let C := q.sideCommon left
  let hC := q.sideCommon_supported left
  let F : FirstSidePresentation src.η :=
    ⟨child.C,child.D,child.hC,child.E,child.leftRay,child.rightRay,child.pair,left⟩
  let parent := F.sourceParent
  let Kmain := firstLowMainScale q left Z A M omega
  let Radius := firstLowRadius q left (sourceRadius src) Z A M omega ξ
  let columns := commonSecondColumns (original src R seed) C hC
  let β := commonSecondBeta (original src R seed) C k.2.1.val
  let labels := fun s : ActiveBlocks columns β Kmain Radius (sourceRadius src/(C.absNorm : ℝ)) =>
    actualCommonBlockKernelLabel src R seed C k.2.1.val hC
      (first_source_selected_seed src R seed hs hz₁ hz₂ Kfirst radius k.1 left)
      parent Kmain Radius (sourceRadius src/(C.absNorm : ℝ)) s 1 1 1
  actualSecondRowBlocks parent t columns β W Kmain Radius (sourceRadius src/(C.absNorm : ℝ))
    (fun s => (CenteredMomentSecondEnergySplit.sourceRows s.1.1.val.1 s.1.1.val.2 s.1.2 Radius).filter
      (fun z => F.sourceBin (labels s) bin z = some b))

#print axioms first_source_selected_seed
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowFirstBlocks -/
