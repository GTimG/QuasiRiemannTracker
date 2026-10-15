/- Asymmetric reserve and endpoint refinement: Zhongpai Gao, with AI assistance. Adapts Kari Roegnvaldsson’s affine/reserve source at 14ab1618c5133a7d12e06aa76661bbcb34e843cd, following accepted c707738a659786b9a44a79c629bed8c801cca8f3. Original notices below are retained. -/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B001
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B105
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B107
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B108

/- BEGIN ORIGINAL MODULE Analytic.JointLowFirstSum ; sha256 f2f4158964ba80c543831bde929d40881068664dce464be50efd635053cb7e01 -/
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
local instance firstLowSumFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
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
theorem actual_first_low_bin_sum
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
    (ξconductor : ℝ) (hξconductor : 0 < ξconductor)
    (Bfirst LfirstRad Crfirst εouter : ℝ)
    (hBfirst : 0 ≤ Bfirst) (hLfirstRad : 0 ≤ LfirstRad)
    (hCrfirst : 0 < Crfirst) (hεouter : 0 < εouter) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
    ∀ (I : ℕ) (Wkernel : 𝓢(ℝ,ℂ)) (ν tailRows tailV lower tailSaving upper bplain₁ bplain₂ BRmask : ℝ)
      (Sbad : Finset (Ideal O)) (primeLoss Bsource Lrad Cr εsum : ℝ),
      0 < ν → ν < τ → 2*τ < d*ηheight → 0 ≤ tailRows → 0 < primeLoss → 0 ≤ Bsource → Bsource ≤ Bcommon →
      0 ≤ Lrad → 0 < Cr → 0 < εsum → Lrad+1 ≤ tailRows → Bfirst ≤ Bsource →
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
      src.η = ηfirst →
      ∀ (Rmask seed : Ideal O), Rmask ≠ 0 → ∀ hs : Squarefree seed, seed ≠ 0 →
      ∀ (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0),
      0 < sourceRadius src → sourceRadius src ≤ Z^Bfirst →
      ∀ (Kfirst : ℝ), 0 < Kfirst →
      ∀ radius : (v : Labels src Rmask seed) → Finset (CommonIndex v.val.1 v.val.2) → ℝ,
      (∀ v E,radius v E ≤ Crfirst*Z^LfirstRad) →
      let q := firstSourceOuterLabel src Rmask seed Kfirst radius
      ∀ (labels : Finset (FirstSourceOuterIndex src Rmask seed Kfirst radius)) (left : Bool)
        (psector A volumeLoss Mparent g omegaLoss ξ sourceLoss profileLoss clip refwidth : ℝ),
      (∀ i ∈ labels,((CenteredMomentRankinRadical.commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^psector) →
      Real.logb Z (sourceRadius src) ≤ A+sourceLoss →
      A+(7/2)*(∑ i,w i) ≤ Mparent+g → Real.logb Z (volume src.toData) ≤ A →
      A-volumeLoss ≤ Real.logb Z (volume src.toData) →
      (Fintype.card α : ℝ)*Real.logb Z (max 1 src.upper) ≤ profileLoss →
      0 ≤ g → g ≤ 1/241 → 0 ≤ omegaLoss → 0 ≤ profileLoss → 0 ≤ clip →
      Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      let pad := 2*sourceLoss+parentLoss+ξ/2+Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))
      0 ≤ pad → pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 1/2000000 →
      Mparent+pad ≤ Mcap → Mparent+pad+Bmask+ξconductor ≤ d → A+sourceLoss ≤ Bcommon →
      (∀ i ∈ labels,
        let c := Real.logb Z (((q i).sideCommon left).absNorm : ℝ);
        let d₁ := Real.logb Z (((q i).sideCommon (!left)).absNorm : ℝ);
        -2*c+(q i).activeWidth Z+(q i).punctureWidth Z ≤ refwidth ∧
        lower ≤ δcommon+(Mparent-max (c-d₁) 0-6*(3/500)-omegaLoss-Bsource)+(3/500)-1/48000 ∧
        firstLowRadius (q i) left (sourceRadius src) Z A Mparent omegaLoss ξ ≤ Cr*Z^Lrad) →
      let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
      ∀ (t : ((i : FirstSourceOuterIndex src Rmask seed Kfirst radius) × (q i).SourceIndex) → ℝ),
      (∀ k ∈ domain, |t k| ≤ Z^ν) →
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
      ∀ bidx : Fin (I+1) × Fin (I+1), 51/100+(e/2)*(bidx.2.val : ℝ) ≤ 167/200 →
      ∀ (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ x,‖src.W₁ x‖ ≤ B₁) → (∀ x,‖src.W₂ x‖ ≤ B₂) → A ≤ tailV →
      src.upper ≤ upper → src.b₁ ≤ bplain₁ → src.b₂ ≤ bplain₂ →
      (Rmask.absNorm : ℝ) ≤ Z^BRmask → height ≤ Z^ν →
      let smallLoss := (BRmask+Bcommon)*εmask+ν*(degree : ℝ)
      Bsource ≤ tailSaving+smallLoss →
      let aSource := (∏ i,loInput i)*a*a
      let Elow := lowFixedCoefficient (ι := α) Cbound Mslot upper bplain₁ bplain₂ p S degree
      let Eabs := 2*128^(Fintype.card α+2)*Mslot^Fintype.card α*B₁*B₂*
        (max 1 upper)^Fintype.card α*max 1 bplain₁*max 1 bplain₂
      (∑ k ∈ domain,
        ‖firstLowBinBlock src Rmask seed hs hz₁ hz₂ Kfirst radius k left
          Z A Mparent omegaLoss ξ (t k) Wkernel bin bidx‖ /
          (volume src.toData*actualHighPrimeCount M H Sbad Z)) ≤
        (Csum*(Ckernel*Elow/aSource+Ckernel*(128/aSource)*Eabs^2))*
          Z^(psector+A+refwidth+δcommon-1/48000+smallLoss+primeLoss+εsum+volumeLoss+εouter)/
          (seed.absNorm : ℝ) := by
  obtain ⟨degree,S,hlow⟩ := actual_selected_common_low_original_source M H hH W
    aslot bslot a b Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon ηfirst parentLoss hparentLoss ξconductor hξconductor
  obtain ⟨Couter,hCouter,houter⟩ := actual_first_source_sector_harmonic_mass
    Bfirst LfirstRad Crfirst εouter hBfirst hLfirstRad hCrfirst hεouter
  refine ⟨degree,S,?_⟩
  intro I Wkernel ν tailRows tailV lower tailSaving upper bplain₁ bplain₂ BRmask Sbad primeLoss Bsource Lrad Cr εsum
    hν hgap hheightBudget htailRows hprimeLoss hBsource hBcommonSource hLrad hCr hεsum htailRowsCap hBfirstSource
  obtain ⟨Nkernel,Ckernel,Csum,hCkernel,hCsum,hlow⟩ := hlow I Wkernel ν tailRows tailV lower tailSaving
    upper bplain₁ bplain₂ BRmask Sbad primeLoss Bsource Lrad Cr εsum
    hν hgap hheightBudget htailRows hprimeLoss hBsource hBcommonSource hLrad hCr hεsum htailRowsCap
  refine ⟨Nkernel,Ckernel,Csum*Couter,hCkernel,mul_pos hCsum hCouter,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hlow⟩ := hlow η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hlow,houter] with Z hlow houter
  intro hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ hη Rmask seed hR hs hs0 hz₁ hz₂ hsource₀ hsource
    Kfirst hKfirst radius hr q labels left psector A volumeLoss Mparent g omegaLoss ξ sourceLoss profileLoss clip refwidth
    hrad hsourceLog hcapacity hvolume hvolumeLower hprofile hg hgCap homega hprofile0 hclip hclipCost
    pad hpad hbudgetSource hMparentCap hMparentConductor hcommonBudget hgeometry domain t ht
    bin hbinNone hbins bidx habinTop B₁ B₂ hB₁ hB₂ hW₁ hW₂ hAtail
    hupper hbplain₁ hbplain₂ hRN hhSmall smallLoss htailSaving aSource Elow Eabs
  subst ηfirst
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hmass := houter.2 α src Rmask seed hs hs0 hz₁ hz₂ hsource₀ hsource Kfirst hKfirst radius hr labels psector hrad
  have hmass' : (∑ k ∈ domain,1/((k.2.1.val).absNorm : ℝ)) ≤ Couter*Z^(psector+εouter)/(seed.absNorm : ℝ) := by
    cases left
    · exact hmass.2
    · exact hmass.1
  let coefficient := Csum*(Ckernel*Elow/aSource+Ckernel*(128/aSource)*Eabs^2)
  have hElow : 0 ≤ Elow := low_fixed_coefficient_nonneg Cbound Mslot upper bplain₁ bplain₂ p S degree hCbound.le
  have haSource : 0 < aSource := by
    dsimp only [aSource]
    have hlo (i : α) : 0 < loInput i := by rw [←hloInput i]; exact src.lo_pos i
    exact mul_pos (mul_pos (Finset.prod_pos (fun i _ => hlo i)) ha) ha
  have hcoefficient : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have hpoint (k) (hk : k ∈ domain) :
      ‖firstLowBinBlock src Rmask seed hs hz₁ hz₂ Kfirst radius k left
        Z A Mparent omegaLoss ξ (t k) Wkernel bin bidx‖ /
        (volume src.toData*actualHighPrimeCount M H Sbad Z) ≤
      coefficient*Z^(A+refwidth+δcommon-1/48000+smallLoss+primeLoss+εsum+volumeLoss)/((k.2.1.val).absNorm : ℝ) := by
    have hgates : k.1 ∈ labels ∧ Squarefree k.2.1.val ∧ k.2.1.val ≠ 0 ∧ ((k.2.1.val).absNorm : ℝ) ≤ Z^Bfirst := by
      cases left
      · exact firstRightSourceLabels_gates labels q _ Z Bfirst hz.le (fun _ _ => hsource) k hk
      · exact firstLeftSourceLabels_gates labels q _ Z Bfirst hz.le (fun _ _ => hsource) k hk
    let child := (q k.1).sourceChild k.2
    let C := (q k.1).sideCommon left
    let D := (q k.1).sideCommon (!left)
    let hC := (q k.1).sideCommon_supported left
    let hD := (q k.1).sideCommon_supported (!left)
    have hseed := first_source_selected_seed src Rmask seed hs hz₁ hz₂ Kfirst radius k.1 left
    have hCn : (1 : ℝ) ≤ C.absNorm := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
    have hsourceB : sourceRadius src/(C.absNorm : ℝ) ≤ Z^Bsource := by
      exact (div_le_self hsource₀.le hCn).trans
        (hsource.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hBfirstSource))
    have hb := hlow hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
      hloInput hhiInput hX₁ hX₂ hY₁ hY₂ child.C child.D child.hC C D Rmask seed k.2.1.val hC hD.1
      child.E child.leftRay child.rightRay child.pair left hR hgates.2.1 hseed
      (t k) (sourceRadius src) A volumeLoss Mparent g omegaLoss ξ sourceLoss profileLoss clip
      hsource₀ le_rfl hsourceLog hcapacity hvolume hvolumeLower hprofile hg hgCap homega hprofile0 hclip hclipCost
      hpad hbudgetSource hMparentCap hMparentConductor hcommonBudget (hgeometry k.1 hgates.1).2.1
      hsourceB hsourceB (hgeometry k.1 hgates.1).2.2
      bin hbinNone hbins bidx habinTop B₁ B₂ hB₁ hB₂ (ht k hk) hz₁ hz₂ hW₁ hW₂ hAtail
      hupper hbplain₁ hbplain₂ hRN hhSmall htailSaving
    change ‖firstLowBinBlock src Rmask seed hs hz₁ hz₂ Kfirst radius k left
      Z A Mparent omegaLoss ξ (t k) Wkernel bin bidx‖ /
      (volume src.toData*actualHighPrimeCount M H Sbad Z) ≤
      (coefficient/((k.2.1.val).absNorm : ℝ))*
      Z^(A-2*Real.logb Z (C.absNorm : ℝ)+Real.logb Z (normValue (activeConductor child.C child.D))+
        Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex child.C child.D => P.val) child.E))+
        δcommon-1/48000+smallLoss+primeLoss+εsum+volumeLoss) at hb
    have hactive : Real.logb Z (normValue (activeConductor child.C child.D)) = (q k.1).activeWidth Z :=
      ((q k.1).activeWidth_normValue Z).symm
    have hpuncture : Real.logb Z (normValue (primeSubsetGenerator
        (fun P : CommonIndex child.C child.D => P.val) child.E)) = (q k.1).punctureWidth Z :=
      ((q k.1).punctureWidth_normValue Z).symm
    rw [hactive,hpuncture] at hb
    apply hb.trans
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ hcoefficient
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [(hgeometry k.1 hgates.1).1]
  apply (Finset.sum_le_sum hpoint).trans
  rw [show (∑ k ∈ domain,coefficient*Z^(A+refwidth+δcommon-1/48000+smallLoss+primeLoss+εsum+volumeLoss)/
      ((k.2.1.val).absNorm : ℝ)) =
      coefficient*Z^(A+refwidth+δcommon-1/48000+smallLoss+primeLoss+εsum+volumeLoss)*
      (∑ k ∈ domain,1/((k.2.1.val).absNorm : ℝ)) by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk; ring]
  apply (mul_le_mul_of_nonneg_left hmass' (by positivity)).trans_eq
  dsimp only [coefficient]
  simp only [Real.rpow_add hz,Real.rpow_sub hz]
  ring

#print axioms actual_first_low_bin_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowFirstSum -/

/- BEGIN ORIGINAL MODULE Analytic.JointPacketFirstGates ; sha256 ba717daa41e3fcced2ec0a50e910de4f3ddd9c2488558402bcd60bc1be79bdf3 -/
section


/-! First projector and principal-support gates are inherited by every
literal packet subset. They do not need a separate population assumption. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ActualFirstSecondSource
variable {src : Input ι} {R seed : Ideal O} {Kfirst : ℝ}
  {radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ}
  {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

theorem packet_first_gates (x : Packet src R seed Kfirst radius side K Radius H) :
    Squarefree (row x).L ∧ (row x).E ∈
      (principalSupport Finset.univ (leftExponent (row x).first.val.1 (row x).first.val.2)
        (rightExponent (row x).first.val.1 (row x).first.val.2)).powerset :=
  ⟨(firstSourceOuterLabel src R seed Kfirst radius x.1.1).projector_squarefree
      x.1.2.1.val x.1.2.1.property,x.1.1.2.1.property⟩

theorem rayRows_first_gates (fallback : First src R seed Kfirst radius)
    (X : Finset (Packet src R seed Kfirst radius side K Radius H))
    (hzero : ∀ x∈X,(row x).z≠0) (χ ξ : RayCharacter)
    (q : NonzeroJointSourceRow (original src R seed) side)
    (hq : q∈rayRows fallback X hzero χ ξ) :
    Squarefree q.val.L ∧ q.val.E ∈ (principalSupport Finset.univ
      (leftExponent q.val.first.val.1 q.val.first.val.2)
      (rightExponent q.val.first.val.1 q.val.first.val.2)).powerset := by
  obtain ⟨x,hx,hχ,hξ,he⟩ := mem_rayRows_witness fallback X hzero χ ξ q hq
  exact (congrArg (fun v : ActualJointSourceRow (original src R seed) side =>
    Squarefree v.L ∧ v.E ∈ (principalSupport Finset.univ
      (leftExponent v.first.val.1 v.first.val.2)
      (rightExponent v.first.val.1 v.first.val.2)).powerset) he).mp (packet_first_gates x)

#print axioms rayRows_first_gates
end ActualFirstSecondSource
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointPacketFirstGates -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstBinLive ; sha256 ee89fb7419d9c71c464f6db148404016a38b960d620eab6b9d2bdafea043e169 -/
section


/-! Whole zero physical blocks are removed exactly before the joint packet
majorant. Every surviving dyadic fiber therefore carries the nonzero source
block needed to derive its two lower column dyads. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentCanonicalFirst CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

namespace ActualFirstSecondSource
variable (src : Input ι) (R seed : Ideal O) (Kfirst : ℝ)
  (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
  (side : Bool) (Z A M omega ξ : ℝ)
  (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
  (bin : NonzeroElement → Option κ) (b : κ)
  (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))

def liveBinRows (k : First src R seed Kfirst radius)
    (n : Blocks src R seed Kfirst radius side
      (mainScale src R seed Kfirst radius side Z A M omega)
      (mainRadius src R seed Kfirst radius side Z A M omega ξ)
      (mainHeight src R seed Kfirst radius side) k) : Finset O :=
  if activePhysicalRows (parent src R seed Kfirst radius side k) (t k)
    (columns src R seed Kfirst radius side k) (beta src R seed Kfirst radius side k) W
    (mainScale src R seed Kfirst radius side Z A M omega k)
    (mainRadius src R seed Kfirst radius side Z A M omega ξ k)
    (mainHeight src R seed Kfirst radius side k) n
    (binRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b k n)=0 then ∅
  else binRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b k n

theorem liveBinRows_gates (k : First src R seed Kfirst radius)
    (n : Blocks src R seed Kfirst radius side
      (mainScale src R seed Kfirst radius side Z A M omega)
      (mainRadius src R seed Kfirst radius side Z A M omega ξ)
      (mainHeight src R seed Kfirst radius side) k) (z : O)
    (hz : z∈liveBinRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W k n) :
    z∈binRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b k n ∧
    activePhysicalRows (parent src R seed Kfirst radius side k) (t k)
      (columns src R seed Kfirst radius side k) (beta src R seed Kfirst radius side k) W
      (mainScale src R seed Kfirst radius side Z A M omega k)
      (mainRadius src R seed Kfirst radius side Z A M omega ξ k)
      (mainHeight src R seed Kfirst radius side k) n
      (binRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b k n)≠0 := by
  unfold liveBinRows at hz
  split_ifs at hz with h
  · exact False.elim (Finset.notMem_empty z hz)
  · exact ⟨hz,h⟩

theorem binBlock_live_eq (k : First src R seed Kfirst radius) :
    firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k side Z A M omega ξ (t k) W bin b =
      actualSecondRowBlocks (parent src R seed Kfirst radius side k) (t k)
        (columns src R seed Kfirst radius side k) (beta src R seed Kfirst radius side k)
        W (mainScale src R seed Kfirst radius side Z A M omega k)
        (mainRadius src R seed Kfirst radius side Z A M omega ξ k)
        (mainHeight src R seed Kfirst radius side k)
        (liveBinRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W k) := by
  rw [binBlock_eq]
  unfold actualSecondRowBlocks
  apply Finset.sum_congr rfl
  intro n hn
  unfold liveBinRows
  split_ifs with h
  · rw [h]
    simp [activePhysicalRows,physicalBlock]
  · rfl

def liveBinPackets (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius)) :=
  packets src R seed Kfirst radius side
    (mainScale src R seed Kfirst radius side Z A M omega)
    (mainRadius src R seed Kfirst radius side Z A M omega ξ)
    (mainHeight src R seed Kfirst radius side) labels
    (liveBinRows src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W)

theorem liveBinPackets_nonzero
    (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (x : Packet src R seed Kfirst radius side
      (mainScale src R seed Kfirst radius side Z A M omega)
      (mainRadius src R seed Kfirst radius side Z A M omega ξ)
      (mainHeight src R seed Kfirst radius side))
    (hx : x∈liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels) :
    (row x).z≠0 := by
  have hm := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hx).2).2
  have hg := liveBinRows_gates src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W
    x.1 x.2.1 x.2.2 hm
  exact binRows_nonzero src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b x.1 x.2.1 x.2.2 hg.1

theorem actual_first_live_bin_packet_majorant (hZ : 0< Z)
    (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius)) (P : ℝ) (hP : 0< P) :
    (∑ k∈firstSideSourceLabels labels (firstSourceOuterLabel src R seed Kfirst radius)
      (fun _ => sourceRadius src) side,
      ‖firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k side
        Z A M omega ξ (t k) W bin b‖/(volume src.toData*P)) ≤
      ∑ x∈liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels,
        packetValue hs hz₁ hz₂ (volume src.toData) P t W x := by
  simp only [binBlock_live_eq]
  have hV : 0< volume src.toData :=
    mul_pos (mul_pos src.X₁_pos src.X₂_pos) (Finset.prod_pos (fun j _ => src.P_pos j))
  apply first_domain_majorant hs hz₁ hz₂ _ P hV hP t W labels _
  · intro k hk
    exact Real.rpow_pos_of_pos hZ _
  · intro k hk n z hz
    have hg := liveBinRows_gates src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W k n z hz
    exact binRows_nonzero src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b k n z hg.1

theorem actual_first_live_bin_joint_majorant (hZ : 0< Z)
    (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (P : ℝ) (hP : 0< P)
    (fallback : First src R seed Kfirst radius) :
    let K := mainScale src R seed Kfirst radius side Z A M omega
    let Radius := mainRadius src R seed Kfirst radius side Z A M omega ξ
    let H := mainHeight src R seed Kfirst radius side
    let X := liveBinPackets src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels
    let hzero := liveBinPackets_nonzero src R seed Kfirst radius side Z A M omega ξ hs hz₁ hz₂ bin b t W labels
    (∑ k∈firstSideSourceLabels labels (firstSourceOuterLabel src R seed Kfirst radius)
      (fun _ => sourceRadius src) side,
      ‖firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k side
        Z A M omega ξ (t k) W bin b‖/(volume src.toData*P)) ≤
      ∑ χ₁ : RayCharacter,∑ ξ₁ : RayCharacter,
      ∑ q∈rayRows fallback X hzero χ₁ ξ₁,
        ∑ n₁ : q.val.FirstDyadic Kfirst (radius q.val.first q.val.E) (sourceRadius src),
        ∑ n₂ : q.val.SecondDyadic (secondScale fallback K χ₁ ξ₁ q.val n₁)
          (secondScale fallback Radius χ₁ ξ₁ q.val n₁) (secondScale fallback H χ₁ ξ₁ q.val n₁),
        if (⟨q,n₁,n₂⟩ : FiberTarget fallback χ₁ ξ₁ K Radius H side)∈rayTarget fallback X hzero χ₁ ξ₁
        then fiberValue hs hz₁ hz₂ fallback χ₁ ξ₁ (volume src.toData) P t W ⟨q,n₁,n₂⟩ else 0 := by
  intro K Radius H X hzero
  apply (actual_first_live_bin_packet_majorant src R seed Kfirst radius side Z A M omega ξ
    hs hz₁ hz₂ bin b t W hZ labels P hP).trans_eq
  change (∑ x∈X,packetValue hs hz₁ hz₂ (volume src.toData) P t W x) = _
  rw [sum_ray_partition hs hz₁ hz₂ X (volume src.toData) P t W]
  apply Finset.sum_congr rfl
  intro χ₁ hχ₁
  apply Finset.sum_congr rfl
  intro ξ₁ hξ₁
  exact sum_ray_fibers hs hz₁ hz₂ fallback X hzero χ₁ ξ₁ (volume src.toData) P t W


end ActualFirstSecondSource
#print axioms ActualFirstSecondSource.actual_first_live_bin_joint_majorant
#print axioms ActualFirstSecondSource.binBlock_live_eq
#print axioms ActualFirstSecondSource.actual_first_live_bin_packet_majorant
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstBinLive -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstCommonSplit ; sha256 158f9a376bb699825ca49b07aa9b958967bfa7696b1ae98e1ca94f41ddce4828 -/
section





/-! The complete coherent second decomposition over the same literal
first domain used by amplification. The bin block applies to every bin,
and retains the original first character presentation on both sides. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalSource CenteredMomentSectorLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSourceSecondZeroEnergy
open CenteredMomentSupportedTailAggregate CenteredMomentCommonRadialData
open CenteredMomentSecondHeightFamily
open CenteredExceptionalProfile RayFourExpansion EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem actual_first_common_normalized_split
    (src : Input ι) (R seed : Ideal O) (hs : Squarefree seed)
    (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0)
    (Kfirst : ℝ) (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
    (left : Bool) (Z A M omega ξ : ℝ) (hZ : 0 < Z)
    (W : 𝓢(ℝ,ℂ)) (P : ℝ) (hP : 0 < P)
    (bin : HeckeInverseAmplification.NonzeroElement → Option κ)
    (Q : Ideal O) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hbin : ∀ w,bin w = none ↔ FixedInducingRow src.η Q fixedBadMask 1 w.val)
    (χ : RayCharacter) (m : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m) :
    let q := firstSourceOuterLabel src R seed Kfirst radius
    let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
    let Index := (i : FirstSourceOuterIndex src R seed Kfirst radius) × (q i).SourceIndex
    let child := fun k : Index => (q k.1).sourceChild k.2
    let columns := fun k : Index => commonSecondColumns (CenteredMomentAmplificationChildInput.original src R seed)
      ((q k.1).sideCommon left) ((q k.1).sideCommon_supported left)
    let β := fun k : Index => commonSecondBeta (CenteredMomentAmplificationChildInput.original src R seed)
      ((q k.1).sideCommon left) k.2.1.val
    let Kmain := fun k : Index => firstLowMainScale (q k.1) left Z A M omega
    let Tsec := fun k : Index => (sourceRadius src/((q k.1).sideCommon left).absNorm)^2/Kmain k
    let Hsource := fun k : Index => sourceRadius src/((q k.1).sideCommon left).absNorm
    ∀ t : Index → ℝ,
    (∑ k ∈ domain,(child k).sideEnergy left (t k) W (Kmain k)/
      (CenteredMomentExceptionalAmplitudePair.volume src.toData*P)) ≤
      (∑ k ∈ domain, ‖((Kmain k : ℂ)*paperRadialFourier W 0)*
        sourceSecondZero (columns k) (β k) ((child k).sideParent left) (t k)‖/
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*P)) +
      (∑ k ∈ domain, ‖partEnergy true ((child k).sideParent left) χ Q m (t k)
        (columns k) (β k) W (Kmain k) (Tsec k) Z ξ (Hsource k)‖/
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*P)) +
      (∑ b : κ, ∑ k ∈ domain, ‖firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k left
        Z A M omega ξ (t k) W bin b‖/(CenteredMomentExceptionalAmplitudePair.volume src.toData*P)) +
      (∑ k ∈ domain, ‖secondDiscardedEnergy ((child k).sideParent left) (t k)
        (columns k) (β k) W (Kmain k) (Tsec k) Z ξ‖/
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*P)) := by
  intro q domain Index child columns β Kmain Tsec Hsource t
  have hpoint (k : (i : FirstSourceOuterIndex src R seed Kfirst radius) × (q i).SourceIndex) :
      (child k).sideEnergy left (t k) W (Kmain k)/
        (CenteredMomentExceptionalAmplitudePair.volume src.toData*P) ≤
      ‖((Kmain k : ℂ)*paperRadialFourier W 0)*
        sourceSecondZero (columns k) (β k) ((child k).sideParent left) (t k)‖/
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*P) +
      ‖partEnergy true ((child k).sideParent left) χ Q m (t k)
        (columns k) (β k) W (Kmain k) (Tsec k) Z ξ (Hsource k)‖/
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*P) +
      (∑ b : κ, ‖firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k left
        Z A M omega ξ (t k) W bin b‖/(CenteredMomentExceptionalAmplitudePair.volume src.toData*P)) +
      ‖secondDiscardedEnergy ((child k).sideParent left) (t k)
        (columns k) (β k) W (Kmain k) (Tsec k) Z ξ‖/
          (CenteredMomentExceptionalAmplitudePair.volume src.toData*P) := by
    let F : FirstSidePresentation src.η :=
      ⟨(child k).C,(child k).D,(child k).hC,(child k).E,
        (child k).leftRay,(child k).rightRay,(child k).pair,left⟩
    have hparent : (child k).sideParent left = F.sourceParent := by cases left <;> rfl
    have hK : 0 < Kmain k := by dsimp [Kmain,firstLowMainScale]; exact Real.rpow_pos_of_pos hZ _
    have henergy : (child k).sideEnergy left (t k) W (Kmain k) =
        (commonEnergy (CenteredMomentAmplificationChildInput.original src R seed)
          ((q k.1).sideCommon left) ((q k.1).sideCommon_supported left)
          ((child k).sideParent left) (t k) k.2.1.val W (Kmain k)).re := by cases left <;> rfl
    rw [henergy]
    have hh := commonEnergy_normalized_bin_majorant src R seed ((q k.1).sideCommon left) k.2.1.val
      ((q k.1).sideCommon_supported left)
      (first_source_selected_seed src R seed hs hz₁ hz₂ Kfirst radius k.1 left)
      F ((child k).sideParent left) hparent bin Q hQ72 hbin χ m hm hmLam hm2
      (t k) W (Kmain k) (Tsec k) Z ξ (Hsource k) hK hz₁ hz₂ le_rfl P hP
    dsimp only at hh
    simp only [firstLowBinBlock,firstLowRadius_eq_second_frequency] at *
    simpa only [F,child,q,Kmain,Tsec,Hsource,columns,β,
      FirstJointLabel.sideParent,FirstSidePresentation.sourceParent,firstSideCharacter] using hh
  apply (Finset.sum_le_sum (fun k _ => hpoint k)).trans_eq
  simp only [Finset.sum_add_distrib]
  congr 2
  exact Finset.sum_comm

#print axioms actual_first_common_normalized_split
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstCommonSplit -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowFirstBins ; sha256 3e4637235e157ba4c2913fa8b1f727adbdb30e8f1f41631b5d77ad3554015a26 -/
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
local instance firstLowBinsFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
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
def actualLowBins (I : ℕ) (e : ℝ) : Finset (Fin (I+1) × Fin (I+1)) :=
  Finset.univ.filter (fun b => 51/100+(e/2)*(b.2.val : ℝ) ≤ 167/200)

theorem actual_first_low_bins_sum
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
    (ξconductor : ℝ) (hξconductor : 0 < ξconductor)
    (Bfirst LfirstRad Crfirst εouter : ℝ)
    (hBfirst : 0 ≤ Bfirst) (hLfirstRad : 0 ≤ LfirstRad)
    (hCrfirst : 0 < Crfirst) (hεouter : 0 < εouter) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
    ∀ (I : ℕ) (Wkernel : 𝓢(ℝ,ℂ)) (ν tailRows tailV lower tailSaving upper bplain₁ bplain₂ BRmask : ℝ)
      (Sbad : Finset (Ideal O)) (primeLoss Bsource Lrad Cr εsum : ℝ),
      0 < ν → ν < τ → 2*τ < d*ηheight → 0 ≤ tailRows → 0 < primeLoss → 0 ≤ Bsource → Bsource ≤ Bcommon →
      0 ≤ Lrad → 0 < Cr → 0 < εsum → Lrad+1 ≤ tailRows → Bfirst ≤ Bsource →
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
      src.η = ηfirst →
      ∀ (Rmask seed : Ideal O), Rmask ≠ 0 → ∀ hs : Squarefree seed, seed ≠ 0 →
      ∀ (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0),
      0 < sourceRadius src → sourceRadius src ≤ Z^Bfirst →
      ∀ (Kfirst : ℝ), 0 < Kfirst →
      ∀ radius : (v : Labels src Rmask seed) → Finset (CommonIndex v.val.1 v.val.2) → ℝ,
      (∀ v E,radius v E ≤ Crfirst*Z^LfirstRad) →
      let q := firstSourceOuterLabel src Rmask seed Kfirst radius
      ∀ (labels : Finset (FirstSourceOuterIndex src Rmask seed Kfirst radius)) (left : Bool)
        (psector A volumeLoss Mparent g omegaLoss ξ sourceLoss profileLoss clip refwidth : ℝ),
      (∀ i ∈ labels,((CenteredMomentRankinRadical.commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^psector) →
      Real.logb Z (sourceRadius src) ≤ A+sourceLoss →
      A+(7/2)*(∑ i,w i) ≤ Mparent+g → Real.logb Z (volume src.toData) ≤ A →
      A-volumeLoss ≤ Real.logb Z (volume src.toData) →
      (Fintype.card α : ℝ)*Real.logb Z (max 1 src.upper) ≤ profileLoss →
      0 ≤ g → g ≤ 1/241 → 0 ≤ omegaLoss → 0 ≤ profileLoss → 0 ≤ clip →
      Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      let pad := 2*sourceLoss+parentLoss+ξ/2+Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))
      0 ≤ pad → pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 1/2000000 →
      Mparent+pad ≤ Mcap → Mparent+pad+Bmask+ξconductor ≤ d → A+sourceLoss ≤ Bcommon →
      (∀ i ∈ labels,
        let c := Real.logb Z (((q i).sideCommon left).absNorm : ℝ);
        let d₁ := Real.logb Z (((q i).sideCommon (!left)).absNorm : ℝ);
        -2*c+(q i).activeWidth Z+(q i).punctureWidth Z ≤ refwidth ∧
        lower ≤ δcommon+(Mparent-max (c-d₁) 0-6*(3/500)-omegaLoss-Bsource)+(3/500)-1/48000 ∧
        firstLowRadius (q i) left (sourceRadius src) Z A Mparent omegaLoss ξ ≤ Cr*Z^Lrad) →
      let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
      ∀ (t : ((i : FirstSourceOuterIndex src Rmask seed Kfirst radius) × (q i).SourceIndex) → ℝ),
      (∀ k ∈ domain, |t k| ≤ Z^ν) →
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
      ∀ (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ x,‖src.W₁ x‖ ≤ B₁) → (∀ x,‖src.W₂ x‖ ≤ B₂) → A ≤ tailV →
      src.upper ≤ upper → src.b₁ ≤ bplain₁ → src.b₂ ≤ bplain₂ →
      (Rmask.absNorm : ℝ) ≤ Z^BRmask → height ≤ Z^ν →
      let smallLoss := (BRmask+Bcommon)*εmask+ν*(degree : ℝ)
      Bsource ≤ tailSaving+smallLoss →
      let aSource := (∏ i,loInput i)*a*a
      let Elow := lowFixedCoefficient (ι := α) Cbound Mslot upper bplain₁ bplain₂ p S degree
      let Eabs := 2*128^(Fintype.card α+2)*Mslot^Fintype.card α*B₁*B₂*
        (max 1 upper)^Fintype.card α*max 1 bplain₁*max 1 bplain₂
      (∑ bidx ∈ actualLowBins I e, ∑ k ∈ domain,
        ‖firstLowBinBlock src Rmask seed hs hz₁ hz₂ Kfirst radius k left
          Z A Mparent omegaLoss ξ (t k) Wkernel bin bidx‖ /
          (volume src.toData*actualHighPrimeCount M H Sbad Z)) ≤
        ((I+1 : ℕ)^2 : ℝ)*(Csum*(Ckernel*Elow/aSource+Ckernel*(128/aSource)*Eabs^2))*
          Z^(psector+A+refwidth+δcommon-1/48000+smallLoss+primeLoss+εsum+volumeLoss+εouter)/
          (seed.absNorm : ℝ) := by
  obtain ⟨degree,S,hmain⟩ := actual_first_low_bin_sum M H hH W
    aslot bslot a b Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon ηfirst parentLoss hparentLoss ξconductor hξconductor
    Bfirst LfirstRad Crfirst εouter hBfirst hLfirstRad hCrfirst hεouter
  refine ⟨degree,S,?_⟩
  intro I Wkernel ν tailRows tailV lower tailSaving upper bplain₁ bplain₂ BRmask Sbad primeLoss Bsource Lrad Cr εsum
    hν hgap hheightBudget htailRows hprimeLoss hBsource hBcommonSource hLrad hCr hεsum htailRowsCap hBfirstSource
  obtain ⟨Nkernel,Ckernel,Csum,hCkernel,hCsum,hmain⟩ := hmain I Wkernel ν tailRows tailV lower tailSaving
    upper bplain₁ bplain₂ BRmask Sbad primeLoss Bsource Lrad Cr εsum
    hν hgap hheightBudget htailRows hprimeLoss hBsource hBcommonSource hLrad hCr hεsum htailRowsCap hBfirstSource
  refine ⟨Nkernel,Ckernel,Csum,hCkernel,hCsum,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hmain] with Z hmain
  intro hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ hη Rmask seed hR hs hs0 hz₁ hz₂ hsource₀ hsource
    Kfirst hKfirst radius hr q labels left psector A volumeLoss Mparent g omegaLoss ξ sourceLoss profileLoss clip refwidth
    hrad hsourceLog hcapacity hvolume hvolumeLower hprofile hg hgCap homega hprofile0 hclip hclipCost
    pad hpad hbudgetSource hMparentCap hMparentConductor hcommonBudget hgeometry domain t ht
    bin hbinNone hbins B₁ B₂ hB₁ hB₂ hW₁ hW₂ hAtail
    hupper hbplain₁ hbplain₂ hRN hhSmall smallLoss htailSaving aSource Elow Eabs
  let target := psector+A+refwidth+δcommon-1/48000+smallLoss+primeLoss+εsum+volumeLoss+εouter
  let coefficient := Csum*(Ckernel*Elow/aSource+Ckernel*(128/aSource)*Eabs^2)
  have hElow : 0 ≤ Elow := low_fixed_coefficient_nonneg Cbound Mslot upper bplain₁ bplain₂ p S degree hCbound.le
  have haSource : 0 < aSource := by
    dsimp only [aSource]
    have hlo (i : α) : 0 < loInput i := by rw [←hloInput i]; exact src.lo_pos i
    exact mul_pos (mul_pos (Finset.prod_pos (fun i _ => hlo i)) ha) ha
  have hcoefficient : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have hpoint (bidx) (hbidx : bidx ∈ actualLowBins I e) :
      (∑ k ∈ domain,
        ‖firstLowBinBlock src Rmask seed hs hz₁ hz₂ Kfirst radius k left
          Z A Mparent omegaLoss ξ (t k) Wkernel bin bidx‖ /
          (volume src.toData*actualHighPrimeCount M H Sbad Z)) ≤
      coefficient*Z^target/(seed.absNorm : ℝ) := by
    exact hmain hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
      hloInput hhiInput hX₁ hX₂ hY₁ hY₂ hη Rmask seed hR hs hs0 hz₁ hz₂ hsource₀ hsource
      Kfirst hKfirst radius hr labels left psector A volumeLoss Mparent g omegaLoss ξ sourceLoss profileLoss clip refwidth
      hrad hsourceLog hcapacity hvolume hvolumeLower hprofile hg hgCap homega hprofile0 hclip hclipCost
      hpad hbudgetSource hMparentCap hMparentConductor hcommonBudget hgeometry t ht
      bin hbinNone hbins bidx (Finset.mem_filter.mp hbidx).2 B₁ B₂ hB₁ hB₂ hW₁ hW₂ hAtail
      hupper hbplain₁ hbplain₂ hRN hhSmall htailSaving
  have hcard : ((actualLowBins I e).card : ℝ) ≤ ((I+1 : ℕ)^2 : ℝ) := by
    exact_mod_cast (show (actualLowBins I e).card ≤ (I+1)^2 by
      calc
        _ ≤ Fintype.card (Fin (I+1) × Fin (I+1)) := Finset.card_le_univ _
        _ = _ := by simp [pow_two])
  calc
    _ ≤ ∑ _bidx ∈ actualLowBins I e,coefficient*Z^target/(seed.absNorm : ℝ) := Finset.sum_le_sum hpoint
    _ = ((actualLowBins I e).card : ℝ)*(coefficient*Z^target/(seed.absNorm : ℝ)) := by simp
    _ ≤ ((I+1 : ℕ)^2 : ℝ)*(coefficient*Z^target/(seed.absNorm : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

#print axioms actual_first_low_bins_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowFirstBins -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstBinClasses ; sha256 22c17daf01522eb6fdd00cb99eab47aa81d8d8258c74f0784d409c2decb00f8d -/
section



/-! The common classifier exhausts the genuine low and high bins.
Unoccupied bins above the initialized zero edge contribute exactly zero. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve HeckeInverseAmplification
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

def actualHighBins (I : ℕ) (e : ℝ) : Finset (Fin (I+1) × Fin (I+1)) :=
  Finset.univ.filter (fun b => 167/200 < 51/100+(e/2)*(b.2.val : ℝ) ∧
    51/100+(e/2)*(b.2.val : ℝ) ≤ 7/8)

theorem actualHighBins_delta {I : ℕ} {e : ℝ} (b : Fin (I+1) × Fin (I+1))
    (hb : b ∈ actualHighBins I e) :
    67/100 ≤ 2*(51/100+(e/2)*(b.2.val : ℝ))-1 ∧
      2*(51/100+(e/2)*(b.2.val : ℝ))-1 ≤ 3/4 := by
  obtain ⟨_,hlo,hhi⟩ := Finset.mem_filter.mp hb
  constructor <;> linarith

theorem FirstSidePresentation.sourceBin_ne_of_empty {ι κ : Type*} [Fintype ι]
    {η : Character} (F : FirstSidePresentation η) (s : CommonSecondKernelLabel ι)
    (bin : NonzeroElement → Option κ) (b : κ) (hempty : ∀ w,bin w ≠ some b) (z : O) :
    F.sourceBin s bin z ≠ some b := by
  unfold FirstSidePresentation.sourceBin
  split_ifs with hz
  · exact hempty _
  · simp

theorem actualSecondRowBlocks_empty (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K R H : ℝ) :
    actualSecondRowBlocks η t S β W K R H (fun _ => ∅) = 0 := by
  simp only [actualSecondRowBlocks,activePhysicalRows,physicalBlock,Finset.sum_empty,mul_zero,
    Finset.sum_const_zero]

theorem firstLowBinBlock_zero_of_empty {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (src : Input ι) (R seed : Ideal O) (hs : Squarefree seed)
    (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0)
    (Kfirst : ℝ) (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (k : (i : FirstSourceOuterIndex src R seed Kfirst radius) ×
      (firstSourceOuterLabel src R seed Kfirst radius i).SourceIndex)
    (left : Bool) (Z A M omega ξ t : ℝ) (W : 𝓢(ℝ,ℂ))
    (bin : NonzeroElement → Option κ) (b : κ) (hempty : ∀ w,bin w ≠ some b) :
    firstLowBinBlock src R seed hs hz₁ hz₂ Kfirst radius k left Z A M omega ξ t W bin b = 0 := by
  have hfilter (F : FirstSidePresentation src.η) (s : CommonSecondKernelLabel ι) (rows : Finset O) :
      rows.filter (fun z => F.sourceBin s bin z = some b) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    exact fun z _ => F.sourceBin_ne_of_empty s bin b hempty z
  unfold firstLowBinBlock
  dsimp only
  simp only [hfilter,actualSecondRowBlocks_empty]

theorem sum_actual_low_high_bins (I : ℕ) (e : ℝ)
    (f : (Fin (I+1) × Fin (I+1)) → ℝ)
    (hzero : ∀ b, 7/8 < 51/100+(e/2)*(b.2.val : ℝ) → f b = 0) :
    (∑ b,f b) = (∑ b ∈ actualLowBins I e,f b)+(∑ b ∈ actualHighBins I e,f b) := by
  simp only [actualLowBins,actualHighBins,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hlo : 51/100+(e/2)*(b.2.val : ℝ) ≤ 167/200
  · have hn : ¬167/200 < 51/100+(e/2)*(b.2.val : ℝ) := not_lt.mpr hlo
    simp [hlo,hn]
  · have hl := lt_of_not_ge hlo
    by_cases hhi : 51/100+(e/2)*(b.2.val : ℝ) ≤ 7/8
    · simp [hlo,hl,hhi]
    · simp [hlo,hhi,hzero b (lt_of_not_ge hhi)]

#print axioms firstLowBinBlock_zero_of_empty
#print axioms sum_actual_low_high_bins
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstBinClasses -/
