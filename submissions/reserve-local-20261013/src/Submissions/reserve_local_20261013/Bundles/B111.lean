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
import Submissions.local44_20261013.Bundles.B001
import Submissions.reserve_local_20261013.Bundles.B016
import Submissions.reserve_local_20261013.Bundles.B070
import Submissions.reserve_local_20261013.Bundles.B071
import Submissions.reserve_local_20261013.Bundles.B082
import Submissions.reserve_local_20261013.Bundles.B108
import Submissions.reserve_local_20261013.Bundles.B109
import Submissions.reserve_local_20261013.Bundles.B110

/- BEGIN ORIGINAL MODULE Analytic.JointGlobalSourceBins ; sha256 f6917ba956ab78614e0c92e610b5391f21539dc4e01e7a4248a7dc7e808383fe -/
section



/-! A single finite classifier is chosen on all nonzero rows. It handles
the exceptional part exactly and works simultaneously for every source
puncture and every subsequent allocation. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDetectorZeros HeckePrimeRay HeckeInverseAmplification
open HeckeFiniteDeletion LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance globalSourceBinsFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem exists_global_original_source_bins
    {Slot : Type*} [Fintype Slot] [Nonempty Slot] (e : ℝ) (he : 0 < e)
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ I : ℕ, 0 < I ∧ ∀ (η η₀ : Character) (Q : Ideal O)
      (hQ72 : Q ≤ Ideal.span {(72:O)}) (hQM : Q ≤ M) (hQη₀ : Q ≤ η₀.modulus)
      (T : ℝ), 2 < T →
    ∃ bin : NonzeroElement → Option (Fin (I+1) × Fin (I+1)),
      (∀ w,bin w = none ↔ FixedInducingRow η Q fixedBadMask 1 w.val) ∧
      (∀ w b,bin w = some b → 1 ≤ b.1.val ∧
        51/100 ≤ 51/100+(e/2)*(b.2.val : ℝ) ∧
        51/100+(e/2)*(b.2.val : ℝ) ≤ 7/8 ∧
        (∀ (R : JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
          (hR : ∀ label,R label ≠ 0),
          jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH (fun _ : Slot => η₀))
            Q hQ72 (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀) Q hQM
              (fun _ => hQη₀)) R hR
            (51/100+(e/2)*(b.2.val : ℝ)) (51/100+(e/2)*(b.2.val : ℝ)+e)
            ((3*(b.1.val+1):ℕ)*T) w)) := by
  obtain ⟨I,hI⟩ := exists_nat_gt (max 1 ((49/100:ℝ)/(e/2)))
  have hIpos : 0 < I := by
    have hh := (le_max_left (1:ℝ) ((49/100:ℝ)/(e/2))).trans_lt hI
    exact_mod_cast (zero_lt_one.trans hh)
  have hwidth : (49/100:ℝ) ≤ I*(e/2) :=
    (div_le_iff₀ (by positivity)).mp ((le_max_right _ _).trans hI.le)
  refine ⟨I,hIpos,?_⟩
  intro η η₀ Q hQ72 hQM hQη₀ T hT
  let Rows := {w : NonzeroElement // ¬FixedInducingRow η Q fixedBadMask 1 w.val}
  obtain ⟨f,hf⟩ := exists_common_anchor_source_bins (Slot := Slot) M H hH η η₀ Q
    hQ72 hQM hQη₀ (fun w : Rows => w.val) (fun w => w.property) T e hT he I hIpos hwidth hβupper
  let bin : NonzeroElement → Option (Fin (I+1) × Fin (I+1)) := fun w =>
    if h : FixedInducingRow η Q fixedBadMask 1 w.val then none else some (f ⟨w,h⟩)
  refine ⟨bin,?_,?_⟩
  · intro w
    by_cases h : FixedInducingRow η Q fixedBadMask 1 w.val <;> simp [bin,h]
  · intro w b hb
    by_cases h : FixedInducingRow η Q fixedBadMask 1 w.val
    · simp [bin,h] at hb
    · have hb' : f ⟨w,h⟩ = b := by simpa [bin,h] using hb
      obtain ⟨hi,ha,hupper,_,hsource,_⟩ := hf ⟨w,h⟩
      rw [←hb']
      exact ⟨hi,ha,hupper,hsource⟩

#print axioms exists_global_original_source_bins
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointGlobalSourceBins -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowLocalTarget ; sha256 96a8911efe92ab8acc1faad34a5e3a7af099016d1db2a8e253276861911bf346 -/
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
local instance lowLocalTargetFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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
/-- The genuine low-bin first target in the local length window. All
analytic loss parameters and profile constants precede the live scale. -/
theorem actual_local_first_low_target
    (W : ℝ → ℂ) (aslot bslot a b lo hi Mslot upper bplain₁ bplain₂ BRmask : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b)
    (hMslot : 0 ≤ Mslot) (hBRmask : 0 ≤ BRmask)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (loInput hiInput : α → ℝ) (hloInput : ∀ i,0 < loInput i)
    (ηfirst : Character) (profile : Profiles a b) (Wkernel : 𝓢(ℝ,ℂ))
    (Sbad : Finset (Ideal O)) (I : ℕ) (e τ : ℝ)
    (he : 0 < e) (hecap : e ≤ lowLocalBinCap (Fintype.card α))
    (hτ : 0 < τ) (hτcap : τ ≤ 1/8)
    (LfirstRad Crfirst : ℝ) (hLfirstRad : 0 ≤ LfirstRad) (hCrfirst : 0 < Crfirst) :
    ∃ ν : ℝ, 0 < ν ∧ ν < τ ∧
    ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      ∀ hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)},
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ lowLocalMesh) →
      (∀ i,lo ≤ σ i) → (∀ i,σ i ≤ hi) →
      0 ≤ height → height ≤ Z^ν → (∀ i,|freq i| ≤ height) →
    ∀ (src : Input α), Matches M H hH src η₀ θ w σ freq W bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      profile.profile 0 = src.W₁ → profile.profile 1 = src.W₂ →
      (∀ i,src.lo i = loInput i) → (∀ i,src.hi i = hiInput i) →
      (∀ i,|src.hi i| ≤ upper) → src.upper ≤ upper →
      |src.b₁| ≤ bplain₁ → |src.b₂| ≤ bplain₂ → src.η = ηfirst →
      Real.logb Z src.X₁ ≤ 423/1000 → Real.logb Z src.X₂ ≤ 423/1000 →
      Real.logb Z src.Y₁ ≤ 1 → Real.logb Z src.Y₂ ≤ 1 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z src.X₁) (Real.logb Z src.X₂) (∑ i,w i) →
    ∀ (Rmask seed : Ideal O), Rmask ≠ 0 → (Rmask.absNorm : ℝ) ≤ Z^BRmask →
    ∀ hs : Squarefree seed, seed ≠ 0 →
    ∀ (hz₁ : src.W₁ 0 = 0) (hz₂ : src.W₂ 0 = 0), 0 < sourceRadius src →
    ∀ Kfirst : ℝ, 0 < Kfirst →
    ∀ radius : (v : Labels src Rmask seed) → Finset (CommonIndex v.val.1 v.val.2) → ℝ,
      (∀ v E,radius v E ≤ Crfirst*Z^LfirstRad) →
    let q := firstSourceOuterLabel src Rmask seed Kfirst radius
    ∀ (labels : Finset (FirstSourceOuterIndex src Rmask seed Kfirst radius))
      (ref : FirstJointLabel α) (left : Bool) (omega ξ : ℝ),
      0 ≤ omega → omega ≤ lowLocalTiny → 0 ≤ ξ → ξ ≤ lowLocalTiny →
      (∀ i ∈ labels,
        (q i).radicalWidth Z ≤ ref.radicalWidth Z+lowLocalTiny ∧
        ref.sideWidth left Z ≤ (q i).sideWidth left Z+lowLocalTiny ∧
        (q i).activeWidth Z ≤ ref.activeWidth Z+lowLocalTiny ∧
        (q i).punctureWidth Z ≤ ref.punctureWidth Z+lowLocalTiny) →
    let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
    ∀ (t : ((i : FirstSourceOuterIndex src Rmask seed Kfirst radius) × (q i).SourceIndex) → ℝ),
      (∀ k ∈ domain,|t k| ≤ Z^ν) →
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
    (∑ bidx ∈ actualLowBins I e, ∑ k ∈ domain,
      ‖firstLowBinBlock src Rmask seed hs hz₁ hz₂ Kfirst radius k left
        Z (Real.logb Z (volume src.toData)) 1 omega ξ (t k) Wkernel bin bidx‖ /
        (volume src.toData*actualHighPrimeCount M H Sbad Z)) ≤
      (C/(seed.absNorm : ℝ))* (1/((ref.sideCommon left).absNorm : ℝ))*
        Z^(ref.sideTargetWidth left Z (Real.logb Z (volume src.toData))-1/50000) := by
  have ht : 0 < lowLocalTiny := by norm_num [lowLocalTiny]
  obtain ⟨hmesh,hmeshInc,hmeshWidth,hmeshLoss,heCap,hεslot,hedata⟩ :=
    low_local_parameter_choices (Fintype.card α)
  obtain ⟨heSmall,hκ,hbudget⟩ := hedata e he hecap
  let εmask := lowLocalTiny/(BRmask+2)
  have hεmask : 0 < εmask := by dsimp only [εmask]; positivity
  obtain ⟨degree,S,hmain⟩ := actual_first_low_bins_sum M H hH W
    aslot bslot a b 0 1 lo hi 2 (lowLocalTiny/4) haslot hWs hW hbslot
    ha haUpper hb (by norm_num) (by norm_num) (by norm_num) (by positivity) hbeta hbetaTop
    1 2 τ (lowLocalSlotLoss (Fintype.card α)) e (lowLocalSlotLoss (Fintype.card α)/4) 1 lowLocalTiny
    (by norm_num) (by norm_num) hτ hεslot he heSmall hκ (by norm_num) (by simpa using hbudget)
    lowLocalMesh hmesh hmeshInc (by simpa only [mul_one] using hmeshWidth) hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput 1 lowLocalTiny (by norm_num) ht ηfirst lowLocalTiny ht lowLocalTiny ht
    1 LfirstRad Crfirst lowLocalTiny (by norm_num) hLfirstRad hCrfirst ht
  let ν := min (τ/2) (lowLocalTiny/(degree+1))
  have hν : 0 < ν := lt_min (by positivity) (by positivity)
  have hντ : ν < τ := (min_le_left _ _).trans_lt (by linarith)
  have hνdegree : ν*(degree : ℝ) ≤ lowLocalTiny := by
    have hh := (le_div_iff₀ (show (0:ℝ) < degree+1 by positivity)).mp (min_le_right (τ/2) (lowLocalTiny/(degree+1)))
    nlinarith
  obtain ⟨Nkernel,Ckernel,Csum,hCkernel,hCsum,hmain⟩ := hmain I Wkernel ν 3 1 (-2) 2
    upper bplain₁ bplain₂ BRmask Sbad lowLocalTiny 1 2 1 lowLocalTiny
    hν hντ (by norm_num; linarith) (by norm_num) ht (by norm_num) le_rfl (by norm_num)
    (by norm_num) ht (by norm_num) le_rfl
  refine ⟨ν,hν,hντ,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  let B₁ := SchwartzMap.seminorm ℝ 0 0 (profile.profile 0)
  let B₂ := SchwartzMap.seminorm ℝ 0 0 (profile.profile 1)
  have hB₁ : 0 ≤ B₁ := apply_nonneg _ _
  have hB₂ : 0 ≤ B₂ := apply_nonneg _ _
  let aSource := (∏ i,loInput i)*a*a
  have haSource : 0 < aSource := mul_pos (mul_pos (Finset.prod_pos (fun i _ => hloInput i)) ha) ha
  let Elow := lowFixedCoefficient (ι := α) Cbound Mslot upper bplain₁ bplain₂ profile S degree
  have hElow : 0 ≤ Elow := low_fixed_coefficient_nonneg Cbound Mslot upper bplain₁ bplain₂ profile S degree hCbound.le
  let Eabs := 2*128^(Fintype.card α+2)*Mslot^Fintype.card α*B₁*B₂*
    (max 1 upper)^Fintype.card α*max 1 bplain₁*max 1 bplain₂
  let C := ((I+1 : ℕ)^2 : ℝ)*(Csum*(Ckernel*Elow/aSource+Ckernel*(128/aSource)*Eabs^2))
  have hC : 0 ≤ C := by dsimp only [C,Eabs]; positivity
  refine ⟨C+1,by positivity,?_⟩
  filter_upwards [hmain,eventually_low_fixed_profile_gates (ι := α) upper bplain₁ bplain₂ b lowLocalTiny ht]
    with Z hmain hfixed
  intro hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hhSmall hfreq src hmatch hhi hMs hp₁ hp₂
    hlo hhiInput hhiAbs hupper hb₁ hb₂ hη hn₁ hn₂ hm₁ hm₂ hz hcap Rmask seed hR hRN hs hs0 hz₁ hz₂
    hsource₀ Kfirst hKfirst radius hr q labels ref left omega ξ homega homegaCap hξ hξcap hsector domain t htSource
    bin hbinNone hbins
  let A := Real.logb Z (volume src.toData)
  let n₁ := Real.logb Z src.X₁
  let n₂ := Real.logb Z src.X₂
  let g := max (n₁+n₂+(9/2)*(∑ i,w i)-1) 0
  have hAeq : A = n₁+n₂+∑ i,w i := original_volume_log src Z w hZ hmatch.scale
  obtain ⟨hA,hcapacity,hg,hgCap⟩ := local_capacity_of_volume Z n₁ n₂ (∑ i,w i) A hAeq hn₁ hn₂ hz hcap
  obtain ⟨hsourceLog,hprofile⟩ := hfixed.2.1 src hsource₀ hhiAbs hb₁ hb₂ hupper
  have hsource : sourceRadius src ≤ Z^(1:ℝ) := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hsource₀).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num [lowLocalTiny] at hsourceLog ⊢; linarith only [hsourceLog,hA])
  have hsourceA : sourceRadius src ≤ Z^(A+lowLocalTiny) := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hsource₀).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le hsourceLog
  obtain ⟨hpad,hbudgetSource,hMcap,hconductor,hsmall⟩ := low_local_live_budgets omega ξ
    (Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ)))
    homega homegaCap hξ hξcap hfixed.2.2.2.1 hfixed.2.2.2.2
  let refwidth := -2*ref.sideWidth left Z+ref.activeWidth Z+ref.punctureWidth Z+4*lowLocalTiny
  have hrad (i) (hi : i ∈ labels) :
      ((CenteredMomentRankinRadical.commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤
        Z^(ref.radicalWidth Z+lowLocalTiny) := by
    have hN := CenteredMomentFirstScale.norm_pos _
      (CenteredMomentRankinRadical.commonRadical_ne_zero i.1.val.1 i.1.val.2)
    calc
      _ = Z^((q i).radicalWidth Z) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hN).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (hsector i hi).1
  have hgeometry (i) (hi : i ∈ labels) :
      let c := Real.logb Z (((q i).sideCommon left).absNorm : ℝ);
      let d₁ := Real.logb Z (((q i).sideCommon (!left)).absNorm : ℝ);
      -2*c+(q i).activeWidth Z+(q i).punctureWidth Z ≤ refwidth ∧
      -2 ≤ lowLocalTiny+(1-max (c-d₁) 0-6*(3/500)-omega-1)+(3/500)-1/45000 ∧
      firstLowRadius (q i) left (sourceRadius src) Z A 1 omega ξ ≤ 1*Z^(2:ℝ) := by
    dsimp only
    have hgates := actual_common_gates src Rmask seed hs hz₁ hz₂ i.1.val.1 i.1.val.2 i.1.property
    have hsideCap (side : Bool) : ((q i).sideCommon side).absNorm ≤ (Z^(1:ℝ)) := by
      cases side
      · exact hgates.2.2.2.2.2.2.trans hsource
      · exact hgates.2.2.2.2.2.1.trans hsource
    have hwidth (side : Bool) : 0 ≤ (q i).sideWidth side Z ∧ (q i).sideWidth side Z ≤ 1 := by
      have hn : (1:ℝ) ≤ ((q i).sideCommon side).absNorm := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Ideal.absNorm_eq_zero_iff.not.mpr ((q i).sideCommon_supported side).1)
      refine ⟨Real.logb_nonneg hZ hn,?_⟩
      have hh := Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le hn) (hsideCap side)
      simpa only [FirstJointLabel.sideWidth,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
    have hmax : max ((q i).sideWidth left Z-(q i).sideWidth (!left) Z) 0 ≤ 1 :=
      max_le (by linarith [(hwidth left).2,(hwidth (!left)).1]) (by norm_num)
    refine ⟨?_,?_,?_⟩
    · change -2*(q i).sideWidth left Z+(q i).activeWidth Z+(q i).punctureWidth Z ≤ refwidth
      dsimp only [refwidth]
      linarith [(hsector i hi).2.1,(hsector i hi).2.2.1,(hsector i hi).2.2.2]
    · change -2 ≤ lowLocalTiny+(1-max ((q i).sideWidth left Z-(q i).sideWidth (!left) Z) 0-
        6*(3/500)-omega-1)+(3/500)-1/45000
      norm_num [lowLocalTiny] at homegaCap ⊢
      linarith
    · simpa only [one_mul] using firstLowRadius_fixed_cap (q i) left (sourceRadius src) Z A
        lowLocalTiny omega ξ hZ hsource₀.le hsourceA homega hsmall
  have hmaskSmall : (BRmask+1)*εmask ≤ lowLocalTiny := by
    dsimp only [εmask]
    apply (le_of_eq (by ring : (BRmask+1)*(lowLocalTiny/(BRmask+2)) =
      lowLocalTiny*((BRmask+1)/(BRmask+2)))).trans
    exact (mul_le_mul_of_nonneg_left ((div_le_one (by linarith)).mpr (by linarith)) ht.le).trans_eq (mul_one _)
  have hsmallLoss : (BRmask+1)*εmask+ν*(degree : ℝ) ≤ 2*lowLocalTiny := by linarith
  have hsmallLoss0 : 0 ≤ (BRmask+1)*εmask+ν*(degree : ℝ) := by positivity
  have hbound := hmain hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq profile src hmatch hhi hMs hp₁ hp₂
    hlo hhiInput (plain_scale_le_base src.X₁ Z src.X₁_pos hZ hn₁)
    (plain_scale_le_base src.X₂ Z src.X₂_pos hZ hn₂)
    (plain_scale_le_base_of_log_le_one src.Y₁ Z src.Y₁_pos hZ hm₁)
    (plain_scale_le_base_of_log_le_one src.Y₂ Z src.Y₂_pos hZ hm₂) hη Rmask seed hR hs hs0 hz₁ hz₂ hsource₀ hsource
    Kfirst hKfirst radius hr labels left (ref.radicalWidth Z+lowLocalTiny) A 0 1 g omega ξ
    lowLocalTiny lowLocalTiny lowLocalTiny refwidth hrad hsourceLog hcapacity le_rfl (by simp only [sub_zero]; exact le_rfl)
    hprofile hg hgCap homega ht.le ht.le hfixed.2.2.1 hpad hbudgetSource hMcap hconductor
    (by norm_num [lowLocalTiny]; linarith only [hA]) hgeometry t htSource bin hbinNone hbins
    B₁ B₂ hB₁ hB₂ (fun x => by rw [←hp₁]; exact SchwartzMap.norm_le_seminorm ℝ _ x)
    (fun x => by rw [←hp₂]; exact SchwartzMap.norm_le_seminorm ℝ _ x)
    (by linarith) hupper ((le_abs_self _).trans hb₁) ((le_abs_self _).trans hb₂) hRN hhSmall (by linarith)
  change _ ≤ C*Z^((ref.radicalWidth Z+lowLocalTiny)+A+refwidth+lowLocalTiny-1/45000+
    ((BRmask+1)*εmask+ν*(degree : ℝ))+lowLocalTiny+lowLocalTiny+0+lowLocalTiny)/(seed.absNorm : ℝ) at hbound
  have hallow : 0 ≤ ref.sideAllowance left Z := by
    cases left
    · exact (ref.target_auxiliary_widths_nonneg Z hZ).2.2.2.2
    · exact (ref.target_auxiliary_widths_nonneg Z hZ).2.2.2.1
  have htarget : (ref.radicalWidth Z+lowLocalTiny)+A+refwidth+lowLocalTiny-1/45000+
      ((BRmask+1)*εmask+ν*(degree : ℝ))+lowLocalTiny+lowLocalTiny+0+lowLocalTiny ≤
      ref.radicalWidth Z+A-2*ref.sideWidth left Z+ref.activeWidth Z+ref.punctureWidth Z+
        ref.sideAllowance left Z-1/50000 := by
    dsimp only [refwidth]
    norm_num [lowLocalTiny] at hsmallLoss ⊢
    linarith
  apply hbound.trans
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le htarget
  have hh := div_le_div_of_nonneg_right (mul_le_mul (by linarith : C ≤ C+1) hpow
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by positivity : 0 ≤ C+1)) (Nat.cast_nonneg seed.absNorm)
  apply hh.trans_eq
  have heq := ref.side_target_power left Z A (C+1) (-1/50000) hZ
  have h := congrArg (fun x : ℝ => x/(seed.absNorm : ℝ)) heq
  dsimp only [A] at h ⊢
  convert h using 1 <;> ring

#print axioms actual_local_first_low_target
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowLocalTarget -/

/- BEGIN ORIGINAL MODULE Analytic.JointOriginalComparisonActual ; sha256 f69397a63d72b4351867605119add387a22ea21cd1c2fd544af85cfd0ade662f -/
section




set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceLowBands CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot QuadraticInitialBound CenteredMomentFiniteProfileExceptional
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance originalComparisonActualFinite : Finite (O⧸M):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

/-- The comparison term for a fixed parent is supplied by the incumbent proof.
The new local window enters only through the direct/reflected comparison geometry. -/
theorem actual_local_comparison_energy
    (Wslot:ℝ→ℂ)(aslot bslot lo hi a b bΦ Bmask ε:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)
    (hcSlot:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hBmask:0≤ Bmask)(hε:0<ε)
    (hbeta:51/100≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8):
    ∃mesh:ℝ,0< mesh ∧ ∃J:ℕ,∃U:Finset (ℕ×ℕ),
    ∀ηfirst η₀:Character,∀Q:Ideal O,Q≤ M → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
      internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) →
      ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀ →
        s.character=ηfirst → s.rowWidth=1 →
        s.characterWidth=Real.logb Z (ηfirst.modulus.absNorm:ℝ) →
      ∀W₁ W₂:𝓢(ℝ,ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
        Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,1≤ X₁ → 1≤ X₂ → X₁≤ Z^(1/4:ℝ) → X₂≤ Z^(3/5:ℝ) →
      (∑i,w i)≤37/1000 →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(1+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxicap,hL,hLcap,hpower⟩:=
    local_comparison_power_from_low (α:=α) M H hH Wslot aslot bslot lo hi
      haslot hsSlot hcSlot.continuous a b bΦ (1/10) (ε/2) 2 Bmask
      ha hlo hhi hbΦ (by norm_num) (by positivity) (by norm_num) hBmask (by norm_num)
  obtain ⟨degree,S,hinc⟩:=actual_incumbent_pair (α:=α) M H hH Wslot
    aslot bslot a b bΦ Bmask L lo hi 2 (ε/2) haslot hsSlot hcSlot hbslot
    ha hlo hhi hbΦ hBmask (by norm_num) (by positivity) hbeta hbetaTop
  obtain ⟨J,U,Cpower,hCp,hpower⟩:=hpower degree S
  let mesh:=Cycle25.Energy.commonMesh 2 Bmask L (ε/2)
  have hmesh:0< mesh:=Cycle25.Energy.commonMesh_pos 2 Bmask L (ε/2)
    (by norm_num) hBmask (by positivity)
  refine ⟨mesh,hmesh,J,U,?_⟩
  intro ηfirst η₀ Q hQM hQzero hQtop hQ72
  obtain ⟨Czero,K,hCzero,hK,hinc⟩:=hinc η₀ Q hQM hQzero hQtop hQ72
  have hη:0<(ηfirst.modulus.absNorm:ℝ):=
    CenteredMomentFirstScale.norm_pos _ ηfirst.modulus_ne_bot
  refine ⟨Cpower*(K+1)*(ηfirst.modulus.absNorm:ℝ),by positivity,?_⟩
  filter_upwards [hpower,hinc,eventually_fixed_logb_le (ηfirst.modulus.absNorm:ℝ) (1/100) hη (by norm_num)]
    with Z hp hiZ hfixed
  refine ⟨hp.1,?_⟩
  intro θ w σ freq t height hw hwmesh hσlo hσhi hh hf s hQ hchar hrow hwidth
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hslots
  have hslo:1≤ s.width:=by
    unfold NaturalState.width
    rw [hrow]
    linarith [s.character_nonneg]
  have hshi:s.width≤101/100:=by
    unfold NaturalState.width
    rw [hrow,hwidth]
    linarith [hfixed.2]
  have hlow:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L mesh lo hi
      2 (ε/2) (3/4) Z η₀ Q degree S K:=by
    intro T θ w σ v t height hw hwL hσlo hσhi hh hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity _
    exact hiZ.2.2 T θ w σ v t height hw hwL hσlo hσhi hh hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity
  have hbound:=hp.2 (ε/2) mesh (3/4) η₀ Q K (by positivity) hK.le hlow
    θ w σ freq t height hw hwmesh hσlo hσhi hh hf rfl
    s hQ hslo hshi (by linarith) W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hslots
  have hz:0< Z:=zero_lt_one.trans hp.1
  have hpow:Z^(s.width+ε/2+ε/2)=(ηfirst.modulus.absNorm:ℝ)*Z^(1+ε):=by
    have he:s.width+ε/2+ε/2=Real.logb Z (ηfirst.modulus.absNorm:ℝ)+(1+ε):=by
      unfold NaturalState.width
      rw [hrow,hwidth]
      ring
    rw [he,Real.rpow_add hz,Real.rpow_logb hz hp.1.ne' hη]
  apply hbound.trans_eq
  rw [hpow]
  ring

#print axioms actual_local_comparison_energy
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointOriginalComparisonActual -/

/- BEGIN ORIGINAL MODULE Analytic.JointPacketPhysical ; sha256 1ff4bb1dd32c04a2f0222007b4f41a06c129ed74e15554db4a2a6e7f3da15a6a -/
section



/-! The canonical physical block at an actual packet is the literal source
block, including its original first presentation and both dyadic indices. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
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
open NonzeroJointSourceRow
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ActualFirstSecondSource
variable {src : Input ι} {R seed : Ideal O} {Kfirst : ℝ}
  {radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ}
  {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

theorem lifted_physicalBlock_eq
    (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (fallback : First src R seed Kfirst radius)
    (rowDefault : NonzeroJointSourceRow (original src R seed) side)
    (χ ξ : RayCharacter) (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
    (x : Packet src R seed Kfirst radius side K Radius H)
    (hχ : x.1.2.2.1=χ) (hξ : x.1.2.2.2=ξ) (hz : (row x).z≠0) (rows : Finset O) :
    let y := liftPacket fallback χ ξ x hχ hξ hz
    let s := sourceKernel src R seed side hs hz₁ hz₂ rowDefault src.η χ ξ⁻¹ 1 1 y.1.label
    physicalBlock s.parent (t (firstAt fallback y.1.val χ ξ y.2.1))
      s.toKernelLabel.columns s.toKernelLabel.beta s.second.val.1 s.second.val.2
      s.toKernelLabel.hC s.toKernelLabel.hD s.partition
      (secondScale fallback Radius χ ξ y.1.val y.2.1) rows W
      (secondScale fallback K χ ξ y.1.val y.2.1) (fun j => (y.2.2 j : ℤ)) =
    activePhysicalRows (parent src R seed Kfirst radius side x.1) (t x.1)
      (columns src R seed Kfirst radius side x.1) (beta src R seed Kfirst radius side x.1)
      W (K x.1) (Radius x.1) (H x.1) x.2.1 rows := by
  subst χ; subst ξ
  have he : sourceKernel src R seed side hs hz₁ hz₂ rowDefault src.η
      x.1.2.2.1 x.1.2.2.2⁻¹ 1 1 (label ⟨row x,hz⟩) = packetLabel hs hz₁ hz₂ x := by
    simp only [sourceKernel,recover_label]
    rfl
  dsimp only [liftPacket]
  rw [he]
  simp only [secondScale,firstAt_packet]
  rfl


theorem rayTarget_physical
    (hs : Squarefree seed) (hz₁ : src.W₁ 0=0) (hz₂ : src.W₂ 0=0)
    (fallback : First src R seed Kfirst radius)
    (rowDefault : NonzeroJointSourceRow (original src R seed) side)
    (X : Finset (Packet src R seed Kfirst radius side K Radius H))
    (hzero : ∀ x∈X,(row x).z≠0) (χ ξ : RayCharacter)
    (t : First src R seed Kfirst radius → ℝ) (W : 𝓢(ℝ,ℂ))
    (hphysical : ∀ x∈X, ∃ rows : Finset O,
      activePhysicalRows (parent src R seed Kfirst radius side x.1) (t x.1)
        (columns src R seed Kfirst radius side x.1) (beta src R seed Kfirst radius side x.1)
        W (K x.1) (Radius x.1) (H x.1) x.2.1 rows ≠ 0)
    (y : FiberTarget fallback χ ξ K Radius H side)
    (hy : y∈rayTarget fallback X hzero χ ξ) :
    let s := sourceKernel src R seed side hs hz₁ hz₂ rowDefault src.η χ ξ⁻¹ 1 1 y.1.label
    ∃ rows : Finset O, physicalBlock s.parent (t (firstAt fallback y.1.val χ ξ y.2.1))
      s.toKernelLabel.columns s.toKernelLabel.beta s.second.val.1 s.second.val.2
      s.toKernelLabel.hC s.toKernelLabel.hD s.partition
      (secondScale fallback Radius χ ξ y.1.val y.2.1) rows W
      (secondScale fallback K χ ξ y.1.val y.2.1) (fun j => (y.2.2 j : ℤ)) ≠ 0 := by
  obtain ⟨x,hx,hχ,hξ,hz,rfl⟩ := mem_rayTarget_witness fallback X hzero χ ξ y hy
  obtain ⟨rows,hr⟩ := hphysical x hx
  exact ⟨rows,by rw [lifted_physicalBlock_eq hs hz₁ hz₂ fallback rowDefault χ ξ t W x hχ hξ hz rows]; exact hr⟩

#print axioms rayTarget_physical

#print axioms lifted_physicalBlock_eq
end ActualFirstSecondSource
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointPacketPhysical -/

/- BEGIN ORIGINAL MODULE Analytic.JointUniformMesh ; sha256 313fe1faa046938c780063ef733775efb92f28bd6898779192b1709268a945e7 -/
section



/-! An explicit admissible mesh independent of the finite slot type. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Local44.Analytic
noncomputable section

/-- The local mesh depends only on the puncture exponent and requested loss. -/
def meshGuaranteed (Bmask ε : ℝ) : ℝ :=
  min (Cycle25.Energy.commonMesh 2 Bmask (Bmask+3) (ε/2)) lowLocalMesh

lemma meshGuaranteed_pos (Bmask ε : ℝ) (hBmask : 0 ≤ Bmask) (hε : 0 < ε) :
    0 < meshGuaranteed Bmask ε :=
  lt_min (Cycle25.Energy.commonMesh_pos 2 Bmask (Bmask+3) (ε/2)
    (by norm_num) hBmask (by positivity)) (low_local_parameter_choices 0).1

lemma meshGuaranteed_le_lowLocalMesh (Bmask ε : ℝ) :
    meshGuaranteed Bmask ε ≤ lowLocalMesh := min_le_right _ _

lemma meshGuaranteed_le_comparison (Bmask ε L : ℝ)
    (hBmask : 0 ≤ Bmask) (hε : 0 < ε) (hL : L ≤ Bmask+3) :
    meshGuaranteed Bmask ε ≤ Cycle25.Energy.commonMesh 2 Bmask L (ε/2) :=
  (min_le_left _ _).trans (Cycle25.Energy.commonMesh_antitone_L 2 Bmask L (Bmask+3) (ε/2)
    (by norm_num) hBmask (by positivity) hL)

#print axioms meshGuaranteed_pos
#print axioms meshGuaranteed_le_comparison
end
end OAI.SevenEighths.Local44.Analytic
end
/- END ORIGINAL MODULE Analytic.JointUniformMesh -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalLocalTarget ; sha256 0f300e3e8cf11bfee74bfb87f31ba8ccf30d908661bedeca13553b535a072953 -/
section



/-! The coherent exceptional first target in the local length window.
All loss parameters, profile constants and the allowed height exponent
are fixed before the live source and arithmetic labels. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstScale CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildInput
open CenteredMomentRankinRadical CenteredMomentFirstMixedAllowance
open CenteredMomentSecondBlockAggregate CenteredMomentSecondEnergySplit
open CenteredMomentSecondExceptionalSourceFamily RayFourExpansion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance coherentExceptionalLocalDecidableSum : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def firstCoherentExceptionalPart
    (src : Input ι) (R seed : Ideal O) (Kfirst : ℝ)
    (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (k : (i : FirstSourceOuterIndex src R seed Kfirst radius) ×
      (firstSourceOuterLabel src R seed Kfirst radius i).SourceIndex)
    (left : Bool) (Z A omega ξ t : ℝ) (W : 𝓢(ℝ,ℂ)) (χ : RayCharacter) (Q : Ideal O) (m : O) : ℂ :=
  let q := firstSourceOuterLabel src R seed Kfirst radius k.1
  let v := q.sourceChild k.2
  let Kmain := firstLowMainScale q left Z A 1 omega
  let Hsource := sourceRadius src/((q.sideCommon left).absNorm : ℝ)
  partEnergy true (v.sideParent left) χ Q m t
    (commonSecondColumns (original src R seed) (q.sideCommon left) (q.sideCommon_supported left))
    (commonSecondBeta (original src R seed) (q.sideCommon left) k.2.1.val)
    W Kmain (Hsource^2/Kmain) Z ξ Hsource

theorem actual_local_first_coherent_exceptional_target
    (Mpool : Ideal O) [NeZero Mpool] (Hpool : Subgroup (O ⧸ Mpool)ˣ)
    (hHpool : RayOrthogonality.globalUnits Mpool ≤ Hpool)
    (Sbad : Finset (Ideal O))
    (a b Mslot upper bplain₁ bplain₂ BRmask τ Lfirst Crfirst : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hMslot : 0 ≤ Mslot) (hBRmask : 0 ≤ BRmask)
    (hτ : 0 < τ) (hLfirst : 0 ≤ Lfirst) (hCrfirst : 0 < Crfirst)
    (lo hi : ι → ℝ) (hlo : ∀ i,0 < lo i)
    (ηfirst : Character) (profile : Profiles a b) (W : 𝓢(ℝ,ℂ)) :
    ∃ ν : ℝ, 0 < ν ∧ ν < τ ∧
    ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72:O)} →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ (src : Input ι) (w : ι → ℝ),
      (∀ i,0 ≤ w i) → (∀ i,src.P i = Z^(w i)) →
      (∀ i,src.lo i = lo i) → (∀ i,src.hi i = hi i) →
      (∀ i,src.M i ≤ Mslot) → src.upper ≤ upper →
      (∀ i,|src.hi i| ≤ upper) → |src.b₁| ≤ bplain₁ → |src.b₂| ≤ bplain₂ →
      src.W₁ = profile.profile 0 → src.W₂ = profile.profile 1 → src.η = ηfirst →
      0 < sourceRadius src →
      Real.logb Z src.X₁ ≤ 423/1000 → Real.logb Z src.X₂ ≤ 423/1000 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z src.X₁) (Real.logb Z src.X₂) (∑ i,w i) →
      Z^(1/4:ℝ) ≤ src.X₁ → Z^(1/4:ℝ) ≤ src.X₂ →
      Z^(1/4:ℝ) ≤ src.Y₁ → Z^(1/4:ℝ) ≤ src.Y₂ →
    ∀ (R seed : Ideal O), R ≠ 0 → (R.absNorm : ℝ) ≤ Z^BRmask →
      Squarefree seed → seed ≠ 0 →
    ∀ radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
      (∀ p E,radius p E ≤ Crfirst*Z^Lfirst) →
    let q := firstSourceOuterLabel src R seed Z radius
    ∀ (labels : Finset (FirstSourceOuterIndex src R seed Z radius))
      (ref : FirstJointLabel ι) (left : Bool) (omega ξ : ℝ),
      0 ≤ omega → omega ≤ 1/1000 → 0 ≤ ξ → ξ ≤ 1/1000 →
      (∀ i ∈ labels,
        (q i).radicalWidth Z ≤ ref.radicalWidth Z+1/10000 ∧
        -2*(q i).sideWidth left Z+(q i).activeWidth Z+(q i).punctureWidth Z+(q i).sideAllowance left Z ≤
          -2*ref.sideWidth left Z+ref.activeWidth Z+ref.punctureWidth Z+ref.sideAllowance left Z+1/10000) →
    let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
    ∀ (t : ((i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex) → ℝ),
      (∀ k ∈ domain,|t k| ≤ Z^ν) →
    ∀ (χ : RayCharacter) (m : O), m ≠ 0 → goodLambda ∣ m → (2:O) ∣ m →
    (∑ k ∈ domain,
      ‖firstCoherentExceptionalPart src R seed Z radius k left Z
        (Real.logb Z (volume src.toData)) omega ξ (t k) W χ Q m‖/
        (volume src.toData*actualHighPrimeCount Mpool Hpool Sbad Z)) ≤
      (C/(seed.absNorm : ℝ))*(1/((ref.sideCommon left).absNorm : ℝ))*
        Z^(ref.sideTargetWidth left Z (Real.logb Z (volume src.toData))-1/100) := by
  obtain ⟨J,S,hS,Cbound,hCbound,hmain⟩ := actual_first_coherent_exceptional_sum a b ha hb lo hi
    (1/10000) (1/10000) (1/10000) (BRmask+8) 1 2 1 (1/10000)
    Lfirst Crfirst (1/10000) (by norm_num) (by norm_num) (by norm_num) (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hLfirst hCrfirst (by norm_num) W
  let ν := min (τ/2) (1/(10000*(2*(J:ℝ)+1)))
  have hν : 0 < ν := lt_min (by positivity) (by positivity)
  have hντ : ν < τ := (min_le_left _ _).trans_lt (by linarith)
  have hνJ : (2*J:ℝ)*ν ≤ 1/10000 := by
    have hh := (le_div_iff₀ (show (0:ℝ) < 10000*(2*(J:ℝ)+1) by positivity)).mp
      (min_le_right (τ/2) (1/(10000*(2*(J:ℝ)+1))))
    nlinarith
  refine ⟨ν,hν,hντ,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hmain⟩ := hmain Q hQ hQt hQ72
  let slotBound := ((128*max 1 upper)^Fintype.card ι)^2*((max 1 upper)^Fintype.card ι)^2*
    (Mslot^Fintype.card ι)^6
  let aSource := (∏ i,lo i)*a*a
  have haSource : 0 < aSource := mul_pos (mul_pos (Finset.prod_pos (fun i _ => hlo i)) ha) ha
  let profileBound := K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (1+2*Real.pi)^(4*J)*profile.control S^2*slotBound*(2:ℝ)^(2*J)
  let parentCost := (ηfirst.modulus.absNorm : ℝ)*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm
  let fixedConductor := 4*(1296*fixedPresentationCost*(ηfirst.modulus.absNorm : ℝ)*
    (CenteredMomentSecondRadicalBudget.fixedFactor : ℝ)*
    (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm)
  let C := Cbound*profileBound*aSource^(-2/3:ℝ)*parentCost
  have hC : 0 ≤ C := by dsimp only [C,profileBound,slotBound,parentCost]; positivity
  refine ⟨C+1,by positivity,?_⟩
  filter_upwards [hmain,eventually_low_fixed_profile_gates (ι := ι) upper bplain₁ bplain₂ b (1/1000) (by norm_num),
    eventually_actual_high_prime_ratio Mpool Hpool hHpool Sbad (1/10000) (by norm_num),
    eventually_ge_atTop (max 2 fixedConductor)] with Z hmain hfixed hprime hfixedConductor
  intro hZ src w hw hscale hloSrc hhiSrc hMs hupper hhiAbs hb₁ hb₂ hp₁ hp₂ hη hsource₀
    hn₁ hn₂ hwSum hcapacity hX₁ hX₂ hY₁ hY₂ R seed hR hRcap hs hs0 radius hr
    q labels ref left omega ξ homega homegaCap hξ hξcap hsector domain t ht χ m hm hmLam hm2
  have hz := zero_lt_one.trans hZ
  let A := Real.logb Z (volume src.toData)
  have hvol : volume src.toData = Z^A := (Real.rpow_logb hz hZ.ne' (volume_pos src.toData)).symm
  have hAeq := original_volume_log src Z w hZ hscale
  have hA := (local_capacity_of_volume Z (Real.logb Z src.X₁) (Real.logb Z src.X₂) (∑ i,w i) A
    hAeq hn₁ hn₂ hwSum hcapacity).1
  have hsourceLog := (hfixed.2.1 src hsource₀ hhiAbs hb₁ hb₂ hupper).1
  have hsourceA : sourceRadius src ≤ Z^(A+1/1000) := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) := (Real.rpow_logb hz hZ.ne' hsource₀).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le hsourceLog
  have hsource : sourceRadius src ≤ Z^(1:ℝ) :=
    hsourceA.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  have hsourceZ : sourceRadius src ≤ Z := by simpa using hsource
  have hzero₁ : src.W₁ 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt ha) (profile.support 0 (by simpa only [←hp₁,Function.mem_support] using hh)).1
  have hzero₂ : src.W₂ 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt ha) (profile.support 1 (by simpa only [←hp₂,Function.mem_support] using hh)).1
  have hpScale (i) : 1 ≤ src.P i := by rw [hscale]; exact Real.one_le_rpow hZ.le (hw i)
  have hwidth : (1:ℝ) ≤ Real.logb Z Z+Real.logb Z (src.η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost := by
    have hηone : (1:ℝ) ≤ src.η.modulus.absNorm := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
    have hηlog := Real.logb_nonneg hZ hηone
    have hflog := Real.logb_nonneg hZ coherent_exceptional_fixed_presentation_one
    rw [Real.logb_self_eq_one hZ]
    linarith
  have hprimeInv : 1/actualHighPrimeCount Mpool Hpool Sbad Z ≤ Z^(-(3/500:ℝ)+1/10000) := by
    apply (div_le_iff₀ hprime.2.1).mpr
    have hh := (div_le_iff₀ hprime.2.1).mp hprime.2.2
    have h := div_le_div_of_nonneg_right hh (Real.rpow_nonneg hz.le (3/500))
    rw [div_self (Real.rpow_pos_of_pos hz _).ne'] at h
    convert h using 1
    rw [Real.rpow_add hz,Real.rpow_neg hz.le]
    ring
  let p := ref.radicalWidth Z+1/10000
  let refwidth := -2*ref.sideWidth left Z+ref.activeWidth Z+ref.punctureWidth Z+ref.sideAllowance left Z+1/10000
  have hrad (i) (hi : i ∈ labels) :
      ((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^p := by
    have hn := CenteredMomentFirstScale.norm_pos _ (commonRadical_ne_zero i.1.val.1 i.1.val.2)
    calc
      _ = Z^((q i).radicalWidth Z) := (Real.rpow_logb hz hZ.ne' hn).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (hsector i hi).1
  have href (i) (hi : i ∈ labels) :
      -2*Real.logb Z (((q i).sideCommon left).absNorm : ℝ)+(q i).activeWidth Z+(q i).punctureWidth Z+
        allowance ((q i).sideCommon left) ((q i).sideCommon (!left)) Z ≤ refwidth := by
    have h := (hsector i hi).2
    cases left
    · simpa only [refwidth,FirstJointLabel.sideWidth,FirstJointLabel.sideCommon,FirstJointLabel.sideAllowance,
        Bool.false_eq_true,ite_false,ite_true,Bool.not_false,(q i).allowances_eq Z] using h
    · exact h
  let v := fun k : (i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex => (q k.1).sourceChild k.2
  let Kmain := fun k : (i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex => firstLowMainScale (q k.1) left Z A 1 omega
  let Hsource := fun k : (i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex => sourceRadius src/(((q k.1).sideCommon left).absNorm : ℝ)
  let Tsec := fun k : (i : FirstSourceOuterIndex src R seed Z radius) × (q i).SourceIndex => Hsource k^2/Kmain k
  have hKmain (k) : 0 < Kmain k := by dsimp [Kmain,firstLowMainScale]; positivity
  have hgeom (k) (hk : k ∈ domain) : frequencyRadius (Tsec k) Z ξ ≤ 1*Z^(2:ℝ) ∧
      Hsource k ≤ Z^(1:ℝ) ∧
      (expandedFactor ((v k).sideCharacter left) : ℝ)*R.absNorm*(sourceRadius src)^2*
        (4*frequencyRadius (Tsec k) Z ξ) ≤ Z^(BRmask+8) := by
    have hg := actual_common_gates src R seed hs hzero₁ hzero₂ k.1.1.val.1 k.1.1.val.2 k.1.1.property
    have hCcap : ((q k.1).C.absNorm : ℝ) ≤ Z := hg.2.2.2.2.2.1.trans hsourceZ
    have hNC : (1:ℝ) ≤ ((q k.1).sideCommon left).absNorm := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ((q k.1).sideCommon_supported left).1)
    have hradius : frequencyRadius (Tsec k) Z ξ ≤ Z^(2:ℝ) :=
      firstLowRadius_fixed_cap (q k.1) left (sourceRadius src) Z A (1/1000) omega ξ hZ hsource₀.le hsourceA homega (by linarith)
    refine ⟨by simpa using hradius,(div_le_self hsource₀.le hNC).trans hsource,?_⟩
    have hfactor := first_side_expanded_factor_cap (v k) left
    have hparent : (v k).parent = ηfirst := hη
    rw [hparent] at hfactor
    have hfix : fixedConductor ≤ Z := (le_max_right _ _).trans hfixedConductor
    have hfpos := fixedPresentationCost_pos
    have hfc : 0 ≤ fixedConductor := by dsimp [fixedConductor]; positivity
    have hradius0 : 0 ≤ frequencyRadius (Tsec k) Z ξ := by
      have hkpos := hKmain k
      dsimp only [frequencyRadius,Tsec]
      positivity
    calc
      _ ≤ (fixedConductor/4*Z^2)*Z^BRmask*Z^2*(4*Z^(2:ℝ)) := by
        have hh : (expandedFactor ((v k).sideCharacter left) : ℝ) ≤ fixedConductor/4*Z^2 := by
          apply hfactor.trans
          have hc : ((v k).C.absNorm : ℝ) ≤ Z := hCcap
          have hs : ((v k).C.absNorm : ℝ)^2 ≤ Z^2 := pow_le_pow_left₀ (by positivity) hc 2
          have hh := mul_le_mul_of_nonneg_left hs
            (show 0 ≤ 1296*fixedPresentationCost*(ηfirst.modulus.absNorm : ℝ)*
              (CenteredMomentSecondRadicalBudget.fixedFactor : ℝ)*
              (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm by positivity)
          convert hh using 1 <;> dsimp only [fixedConductor] <;> ring
        gcongr
      _ = fixedConductor*Z^(BRmask+6) := by
        rw [show (6:ℝ)=2+2+2 by norm_num]
        simp only [Real.rpow_add hz,Real.rpow_two]
        ring
      _ ≤ Z*Z^(BRmask+6) := mul_le_mul_of_nonneg_right hfix (by positivity)
      _ = Z^(BRmask+7) := by rw [show BRmask+7 = 1+(BRmask+6) by ring,Real.rpow_add hz 1 (BRmask+6),Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hKcap (k) (hk : k ∈ domain) : Kmain k ≤ mainCommonRadius Z
      (Real.logb Z (((v k).sideCommon (!left)).absNorm : ℝ))
      (nominalLog ((v k).sideCommon left) ((v k).sideCommon (!left))
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex ((v k).sideCommon left) ((v k).sideCommon (!left)) => P.val)
          ((v k).sideSubset left)}) Z (volume src.toData) Z)
      (Real.logb Z (((v k).sideCommon left).absNorm : ℝ)) (9/500) omega 0 := by
    have heq : Kmain k = firstLowMainScale (v k) left Z A 1 omega := by
      cases left <;> rfl
    rw [heq,(v k).sideSubset_generator,hvol]
    simpa only [Real.rpow_one,FirstJointLabel.sideWidth] using (firstLowMainScale_actual_radius (v k) left Z A 1 omega hZ).le
  have hbound := hmain.2 src profile hloSrc hhiSrc hpScale hp₁ hp₂ hsource₀ hsource R seed hR hs hs0
    Z 1 A omega (1/10000) (Z^ν) hz le_rfl (by positivity) hwidth hvol (by linarith)
    hX₁ hX₂ hY₁ hY₂ radius hr labels left p refwidth hrad href (fun _ => χ) (fun _ => m)
    t Kmain Tsec (fun _ => ξ) Hsource (fun _ => actualHighPrimeCount Mpool Hpool Sbad Z)
    (fun _ _ => ⟨hm,hmLam,hm2⟩) (fun k hk => ⟨ht k hk,hKmain k,hprime.2.1,hprimeInv⟩) hgeom hKcap
  have hslot := coherent_exceptional_slot_fixed src Mslot upper hMslot hMs hupper
  have hprof0 : coherentExceptionalProfile S src profile J Q K 0 ≤ profileBound/(2:ℝ)^(2*J) := by
    rw [coherentExceptionalProfile_exact]
    simp only [abs_zero,add_zero,one_pow,mul_one]
    dsimp only [profileBound]
    rw [mul_div_cancel_right₀ _ (by positivity)]
    calc
      _ = (K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*profile.control S^2)*
        (slotControl src.toData^2*frozenProfile src^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hslot (by positivity)
  have hprof : coherentExceptionalProfile S src profile J Q K (Z^ν) ≤ profileBound*Z^((2*J:ℝ)*ν) := by
    have hh := coherentExceptionalProfile_height_power S src profile J Q K (Z^ν) Z ν 1 hK.le hZ.le hν.le (by norm_num)
      (by rw [abs_of_pos (Real.rpow_pos_of_pos hz _)];simp)
    apply hh.trans
    norm_num only [one_add_one_eq_two] at ⊢
    have hh' := mul_le_mul_of_nonneg_right hprof0 (show (0:ℝ) ≤ (2:ℝ)^(2*J)*Z^((2*J:ℝ)*ν) by positivity)
    convert hh' using 1 <;> field_simp
  have halower : originalLowerProfile src a a = aSource := by
    dsimp only [originalLowerProfile,aSource]
    simp_rw [hloSrc]
  rw [halower,hη] at hbound
  have htarget : p+A+refwidth-93/1000+5*omega/6+(1/10000)+2*(1/10000)+(1/10000)+2*1*(1/10000)+(1/10000)+(1/10000)+(2*J:ℝ)*ν ≤
      ref.radicalWidth Z+A-2*ref.sideWidth left Z+ref.activeWidth Z+ref.punctureWidth Z+ref.sideAllowance left Z-1/100 := by
    dsimp only [p,refwidth]
    linarith
  have hh : (∑ k ∈ domain, ‖firstCoherentExceptionalPart src R seed Z radius k left Z A omega ξ (t k) W χ Q m‖/
      (volume src.toData*actualHighPrimeCount Mpool Hpool Sbad Z)) ≤
      C*Z^(p+A+refwidth-93/1000+5*omega/6+(1/10000)+2*(1/10000)+(1/10000)+2*1*(1/10000)+(1/10000)+(1/10000)+(2*J:ℝ)*ν)/(seed.absNorm : ℝ) := by
    apply hbound.trans
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprof hCbound)
      (show 0 ≤ aSource^(-2/3:ℝ)*parentCost*
        Z^(p+A+refwidth-93/1000+5*omega/6+(1/10000)+2*(1/10000)+(1/10000)+2*1*(1/10000)+(1/10000)+(1/10000))/(seed.absNorm : ℝ) by
        dsimp only [parentCost];positivity)
    convert hh using 1 <;> dsimp only [C,parentCost] <;> rw [Real.rpow_add hz] <;> ring
  apply hh.trans
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le htarget
  have hh := div_le_div_of_nonneg_right (mul_le_mul (by linarith : C ≤ C+1) hpow
    (Real.rpow_nonneg hz.le _) (by positivity : 0 ≤ C+1)) (Nat.cast_nonneg seed.absNorm)
  apply hh.trans_eq
  have heq := ref.side_target_power left Z A (C+1) (-1/100) hZ
  have heq' := congrArg (fun x : ℝ => x/(seed.absNorm : ℝ)) heq
  dsimp only [A] at heq' ⊢
  convert heq' using 1 <;> ring

#print axioms actual_local_first_coherent_exceptional_target
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalLocalTarget -/
