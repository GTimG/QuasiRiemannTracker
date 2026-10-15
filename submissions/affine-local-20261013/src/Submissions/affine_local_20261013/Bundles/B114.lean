/-
Affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 at tracker revision 2c3df3b.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below.
Affine-capacity adaptation: the source module hashes below identify the
pre-adaptation provenance, not the modified declarations in this file. -/
import Submissions.local44_20261013.Bundles.B001
import Submissions.local44_20261013.Bundles.B007
import Submissions.affine_local_20261013.Bundles.B028
import Submissions.affine_local_20261013.Bundles.B082
import Submissions.affine_local_20261013.Bundles.B102
import Submissions.affine_local_20261013.Bundles.B103
import Submissions.affine_local_20261013.Bundles.B106
import Submissions.affine_local_20261013.Bundles.B112
import Submissions.affine_local_20261013.Bundles.B113

/- BEGIN ORIGINAL MODULE Analytic.JointLocalErrorParameters ; sha256 9f94610c1deec11bec4036c0ca42a411ce161540c7b5c237c81c4633029c227a -/
section



/-! Fixed admissible loss parameters for the actual extracted errors. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic

def errorLocalEps (BR : ℝ) : ℝ := 1/(10000000*(BR+9))
def errorLocalMask (BR : ℝ) : ℝ := lowLocalTiny/(4*(BR+9))

lemma error_local_parameters (BR : ℝ) (hBR : 0 ≤ BR) :
    0 < errorLocalEps BR ∧ 0 < errorLocalMask BR ∧
    errorLocalEps BR ≤ 1/1000 ∧
    (∀ j, CenteredMomentEnergyFirstGaussianProfileWeights.losses
      (errorLocalEps BR) (errorLocalEps BR) (errorLocalEps BR) (BR+8) j ≤ 1/10000) ∧
    (∀ ξ : ℝ, ξ ≤ lowLocalTiny →
      CenteredMomentFirstSecondInputGates.exponent 1 3 BR 4 1 ξ ≤ BR+8) ∧
    (∀ delta reserve mesh : ℝ, delta+reserve ≤ lowLocalTiny → mesh ≤ lowLocalTiny/4 →
      ((BR+8)+(BR+8))*errorLocalMask BR+lowLocalTiny/4+lowLocalTiny/4+
        (delta+reserve+lowLocalTiny/4)/6+lowLocalTiny/3+(3/4)*mesh ≤ 1/10000) := by
  have hden : 0 < 10000000*(BR+9) := by positivity
  have he : 0 < errorLocalEps BR := by unfold errorLocalEps; positivity
  have hm : 0 < errorLocalMask BR := by unfold errorLocalMask lowLocalTiny; positivity
  have heq : (10000000*(BR+9))*errorLocalEps BR = 1 := by
    unfold errorLocalEps
    field_simp
  have hem : errorLocalEps BR ≤ 1/10000000 := by nlinarith
  have hmask : (2*(BR+8))*errorLocalMask BR ≤ lowLocalTiny/2 := by
    dsimp only [errorLocalMask]
    apply (le_of_eq (by field_simp; ring : 2*(BR+8)*(lowLocalTiny/(4*(BR+9))) =
      (lowLocalTiny/2)*((BR+8)/(BR+9)))).trans
    apply (mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).mpr (by linarith))
      (by norm_num [lowLocalTiny] : 0 ≤ lowLocalTiny/2)).trans_eq
    ring
  refine ⟨he,hm,by linarith,?_,?_,?_⟩
  · intro j
    fin_cases j <;> norm_num [CenteredMomentEnergyFirstGaussianProfileWeights.losses]
    · linarith
    · nlinarith
  · intro ξ hξ
    unfold CenteredMomentFirstSecondInputGates.exponent
    norm_num [lowLocalTiny] at hξ
    apply max_le
    · linarith
    · apply max_le
      · linarith
      · apply max_le <;> linarith
  · intro delta reserve mesh hsum hmesh
    norm_num [lowLocalTiny] at hmask hsum hmesh ⊢
    nlinarith

lemma error_local_declared_capacity (n₁ n₂ z q : ℝ)
    (hz : z ≤ 37/1000) (hcap : localRegion n₁ n₂ z) (hq : 0 ≤ q) :
    n₁+n₂+6*(3/4)*z ≤ max (n₁+n₂+(9/2)*z) (1+q) ∧
    1+q ≤ max (n₁+n₂+(9/2)*z) (1+q) ∧
    max (n₁+n₂+(9/2)*z) (1+q)-(1+q) ≤ 37/10000 := by
  refine ⟨by convert le_max_left (n₁+n₂+(9/2)*z) (1+q) using 1 <;> ring,le_max_right _ _,?_⟩
  apply (sub_le_iff_le_add).mpr
  apply max_le <;> linarith [hcap.2]

#print axioms error_local_parameters
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLocalErrorParameters -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowLiteralTarget ; sha256 c76ba55a7b83f1f8e1b323a7ea8f2ca015f01665305f0a3730b826bb486a7081 -/
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
local instance lowLiteralTargetFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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
theorem actual_literal_first_low_target
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
    (ξamp reserve ξsecond : ℝ) (hξamp : 0 < ξamp) (hreserve : 0 ≤ reserve)
    (hamp : ξamp+reserve ≤ lowLocalTiny) (hξsecond : 0 ≤ ξsecond)
    (hξsecondCap : ξsecond ≤ lowLocalTiny) :
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
    ∀ Kfirst : ℝ, 1 ≤ Kfirst →
    let radius := actualLowFirstRadius src Rmask seed Kfirst Z ξamp
    let q := firstSourceOuterLabel src Rmask seed Kfirst radius
    ∀ (labels : Finset (FirstSourceOuterIndex src Rmask seed Kfirst radius))
      (ref : FirstJointLabel α) (left : Bool),
    let omega := lowLiteralOmega (Fintype.card α) upper bplain₁ bplain₂ ξamp reserve Z
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
        Z (Real.logb Z (volume src.toData)) 1 omega ξsecond (t k) Wkernel bin bidx‖ /
        (volume src.toData*actualHighPrimeCount M H Sbad Z)) ≤
      (C/(seed.absNorm : ℝ))* (1/((ref.sideCommon left).absNorm : ℝ))*
        Z^(ref.sideTargetWidth left Z (Real.logb Z (volume src.toData))-1/50000) := by
  obtain ⟨ν,hν,hντ,hmain⟩ := actual_local_first_low_target M H hH W
    aslot bslot a b lo hi Mslot upper bplain₁ bplain₂ BRmask haslot hWs hW hbslot
    ha haUpper hb hMslot hBRmask hbeta hbetaTop loInput hiInput hloInput
    ηfirst profile Wkernel Sbad I e τ he hecap hτ hτcap 3 1 (by norm_num) (by norm_num)
  refine ⟨ν,hν,hντ,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  have ht : 0 < lowLocalTiny := by norm_num [lowLocalTiny]
  filter_upwards [hmain,eventually_low_fixed_profile_gates (ι := α) upper bplain₁ bplain₂ b lowLocalTiny ht,
    eventually_low_literal_omega (Fintype.card α) upper bplain₁ bplain₂ ξamp reserve hξamp hreserve hamp]
    with Z hmain hfixed homega
  intro hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hhSmall hfreq src hmatch hhi hMs hp₁ hp₂
    hlo hhiInput hhiAbs hupper hb₁ hb₂ hη hn₁ hn₂ hm₁ hm₂ hz hcap Rmask seed hR hRN hs hs0 hz₁ hz₂
    hsource₀ Kfirst hKfirst radius q labels ref left omega hsector domain t htSource bin hbinNone hbins
  have hAeq := original_volume_log src Z w hZ hmatch.scale
  have hA := (local_capacity_of_volume Z (Real.logb Z src.X₁) (Real.logb Z src.X₂) (∑ i,w i)
    (Real.logb Z (volume src.toData)) hAeq hn₁ hn₂ hz hcap).1
  have hsourceLog := (hfixed.2.1 src hsource₀ hhiAbs hb₁ hb₂ hupper).1
  have hsource : sourceRadius src ≤ Z^(1:ℝ) := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hsource₀).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by
        norm_num [lowLocalTiny] at hsourceLog ⊢
        linarith only [hsourceLog,hA])
  have hξampCap : ξamp ≤ 1 := by norm_num [lowLocalTiny] at hamp; linarith
  exact hmain hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hhSmall hfreq src hmatch hhi hMs hp₁ hp₂
    hlo hhiInput hhiAbs hupper hb₁ hb₂ hη hn₁ hn₂ hm₁ hm₂ hz hcap Rmask seed hR hRN hs hs0 hz₁ hz₂
    hsource₀ Kfirst (zero_lt_one.trans_le hKfirst) radius
    (actualLowFirstRadius_le src Rmask seed Kfirst Z ξamp hKfirst hZ hξampCap hsource₀.le hsource)
    labels ref left omega ξsecond homega.2.1 homega.2.2 hξsecond hξsecondCap hsector t htSource bin hbinNone hbins

#print axioms actual_literal_first_low_target
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowLiteralTarget -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentTailLiteralTarget ; sha256 2a244c378176517f4c51c414cf34babebe5b1ffb525b534aa724cf0745c1f5be -/
section




/-! The literal second discarded tail has a fixed saving in the canonical
first target. Its nominal scale uses the actual source radius. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentSupportedTailAggregate
open CenteredMomentExceptionalAmplitudePair EisensteinSchwartzPoisson
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def firstCoherentTailPart (src : Input ι) (R seed : Ideal O) (Kfirst : ℝ)
    (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (k : (i : FirstSourceOuterIndex src R seed Kfirst radius) ×
      (firstSourceOuterLabel src R seed Kfirst radius i).SourceIndex)
    (left : Bool) (Z A omega ξ t : ℝ) (W : 𝓢(ℝ,ℂ)) : ℂ :=
  let q := firstSourceOuterLabel src R seed Kfirst radius k.1
  let Kmain := firstLowMainScale q left Z A 1 omega
  secondDiscardedEnergy ((q.sourceChild k.2).sideParent left) t
    (commonSecondColumns (original src R seed) (q.sideCommon left) (q.sideCommon_supported left))
    (commonSecondBeta (original src R seed) (q.sideCommon left) k.2.1.val)
    W Kmain ((sourceRadius src/((q.sideCommon left).absNorm : ℝ))^2/Kmain) Z ξ

theorem actual_literal_first_coherent_tail_target
    (Mpool : Ideal O) [NeZero Mpool] (Hpool : Subgroup (O ⧸ Mpool)ˣ)
    (hHpool : RayOrthogonality.globalUnits Mpool ≤ Hpool) (Sbad : Finset (Ideal O))
    (Mslot B₁ B₂ upper bplain₁ bplain₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (ξamp reserve ξsecond : ℝ) (hξamp : 0 < ξamp) (hreserve : 0 ≤ reserve)
    (hamp : ξamp+reserve ≤ lowLocalTiny) (hξsecond : 0 < ξsecond)
    (W : 𝓢(ℝ,ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ (src : Input ι), (∀ i,src.M i ≤ Mslot) → src.upper ≤ upper →
      (∀ i,|src.hi i| ≤ upper) → |src.b₁| ≤ bplain₁ → |src.b₂| ≤ bplain₂ →
      (∀ x,‖src.W₁ x‖ ≤ B₁) → (∀ x,‖src.W₂ x‖ ≤ B₂) →
      src.W₁ 0 = 0 → src.W₂ 0 = 0 → 0 < sourceRadius src →
      0 ≤ Real.logb Z (volume src.toData) → Real.logb Z (volume src.toData) ≤ 881/1000 →
    ∀ (R seed : Ideal O), Squarefree seed → seed ≠ 0 →
    ∀ Kfirst : ℝ, 1 ≤ Kfirst →
    let radius := actualLowFirstRadius src R seed Kfirst Z ξamp
    let q := firstSourceOuterLabel src R seed Kfirst radius
    ∀ (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
      (ref : FirstJointLabel ι) (left : Bool),
      (ref.C.absNorm : ℝ) ≤ Z^(1:ℝ) → (ref.D.absNorm : ℝ) ≤ Z^(1:ℝ) →
      (∀ i ∈ labels,(q i).radicalWidth Z ≤ ref.radicalWidth Z+1/1000) →
    let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
    let omega := lowLiteralOmega (Fintype.card ι) upper bplain₁ bplain₂ ξamp reserve Z
    ∀ t : ((i : FirstSourceOuterIndex src R seed Kfirst radius) × (q i).SourceIndex) → ℝ,
    (∑ k ∈ domain,‖firstCoherentTailPart src R seed Kfirst radius k left Z
      (Real.logb Z (volume src.toData)) omega ξsecond (t k) W‖/
        (volume src.toData*actualHighPrimeCount Mpool Hpool Sbad Z)) ≤
      (C/(seed.absNorm : ℝ))*(1/((ref.sideCommon left).absNorm : ℝ))*
        Z^(ref.sideTargetWidth left Z (Real.logb Z (volume src.toData))-1/100) := by
  let Csource := lowLiteralSupportConstant (Fintype.card ι) upper bplain₁ bplain₂
  obtain ⟨S,Ctail,hCtail,htail⟩ := actual_first_coherent_source_tail_sum (ι := ι)
    Csource 10 3 1 ξsecond 10 (1/1000) (by norm_num) (by norm_num) (by norm_num) hξsecond (by norm_num)
  let profileBound := coherentAbsoluteProfileBound (Fintype.card ι) Mslot B₁ B₂ upper bplain₁ bplain₂
  let C := Ctail*profileBound^2*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1,by positivity,?_⟩
  filter_upwards [htail,eventually_low_fixed_profile_gates (ι := ι) upper bplain₁ bplain₂ 1 (1/1000) (by norm_num),
    eventually_low_literal_omega (Fintype.card ι) upper bplain₁ bplain₂ ξamp reserve hξamp hreserve hamp,
    eventually_actual_high_prime_ratio Mpool Hpool hHpool Sbad (1/1000) (by norm_num)]
    with Z htail hfixed homega hprime
  intro hZ src hMs hu hhi hb₁ hb₂ hW₁ hW₂ hz₁ hz₂ hsource₀ hA0 hA R seed hs hs0
    Kfirst hKfirst radius q labels ref left hrefC hrefD hsector domain omega t
  have hz : 0 < Z := zero_lt_one.trans hZ
  let A := Real.logb Z (volume src.toData)
  have hsourceLog := (hfixed.2.1 src hsource₀ hhi hb₁ hb₂ hu).1
  have hsourceA : sourceRadius src ≤ Z^(A+1/1000) := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) := (Real.rpow_logb hz hZ.ne' hsource₀).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le hsourceLog
  have hsource1 : sourceRadius src ≤ Z^(1:ℝ) :=
    hsourceA.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [A]; linarith))
  have hsource10 : sourceRadius src ≤ Z^(10:ℝ) :=
    hsource1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  have hVcap : volume src.toData ≤ Z^(10:ℝ) := by
    calc
      _ = Z^A := (Real.rpow_logb hz hZ.ne' (volume_pos src.toData)).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [A]; linarith)
  have hsourceFactor : sourceRadius src ≤ Csource*volume src.toData :=
    sourceRadius_le_fixed_volume src upper bplain₁ bplain₂ hhi hb₁ hb₂
  have hξampCap : ξamp ≤ 1 := by norm_num [lowLocalTiny] at hamp; linarith
  have hr : ∀ p E,radius p E ≤ 1*Z^(3:ℝ) :=
    actualLowFirstRadius_le src R seed Kfirst Z ξamp hKfirst hZ hξampCap hsource₀.le hsource1
  have hP : 1 ≤ actualHighPrimeCount Mpool Hpool Sbad Z := by
    have hp₀ := hprime.2.1
    unfold actualHighPrimeCount at hp₀ ⊢
    have hp : 0 < (CenteredMomentPrimePool.primePool Mpool Hpool Sbad (1/2) 1 (Z^(3/500:ℝ))).card := by
      exact_mod_cast hp₀
    exact_mod_cast Nat.succ_le_of_lt hp
  let p := ref.radicalWidth Z+1/1000
  have hrad (i) (hi : i ∈ labels) :
      ((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^p := by
    have hn := CenteredMomentFirstScale.norm_pos _ (commonRadical_ne_zero i.1.val.1 i.1.val.2)
    calc
      _ = Z^((q i).radicalWidth Z) := (Real.rpow_logb hz hZ.ne' hn).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (hsector i hi)
  let Kmain := fun k : (i : FirstSourceOuterIndex src R seed Kfirst radius) × (q i).SourceIndex =>
    firstLowMainScale (q k.1) left Z A 1 omega
  let Tsec := fun k : (i : FirstSourceOuterIndex src R seed Kfirst radius) × (q i).SourceIndex =>
    (sourceRadius src/(((q k.1).sideCommon left).absNorm : ℝ))^2/Kmain k
  have hKP (k) (_hk : k ∈ domain) : 0 < Kmain k ∧ Kmain k ≤ Z^(10:ℝ) ∧
      1 ≤ actualHighPrimeCount Mpool Hpool Sbad Z ∧ Tsec k ≤ Z^(10:ℝ) ∧
      (sourceRadius src/(((q k.1).sideCommon left).absNorm : ℝ))^2/Kmain k ≤ Tsec k := by
    have hCD := first_actual_common_caps src R seed hs hz₁ hz₂ Kfirst radius k.1 Z hsource1
    have hK := firstLowMainScale_polynomial_cap (q k.1) left Z A omega hZ
      (by dsimp [A];linarith) (homega.2.2.trans (by norm_num [lowLocalTiny])) hCD.1 hCD.2
    have hT2 := firstLowRadius_fixed_cap (q k.1) left (sourceRadius src) Z A (1/1000) omega 0
      hZ hsource₀.le hsourceA homega.2.1 (by norm_num)
    have hT : Tsec k ≤ Z^(2:ℝ) := by
      simpa only [firstLowRadius,frequencyRadius,zero_div,Real.rpow_zero,mul_one,
        Tsec,Kmain,jointSecondNominal,jointSecondBall,firstLowMainScale] using hT2
    exact ⟨hK.1,hK.2,hP,hT.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)),le_rfl⟩
  have hb := htail.2 src R seed hs hs0 hz₁ hz₂ hsource₀ hsource10 hsourceFactor hVcap
    B₁ B₂ hB₁ hB₂ hW₁ hW₂ Kfirst (zero_lt_one.trans_le hKfirst) radius hr labels left p W hrad
    (fun k => ((q k.1).sourceChild k.2).sideParent left) t Kmain Tsec
    (fun _ => actualHighPrimeCount Mpool Hpool Sbad Z) hKP
  have hprof := originalAbsoluteProfile_fixed src Mslot B₁ B₂ upper bplain₁ bplain₂ hB₁ hB₂ hMs hu hb₁ hb₂
  have href := ref.sideWidth_bounds left Z 1 hZ hrefC hrefD
  have haux := ref.target_auxiliary_widths_nonneg Z hZ
  have hallow : 0 ≤ ref.sideAllowance left Z := by cases left <;> simp_all only [FirstJointLabel.sideAllowance,ite_true,ite_false,Bool.false_eq_true]
  have hexp : p+1/1000-10 ≤ ref.radicalWidth Z+A-2*ref.sideWidth left Z+
      ref.activeWidth Z+ref.punctureWidth Z+ref.sideAllowance left Z-1/100 := by
    dsimp only [p,A]
    linarith [haux.2.1,haux.2.2.1]
  apply hb.trans
  have hcoefficient : Ctail*(originalAbsoluteProfile src B₁ B₂)^2*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ C+1 := by
    apply le_trans _ (show C ≤ C+1 by linarith)
    dsimp only [C,profileBound]
    gcongr <;> first | exact hprof.1 | exact hprof.2
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul hcoefficient (Real.rpow_le_rpow_of_exponent_le hZ.le hexp)
      (Real.rpow_nonneg hz.le _) (by positivity : 0 ≤ C+1)) (Nat.cast_nonneg seed.absNorm)
  apply hh.trans_eq
  have heq := congrArg (fun x : ℝ => x/(seed.absNorm : ℝ))
    (ref.side_target_power left Z A (C+1) (-1/100) hZ)
  dsimp only [A] at heq ⊢
  convert heq using 1 <;> ring

#print axioms actual_literal_first_coherent_tail_target
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentTailLiteralTarget -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentZeroLiteralTarget ; sha256 27fd03bf1d6d32b7d767cd2c7eb4a78a44b90e33a4506ed116241162fea971b8 -/
section




/-! The coherent second zero contribution at the actual first radius and
amplified ball. Source profile constants, the annular prime average and all
scalar losses are discharged before the live first labels. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceSecondZeroEnergy
open CenteredMomentExceptionalAmplitudePair EisensteinSchwartzPoisson
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma coherent_zero_profile_bound (s : Input ι) (Mslot B₁ B₂ upper b₁ b₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hM : ∀ i,s.M i ≤ Mslot)
    (hhi : ∀ i,|s.hi i| ≤ upper) (hb₁ : |s.b₁| ≤ b₁) (hb₂ : |s.b₂| ≤ b₂) :
    (2*B₁*B₂*∏ i,s.M i)^2*|(∏ i,s.hi i)*s.b₁*s.b₂| ≤
      (2*B₁*B₂*(max 1 Mslot)^Fintype.card ι)^2*
        lowLiteralSupportConstant (Fintype.card ι) upper b₁ b₂ := by
  have hM0 (i) : 0 ≤ s.M i := zero_le_one.trans (s.M_ge_one i)
  have hm : (∏ i,s.M i) ≤ (max 1 Mslot)^Fintype.card ι := by
    calc
      _ ≤ ∏ _i : ι,max 1 Mslot := Finset.prod_le_prod₀
        (fun i _ => hM0 i) (fun i _ => (hM i).trans (le_max_right _ _))
      _ = _ := by simp
  have hp : |(∏ i,s.hi i)*s.b₁*s.b₂| ≤ lowLiteralSupportConstant (Fintype.card ι) upper b₁ b₂ := by
    rw [abs_mul,abs_mul,Finset.abs_prod]
    unfold lowLiteralSupportConstant
    calc
      _ ≤ (∏ _i : ι,max 1 upper)*max 1 b₁*max 1 b₂ := by
        gcongr
        · exact (hhi _).trans (le_max_right _ _)
        · exact hb₁.trans (le_max_right _ _)
        · exact hb₂.trans (le_max_right _ _)
      _ = _ := by simp
  have hm0 : 0 ≤ ∏ i,s.M i := Finset.prod_nonneg (fun i _ => hM0 i)
  exact mul_le_mul (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_left hm (by positivity)) 2) hp (abs_nonneg _) (sq_nonneg _)

variable (M : Ideal O) [NeZero M]
local instance coherentZeroLiteralFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

include hH in
/-- The literal coherent zero term has a fixed saving at the first reference
width. The source parent is selected from the original first fixed pair. -/
theorem actual_literal_first_coherent_zero_target
    (Mslot B₁ B₂ upper b₁ b₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (W : 𝓢(ℝ,ℂ)) (Sbad : Finset (Ideal O))
    (ξamp reserve : ℝ) (hξamp : 0 < ξamp) (hreserve : 0 ≤ reserve)
    (hbudget : ξamp+reserve ≤ lowLocalTiny) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 1 < Z,
    ∀ (src : Input ι) (w : ι → ℝ), (∀ i,src.P i = Z^(w i)) →
      (∀ i,src.M i ≤ Mslot) → (∀ i,|src.hi i| ≤ upper) →
      |src.b₁| ≤ b₁ → |src.b₂| ≤ b₂ →
      (∀ x,‖src.W₁ x‖ ≤ B₁) → (∀ x,‖src.W₂ x‖ ≤ B₂) →
      Real.logb Z src.X₁ ≤ 423/1000 → Real.logb Z src.X₂ ≤ 423/1000 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z src.X₁) (Real.logb Z src.X₂) (∑ i,w i) →
    ∀ (R seed : Ideal O), Squarefree seed → seed ≠ 0 →
      src.W₁ 0 = 0 → src.W₂ 0 = 0 → 0 < sourceRadius src →
    ∀ Kfirst : ℝ, 1 ≤ Kfirst →
    let radius := actualLowFirstRadius src R seed Kfirst Z ξamp
    let q := firstSourceOuterLabel src R seed Kfirst radius
    ∀ (labels : Finset (FirstSourceOuterIndex src R seed Kfirst radius))
      (ref : FirstJointLabel ι) (left : Bool),
      (∀ i ∈ labels,
        (q i).radicalWidth Z ≤ ref.radicalWidth Z+lowLocalTiny ∧
        ref.sideWidth left Z ≤ (q i).sideWidth left Z+lowLocalTiny ∧
        (q i).activeWidth Z ≤ ref.activeWidth Z+lowLocalTiny ∧
        (q i).punctureWidth Z ≤ ref.punctureWidth Z+lowLocalTiny) →
    let domain := firstSideSourceLabels labels q (fun _ => sourceRadius src) left
    let omega := lowLiteralOmega (Fintype.card ι) upper b₁ b₂ ξamp reserve Z
    let Kmain := fun k : (i : FirstSourceOuterIndex src R seed Kfirst radius) × (q i).SourceIndex =>
      firstLowMainScale (q k.1) left Z (Real.logb Z (volume src.toData)) 1 omega
    ∀ t : ((i : FirstSourceOuterIndex src R seed Kfirst radius) × (q i).SourceIndex) → ℝ,
      (∑ k ∈ domain,
        ‖((Kmain k : ℂ)*paperRadialFourier W 0)*
          sourceSecondZero (commonSecondColumns (original src R seed) ((q k.1).sideCommon left)
            ((q k.1).sideCommon_supported left))
            (commonSecondBeta (original src R seed) ((q k.1).sideCommon left) k.2.1.val)
            (((q k.1).sourceChild k.2).sideParent left) (t k)‖ /
          (volume src.toData*actualHighPrimeCount M H Sbad Z)) ≤
      (C/(seed.absNorm : ℝ))*(1/((ref.sideCommon left).absNorm : ℝ))*
        Z^(ref.sideTargetWidth left Z (Real.logb Z (volume src.toData))-1/100) := by
  have ht : 0 < lowLocalTiny := by norm_num [lowLocalTiny]
  obtain ⟨Czero,hCzero,hzero⟩ := actual_first_coherent_zero_sum (ι := ι)
    1 3 1 lowLocalTiny lowLocalTiny (by norm_num) (by norm_num) (by norm_num) ht ht
  let Cs := lowLiteralSupportConstant (Fintype.card ι) upper b₁ b₂
  have hCs : 0 < Cs := by dsimp only [Cs,lowLiteralSupportConstant]; positivity
  let C := Czero*((2*B₁*B₂*(max 1 Mslot)^Fintype.card ι)^2*Cs)*‖paperRadialFourier W 0‖
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C+1,by positivity,?_⟩
  filter_upwards [hzero,eventually_fixed_logb_le Cs lowLocalTiny hCs ht,
    eventually_low_literal_omega (Fintype.card ι) upper b₁ b₂ ξamp reserve hξamp hreserve hbudget,
    eventually_actual_high_prime_ratio M H hH Sbad lowLocalTiny ht]
    with Z hzero hprofile homega hprime
  intro hZ src w hP hM hhi hb₁ hb₂ hW₁ hW₂ hn₁ hn₂ hw hcap R seed hs hs0 hz₁ hz₂ hsource₀
    Kfirst hKfirst radius q labels ref left hsector domain omega Kmain t
  let A := Real.logb Z (volume src.toData)
  have hAeq := original_volume_log src Z w hZ hP
  have hA := (local_capacity_of_volume Z (Real.logb Z src.X₁) (Real.logb Z src.X₂)
    (∑ i,w i) A hAeq hn₁ hn₂ hw hcap).1
  have hsourceLog := Real.logb_le_logb_of_le hZ hsource₀
    (sourceRadius_le_fixed_volume src upper b₁ b₂ hhi hb₁ hb₂)
  change Real.logb Z (sourceRadius src) ≤ Real.logb Z (Cs*volume src.toData) at hsourceLog
  rw [Real.logb_mul hCs.ne' (volume_pos src.toData).ne'] at hsourceLog
  have hsource : sourceRadius src ≤ Z^(1:ℝ) := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) :=
        (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hsource₀).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by
        have hp := hprofile.2
        norm_num [lowLocalTiny] at hp
        linarith only [hsourceLog,hA,hp])
  have hξcap : ξamp ≤ 1 := by norm_num [lowLocalTiny] at hbudget; linarith only [hbudget,hreserve]
  have hradius := actualLowFirstRadius_le src R seed Kfirst Z ξamp hKfirst hZ hξcap hsource₀.le hsource
  let refwidth := -2*ref.sideWidth left Z+ref.activeWidth Z+ref.punctureWidth Z+4*lowLocalTiny
  have hrad (i) (hi : i ∈ labels) :
      ((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^(ref.radicalWidth Z+lowLocalTiny) := by
    have hn := CenteredMomentFirstScale.norm_pos _ (commonRadical_ne_zero i.1.val.1 i.1.val.2)
    calc
      _ = Z^((q i).radicalWidth Z) := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (hsector i hi).1
  have hrecip : 1/actualHighPrimeCount M H Sbad Z ≤ Z^(-(3/500 : ℝ)+lowLocalTiny) := by
    rw [show -(3/500 : ℝ)+lowLocalTiny=lowLocalTiny-(3/500 : ℝ) by ring,
      Real.rpow_sub (zero_lt_one.trans hZ)]
    apply (div_le_div_iff₀ hprime.2.1 (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)).mpr
    simpa only [one_mul,mul_comm] using (div_le_iff₀ hprime.2.1).mp hprime.2.2
  have hscale (i) (hi : i ∈ labels) :
      let c := Real.logb Z ((q i).sideCommon left).absNorm;
      let d := Real.logb Z ((q i).sideCommon (!left)).absNorm;
      -2*c+(q i).activeWidth Z+(q i).punctureWidth Z ≤ refwidth ∧
      ∀ k : (q i).SourceIndex, Kmain ⟨i,k⟩ ≤
        Z^(2*A-c-d+(q i).activeWidth Z+(q i).punctureWidth Z-1+max (d-c) 0+6*(3/500)+omega) := by
    dsimp only
    constructor
    · change -2*(q i).sideWidth left Z+(q i).activeWidth Z+(q i).punctureWidth Z ≤ refwidth
      dsimp only [refwidth]
      linarith only [(hsector i hi).2.1,(hsector i hi).2.2.1,(hsector i hi).2.2.2]
    · intro k
      dsimp only [Kmain,firstLowMainScale]
      rw [←(q i).activeWidth_normValue,←(q i).punctureWidth_normValue]
  have hbound := hzero.2 src R seed hs hs0 hz₁ hz₂ hsource₀ hsource
    B₁ B₂ hB₁ hB₂ hW₁ hW₂ Kfirst (zero_lt_one.trans_le hKfirst) radius hradius
    labels left (ref.radicalWidth Z+lowLocalTiny) A 1 omega lowLocalTiny refwidth W
    (by linarith only [hA]) (by norm_num) hrad
    (fun k => ((q k.1).sourceChild k.2).sideParent left) t Kmain (fun _ => actualHighPrimeCount M H Sbad Z)
    (fun k _ => ⟨by dsimp only [Kmain,firstLowMainScale]; positivity,hprime.2.1,hrecip⟩) hscale
  have hcoef : (Czero*(2*B₁*B₂*∏ j,src.M j)^2*|(∏ j,src.hi j)*src.b₁*src.b₂| *‖paperRadialFourier W 0‖) ≤ C := by
    dsimp only [C,Cs]
    exact mul_le_mul_of_nonneg_right
      (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (coherent_zero_profile_bound src Mslot B₁ B₂ upper b₁ b₂ hB₁ hB₂ hM hhi hb₁ hb₂) hCzero.le)
      (norm_nonneg _)
  have hallow : 0 ≤ ref.sideAllowance left Z := by
    cases left
    · exact (ref.target_auxiliary_widths_nonneg Z hZ).2.2.2.2
    · exact (ref.target_auxiliary_widths_nonneg Z hZ).2.2.2.1
  have hexp : (ref.radicalWidth Z+lowLocalTiny)+A+refwidth-87/1000+omega+lowLocalTiny+lowLocalTiny+lowLocalTiny ≤
      ref.radicalWidth Z+A-2*ref.sideWidth left Z+ref.activeWidth Z+ref.punctureWidth Z+
        ref.sideAllowance left Z-1/100 := by
    have ho := homega.2.2
    change omega ≤ lowLocalTiny at ho
    dsimp only [refwidth]
    norm_num [lowLocalTiny] at ho ⊢
    linarith only [ho,hallow]
  apply hbound.trans
  have hh := div_le_div_of_nonneg_right (mul_le_mul (hcoef.trans (by linarith : C ≤ C+1))
    (Real.rpow_le_rpow_of_exponent_le hZ.le hexp)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by positivity : 0 ≤ C+1)) (Nat.cast_nonneg seed.absNorm)
  apply hh.trans_eq
  have heq := ref.side_target_power left Z A (C+1) (-1/100) hZ
  have heq' := congrArg (fun x : ℝ => x/(seed.absNorm : ℝ)) heq
  dsimp only [A] at heq' ⊢
  convert heq' using 1 <;> ring

#print axioms actual_literal_first_coherent_zero_target
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentZeroLiteralTarget -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstFullSectors ; sha256 1055fa27b97be6abf1486a59d75ff6fa4d288cb157cfcfc95878a882b61a228f -/
section



/-! One bounded first-sector partition controls both physical sides,
including their effective row factors and canceled-prime products.
Every nonempty cell uses an actual scalar-minimizing reference. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CanonicalRowCompletion CenteredMomentSectorLocalization
namespace FirstJointLabel
variable {Slot : Type*} [Fintype Slot]

def fullWidthCoordinates (q : FirstJointLabel Slot) (Z : ℝ) : Fin 11 → ℝ :=
  ![q.leftWidth Z,q.rightWidth Z,q.radicalWidth Z,q.activeWidth Z,
    q.punctureWidth Z,q.leftAllowance Z,q.rightAllowance Z,
    Real.logb Z (normValue (leftEffectiveFactor q.C q.D)),
    Real.logb Z ((canceledIdeal q.C q.D 5).absNorm : ℝ),
    Real.logb Z (normValue (leftEffectiveFactor q.D q.C)),
    Real.logb Z ((canceledIdeal q.D q.C 5).absNorm : ℝ)]

lemma fullWidthCoordinates_first (q : FirstJointLabel Slot) (Z : ℝ) (j : Fin 7) :
    q.fullWidthCoordinates Z (Fin.castAdd 4 j) = q.widthCoordinates Z j := by
  fin_cases j <;> rfl

theorem full_width_coordinates_bounds (q : FirstJointLabel Slot) (Z B : ℝ)
    (hZ : 1 < Z) (hB : 0 ≤ B)
    (hC : (q.C.absNorm : ℝ) ≤ Z^B) (hD : (q.D.absNorm : ℝ) ≤ Z^B) :
    ∀ j,0 ≤ q.fullWidthCoordinates Z j ∧ q.fullWidthCoordinates Z j ≤ 5*B := by
  have hw := q.width_coordinates_bounds Z B hZ hB hC hD
  have h (j) : 0 ≤ q.widthCoordinates Z j ∧ q.widthCoordinates Z j ≤ 5*B :=
    ⟨(hw j).1,(hw j).2.trans (by linarith)⟩
  have hl := left_cancellation_sector_caps q.C q.D q.hC Z B hZ hC
  have hr := left_cancellation_sector_caps q.D q.C q.hD Z B hZ hD
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6
  norm_num [widthCoordinates] at h0 h1 h2 h3 h4 h5 h6
  intro j
  fin_cases j <;> norm_num only [fullWidthCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons]
  all_goals first
    | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6
    | exact ⟨hl.2.2.1,hl.2.2.2⟩
    | exact ⟨hl.1,hl.2.1.trans (by linarith)⟩
    | exact ⟨hr.2.2.1,hr.2.2.2⟩
    | exact ⟨hr.1,hr.2.1.trans (by linarith)⟩

theorem first_widths_close_of_full (q ref : FirstJointLabel Slot) (Z e : ℝ)
    (h : ∀ j,|q.fullWidthCoordinates Z j-ref.fullWidthCoordinates Z j| < e) :
    ∀ j,|q.widthCoordinates Z j-ref.widthCoordinates Z j| < e := by
  intro j
  simpa only [fullWidthCoordinates_first] using h (Fin.castAdd 4 j)

theorem cancellation_widths_close_of_full (q ref : FirstJointLabel Slot) (left : Bool) (Z e : ℝ)
    (h : ∀ j,|q.fullWidthCoordinates Z j-ref.fullWidthCoordinates Z j| < e) :
    |Real.logb Z (normValue (leftEffectiveFactor (q.sideCommon left) (q.sideCommon (!left))))-
      Real.logb Z (normValue (leftEffectiveFactor (ref.sideCommon left) (ref.sideCommon (!left))))| < e ∧
    |Real.logb Z ((canceledIdeal (q.sideCommon left) (q.sideCommon (!left)) 5).absNorm : ℝ)-
      Real.logb Z ((canceledIdeal (ref.sideCommon left) (ref.sideCommon (!left)) 5).absNorm : ℝ)| < e := by
  cases left
  · exact ⟨h 9,h 10⟩
  · exact ⟨h 7,h 8⟩

theorem literal_target_gates_of_full (q ref : FirstJointLabel Slot) (left : Bool) (Z e : ℝ)
    (h : ∀ j,|q.fullWidthCoordinates Z j-ref.fullWidthCoordinates Z j| < e) :
    q.radicalWidth Z ≤ ref.radicalWidth Z+e ∧
    ref.sideWidth left Z ≤ q.sideWidth left Z+e ∧
    q.activeWidth Z ≤ ref.activeWidth Z+e ∧
    q.punctureWidth Z ≤ ref.punctureWidth Z+e ∧
    -2*q.sideWidth left Z+q.activeWidth Z+q.punctureWidth Z+q.sideAllowance left Z ≤
      -2*ref.sideWidth left Z+ref.activeWidth Z+ref.punctureWidth Z+ref.sideAllowance left Z+5*e := by
  have hh := q.first_widths_close_of_full ref Z e h
  have hc := abs_lt.mp (hh 0)
  have hd := abs_lt.mp (hh 1)
  have hp := abs_lt.mp (hh 2)
  have hR := abs_lt.mp (hh 3)
  have hE := abs_lt.mp (hh 4)
  have hBc := abs_lt.mp (hh 5)
  have hBd := abs_lt.mp (hh 6)
  norm_num [widthCoordinates] at hc hd hp hR hE hBc hBd
  simp only [leftWidth,rightWidth] at hc hd
  cases left <;>
    simp only [sideWidth,sideCommon,sideAllowance,ite_true,ite_false,Bool.false_eq_true]
  all_goals change _ ∧ _ ∧ _ ∧ _ ∧ _
  all_goals refine ⟨by linarith,?_,by linarith,by linarith,?_⟩
  all_goals linarith

end FirstJointLabel

theorem uniform_first_full_sectors (B e : ℝ) (hB : 0 ≤ B) (he : 0 < e) :
    ∃ N : ℕ, ∀ {Row Slot : Type*} [Fintype Slot]
      (labels : Finset Row) (q : Row → FirstJointLabel Slot) (Z : ℝ), 1 < Z →
      (∀ u ∈ labels,(q u).C.absNorm ≤ (Z^B : ℝ) ∧ (q u).D.absNorm ≤ (Z^B : ℝ)) →
      ∃ bin : (u : Row) → u ∈ labels → (Fin 11 → Fin (N+1)),
        (∀ u v hu hv,bin u hu = bin v hv → ∀ j,
          |(q u).fullWidthCoordinates Z j-(q v).fullWidthCoordinates Z j| < e) ∧
        ∀ b : Fin 11 → Fin (N+1),
          let cell := labels.attach.filter (fun u => bin u.val u.property = b)
          cell.Nonempty → ∃ ref ∈ cell, ∀ u ∈ cell,
            (q ref.val).activeWidth Z/2+(q ref.val).punctureWidth Z ≤
              (q u.val).activeWidth Z/2+(q u.val).punctureWidth Z := by
  obtain ⟨N,hN⟩ := exists_nat_ge (5*B/e)
  refine ⟨N,?_⟩
  intro Row Slot inst labels q Z hZ hcap
  obtain ⟨bin,hbin⟩ := exists_finite_width_bins 11 N e he
    (fun u : {u : Row // u ∈ labels} => (q u.val).fullWidthCoordinates Z) (by
      intro u j
      have hh := (q u.val).full_width_coordinates_bounds Z B hZ hB (hcap u.val u.property).1 (hcap u.val u.property).2 j
      exact ⟨hh.1,hh.2.trans ((div_le_iff₀ he).mp hN)⟩)
  refine ⟨fun u hu => bin ⟨u,hu⟩,?_,?_⟩
  · intro u v hu hv huv
    exact hbin ⟨u,hu⟩ ⟨v,hv⟩ huv
  · intro b cell hcell
    exact exists_first_scalar_reference cell hcell (fun u => q u.val) Z

#print axioms FirstJointLabel.literal_target_gates_of_full
#print axioms uniform_first_full_sectors
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstFullSectors -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstOriginalRemainderTarget ; sha256 9770768ebab3ec6a72170fc4c9a41b6313f232441cfb5f2cd127e990e7667d20 -/
section



/-! First zero and discarded contributions in the literal local window.
Only the retained centered source and the genuine comparison rectangle remain. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceInputTailUniform CenteredMomentExceptionalAmplitudePair
open CenteredMomentEnergyOriginalSource CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentFirstPhysicalSource
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentLogDyadic CenteredMomentSourceProfileMass
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance firstOriginalTargetSumDecEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem actual_local_first_original_remainder
    (a b upper bplain₁ bplain₂ ε ξ : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hupper : 0 ≤ upper) (hε : 0 < ε) (hξ : 0 < ξ) :
    ∃ Sd St : Finset (ℕ×ℕ), ∃ Cd Ct : ℝ, 0 < Cd ∧ 0 < Ct ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (src : Input ι) (profile : Profiles a b),
      profile.profile 0 = src.W₁ → profile.profile 1 = src.W₂ →
      (∀ i,|src.hi i| ≤ upper) → |src.b₁| ≤ bplain₁ → |src.b₂| ≤ bplain₂ → src.upper ≤ upper →
      0 < sourceRadius src →
    ∀ w : ι → ℝ, (∀ i,src.P i=Z^(w i)) →
      Real.logb Z src.X₁ ≤ 423/1000 → Real.logb Z src.X₂ ≤ 423/1000 → (∑ i,w i) ≤ 37/1000 →
    ∀ (R : Ideal O) (r : CenteredMomentRadialEligibleEnergy.Radial), r.scale = Z →
      CenteredMomentInductionEnergy.energy src.η (fixedBadMask*idealGenerator R) 1 src.t
        src.W₁ src.W₂ src.slots src.toData.coefficient src.P src.X₁ src.X₂ r.keep r.profile r.scale ≤
      (2/volume src.toData)*
        (∑ i : FirstSourceOuterIndex src R 1 Z (actualLowFirstRadius src R 1 Z Z ξ),
          ‖firstPhysicalValue src R 1 Z (actualLowFirstRadius src R 1 Z Z ξ)
            (fun _ => src.t) r.profile (fun _ => logAnnulus) i‖)+
      2*Cd*(plainControl src (profile.profile 0) (profile.profile 1))^2*
        Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) r.profile*Z^(1+ε)+
      2*Ct*(plainControl src (profile.profile 0) (profile.profile 1))^2*
        St.sup (schwartzSeminormFamily ℝ ℝ ℂ) r.profile*Z^(1+ε)+
      2*CenteredMomentInductionEnergy.energy src.η (fixedBadMask*idealGenerator R) 1 src.t
        src.W₁ src.W₂ src.slots src.toData.coefficient src.P src.Y₁ src.Y₂ r.keep r.profile r.scale := by
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,hrem⟩ := positive_first_source_remainder
    (fun _ : ι => upper) a b ε ξ 0 (fun _ => hupper) ha hb hε hξ
  refine ⟨Sd,St,Cd,Ct,hCd,hCt,?_⟩
  filter_upwards [hrem,eventually_low_fixed_profile_gates (ι := ι) upper bplain₁ bplain₂ b (1/100) (by norm_num)]
    with Z hrem hfixed
  refine ⟨hrem.1,?_⟩
  intro src profile hp₁ hp₂ hhi hb₁ hb₂ hupperSrc hsource₀ w hscale hn₁ hn₂ hzSum R r hr
  have hZ := hrem.1
  have hz := zero_lt_one.trans hZ
  have hV := CenteredMomentSourceInputTailUniform.volume_pos src
  have hvlog := original_volume_log src Z w hZ hscale
  have hAcap : Real.logb Z (volume src.toData) ≤ 883/1000 := by linarith
  have hVcap : volume src.toData ≤ Z := by
    calc
      _ = Z^(Real.logb Z (volume src.toData)) := (Real.rpow_logb hz hZ.ne' hV).symm
      _ ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
      _ = Z := Real.rpow_one Z
  have hHlog := (hfixed.2.1 src hsource₀ hhi hb₁ hb₂ hupperSrc).1
  have hHcap : sourceRadius src ≤ Z := by
    calc
      _ = Z^(Real.logb Z (sourceRadius src)) := (Real.rpow_logb hz hZ.ne' hsource₀).symm
      _ ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
      _ = Z := Real.rpow_one Z
  have hzero (j : Fin 2) : profile.profile j 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt ha) (profile.support j hh).1
  have hzero₁ : src.W₁ 0 = 0 := by rw [←hp₁]; exact hzero 0
  have hzero₂ : src.W₂ 0 = 0 := by rw [←hp₂]; exact hzero 1
  have hh := hrem.2 src (profile.profile 0) (profile.profile 1) hp₁.symm hp₂.symm
    (profile.support 0) (profile.support 1) (fun i => (le_abs_self _).trans (hhi i))
    hVcap hsource₀ hHcap R r hr
  have hret := original_retained_norm_actual_first_blocks src R 1 hzero₁ hzero₂ src.t r.profile Z Z ξ hz
  have hret' := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hret hV.le) (by norm_num : (0:ℝ) ≤ 2)
  have htail :
      2*Ct*(plainControl src (profile.profile 0) (profile.profile 1))^2*
        St.sup (schwartzSeminormFamily ℝ ℝ ℂ) r.profile*Z^(1-(0:ℝ)) ≤
      2*Ct*(plainControl src (profile.profile 0) (profile.profile 1))^2*
        St.sup (schwartzSeminormFamily ℝ ℝ ℂ) r.profile*Z^(1+ε) := by
    apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
    positivity
  apply hh.trans
  rw [mul_div_assoc]
  have heq : (2/volume src.toData)*
      (∑ i : FirstSourceOuterIndex src R 1 Z (actualLowFirstRadius src R 1 Z Z ξ),
        ‖firstPhysicalValue src R 1 Z (actualLowFirstRadius src R 1 Z Z ξ)
          (fun _ => src.t) r.profile (fun _ => logAnnulus) i‖) =
      2*((∑ i : FirstSourceOuterIndex src R 1 Z (actualLowFirstRadius src R 1 Z Z ξ),
        ‖firstPhysicalValue src R 1 Z (actualLowFirstRadius src R 1 Z Z ξ)
          (fun _ => src.t) r.profile (fun _ => logAnnulus) i‖)/volume src.toData) := by ring
  rw [heq]
  exact add_le_add (add_le_add (add_le_add hret' le_rfl) htail) le_rfl

#print axioms actual_local_first_original_remainder
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstOriginalRemainderTarget -/
