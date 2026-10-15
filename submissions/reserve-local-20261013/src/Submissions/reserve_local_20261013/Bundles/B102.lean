/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B005
import Submissions.reserve_local_20261013.Bundles.B033
import Submissions.reserve_local_20261013.Bundles.B037
import Submissions.reserve_local_20261013.Bundles.B047
import Submissions.reserve_local_20261013.Bundles.B065
import Submissions.reserve_local_20261013.Bundles.B071
import Submissions.reserve_local_20261013.Bundles.B075
import Submissions.reserve_local_20261013.Bundles.B081
import Submissions.reserve_local_20261013.Bundles.B082
import Submissions.reserve_local_20261013.Bundles.B083
import Submissions.reserve_local_20261013.Bundles.B085
import Submissions.reserve_local_20261013.Bundles.B087
import Submissions.reserve_local_20261013.Bundles.B089
import Submissions.reserve_local_20261013.Bundles.B091
import Submissions.reserve_local_20261013.Bundles.B092
import Submissions.reserve_local_20261013.Bundles.B094
import Submissions.reserve_local_20261013.Bundles.B096
import Submissions.reserve_local_20261013.Bundles.B099
import Submissions.reserve_local_20261013.Bundles.B100
import Submissions.reserve_local_20261013.Bundles.B101
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNormalized
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass

/- BEGIN ORIGINAL MODULE Analytic.JointLowPhysicalAggregate ; sha256 e1e1e33fdd970b43dd6983b305deef74a4934992da923f6d65cc402b40636baa -/
section




/-! Literal finite-row parts of the second physical transform. The split is
made only after Poisson; both common factors, the canonical phase, every
projector and both rays remain in the physical block. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open EisensteinSchwartzPoisson CenteredMomentSecondRetainedRows
open CenteredMomentSourceRow CenteredMomentWholeDivisorShell
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentMobiusRegroup CenteredMomentFixedRay RayFourExpansion
open CenteredMomentSecondSectorColumns CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O

/-- A literal physical block on any selected post-transform frequency set. -/
def activePhysicalRows (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K R H : ℝ) (q : ActiveBlocks S β K R H) (rows : Finset O) : ℂ :=
  physicalBlock η t (activeSource S β) β q.1.1.val.1 q.1.1.val.2
    (commonLabels_supported (activeSource S β) _ _ q.1.1.property).1
    (commonLabels_supported (activeSource S β) _ _ q.1.1.property).2 q.1.2 R rows W K
    (fun i => (q.2 i : ℤ))

def actualSecondRowBlocks (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K R H : ℝ) (rows : ActiveBlocks S β K R H → Finset O) : ℂ :=
  ∑ q : ActiveBlocks S β K R H,
    (heightCoeff η t q.1.1.val.1*star (heightCoeff η t q.1.1.val.2))*
      activePhysicalRows η t S β W K R H q (rows q)

lemma actualSecondBlocks_eq_rows (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ H : ℝ) :
    actualSecondBlocks η t S β W K T Z ξ H =
      actualSecondRowBlocks η t S β W K (frequencyRadius T Z ξ) H
        (fun q => retainedRows (frequencyRadius T Z ξ)
          (commonFrequencyGenerator q.1.1.val.1 q.1.1.val.2*
            nonunitFrequencyGenerator q.1.1.val.1 q.1.1.val.2 q.1.2)) := by
  unfold actualSecondBlocks actualSecondRowBlocks
  rw [Fintype.sum_sigma,Fintype.sum_sigma]
  simp only [activePhysicalRows,Finset.mul_sum]

lemma activePhysicalRows_bin_partition {κ : Type*} [Fintype κ]
    (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K R H : ℝ) (q : ActiveBlocks S β K R H)
    (rows : Finset O) (bin : O → κ) :
    activePhysicalRows η t S β W K R H q rows =
      ∑ b : κ, activePhysicalRows η t S β W K R H q (rows.filter (fun z => bin z = b)) := by
  unfold activePhysicalRows physicalBlock
  exact finite_row_bin_partition rows bin _

lemma actualSecondRowBlocks_bin_partition {κ : Type*} [Fintype κ]
    (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K R H : ℝ) (rows : ActiveBlocks S β K R H → Finset O)
    (bin : ActiveBlocks S β K R H → O → κ) :
    actualSecondRowBlocks η t S β W K R H rows =
      ∑ b : κ, actualSecondRowBlocks η t S β W K R H
        (fun q => (rows q).filter (fun z => bin q z = b)) := by
  unfold actualSecondRowBlocks
  conv_lhs =>
    enter [2,q]
    rw [activePhysicalRows_bin_partition (κ := κ) η t S β W K R H q (rows q) (bin q),Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The original dyadic row window is exactly zero above its upper scale;
retaining this finite cutoff removes the low moment's row-norm gate. -/
lemma activePhysicalRows_eq_dyadic_filter (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K R H : ℝ)
    (q : ActiveBlocks S β K R H) (rows : Finset O) :
    activePhysicalRows η t S β W K R H q rows =
      activePhysicalRows η t S β W K R H q
        (rows.filter (fun z => normValue z ≤ dyadicScale (q.2 1 : ℤ))) := by
  unfold activePhysicalRows physicalBlock
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : normValue z ≤ dyadicScale (q.2 1 : ℤ)
  · simp only [h,ite_true]
  · have hw := dyadicWeight_zero_high (q.2 1 : ℤ) (normValue z) (le_of_not_ge h)
    simp [h,hw]

lemma actualSecondRowBlocks_eq_dyadic_filter (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K R H : ℝ)
    (rows : ActiveBlocks S β K R H → Finset O) :
    actualSecondRowBlocks η t S β W K R H rows =
      actualSecondRowBlocks η t S β W K R H
        (fun q => (rows q).filter (fun z => normValue z ≤ dyadicScale (q.2 1 : ℤ))) := by
  unfold actualSecondRowBlocks
  apply Finset.sum_congr rfl
  intro q hq
  rw [activePhysicalRows_eq_dyadic_filter η t S β W K R H q (rows q)]

lemma actualSecondRowBlocks_norm_le (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K R H : ℝ)
    (rows : ActiveBlocks S β K R H → Finset O) :
    ‖actualSecondRowBlocks η t S β W K R H rows‖ ≤
      ∑ q : ActiveBlocks S β K R H, ‖activePhysicalRows η t S β W K R H q (rows q)‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (common_height_norm_le_one η t _ _
      (commonLabels_supported (activeSource S β) _ _ q.1.1.property).1.1
      (commonLabels_supported (activeSource S β) _ _ q.1.1.property).2.1)

def actualSecondProjectors (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (K R H : ℝ) (q : ActiveBlocks S β K R H) : Finset (Ideal O) :=
  divisorPool Finset.univ
    (fun J : sectorPool q.1.1.val.2
      (commonLabels_supported (activeSource S β) _ _ q.1.1.property).2.1 (activeSource S β) =>
        (J : Ideal O))

/-- Every actual projector divides a live residual source column, so its
norm cap follows from the literal source support without a separate gate. -/
lemma actualSecondProjectors_norm_cap (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (K R H Y : ℝ) (hnorm : ∀ I ∈ S,β I ≠ 0 → (I.absNorm : ℝ) ≤ Y)
    (q : ActiveBlocks S β K R H) (D : Ideal O)
    (hD : D ∈ actualSecondProjectors S β K R H q) : (D.absNorm : ℝ) ≤ Y := by
  let C := q.1.1.val.2
  have hC := (commonLabels_supported (activeSource S β) _ _ q.1.1.property).2
  apply (divisorPool_nonzero_norm Finset.univ
    (fun J : sectorPool C hC.1 (activeSource S β) => (J : Ideal O))
    (fun J _ => (sectorPool_supported C hC.1 (activeSource S β) J).1) Y ?_ D hD).2
  intro J hJ
  have hm : C*(J : Ideal O) ∈ supportedColumns (activeSource S β) :=
    (mem_residualPool C hC.1 _ J).mp (Finset.mem_filter.mp J.property).1
  have hl := (mem_activeSource S β _).mp (Finset.mem_filter.mp hm).1
  have hCJ : C*(J : Ideal O) ≠ 0 :=
    mul_ne_zero hC.1 (sectorPool_supported C hC.1 (activeSource S β) J).1
  have hle : ((J : Ideal O).absNorm : ℝ) ≤ ((C*(J : Ideal O)).absNorm : ℝ) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hCJ))
      (map_dvd Ideal.absNorm (dvd_mul_left (J : Ideal O) C))
  exact hle.trans (hnorm _ hl.1 hl.2)

/-- Exact projector and ray majorant for a finite physical frequency part. -/
lemma activePhysicalRows_projected_majorant (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K R H V P : ℝ)
    (hK : 0 < K) (hV : 0 < V) (hP : 0 < P)
    (q : ActiveBlocks S β K R H) (rows : Finset O) (hrows : ∀ z ∈ rows,z ≠ 0) :
    ‖activePhysicalRows η t S β W K R H q rows‖/(V*P) ≤
      ∑ L ∈ actualSecondProjectors S β K R H q, ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*
          ‖pairCoeff (phaseTable (primaryGenerator q.1.1.val.1) (primaryGenerator q.1.1.val.2)) χ ξ‖*
          (secondPrecountFactor V P q.1.1.val.1 q.1.1.val.2 q.1.2 K (fun i => (q.2 i : ℤ))*
            ∑ z ∈ rows, ‖(projectedSecondKernelLabel η (activeSource S β) β q.1.1.val.1 q.1.1.val.2
              (commonLabels_supported (activeSource S β) _ _ q.1.1.property).1
              (commonLabels_supported (activeSource S β) _ _ q.1.1.property).2
              (commonLabels_data _ _ _ _ q.1.1.property).2.2 q.1.2 L χ ξ).kernelRow t z W K R
                (fun i => (q.2 i : ℤ))‖) := by
  have hm := actual_physicalBlock_bin_majorant (κ := Unit) η t (activeSource S β) β
    q.1.1.val.1 q.1.1.val.2
    (commonLabels_supported (activeSource S β) _ _ q.1.1.property).1
    (commonLabels_supported (activeSource S β) _ _ q.1.1.property).2
    (commonLabels_data _ _ _ _ q.1.1.property).2.2 q.1.2 R rows (fun _ => ())
    hrows W K hK (fun i => (q.2 i : ℤ)) V P hV hP
  have hp := secondPrecountFactor_pos V P hV hP _ _
    (commonLabels_supported (activeSource S β) _ _ q.1.1.property).1
    (commonLabels_supported (activeSource S β) _ _ q.1.1.property).2 q.1.2 K hK (fun i => (q.2 i : ℤ))
  apply hm.trans_eq
  simp only [Finset.univ_unique,Finset.sum_singleton,Finset.filter_true,
    actualSecondProjectors,Finset.mul_sum,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- The common-energy identity with one genuine finite bin partition made
only in its transformed physical frequencies. -/
theorem commonEnergy_actual_second_bins {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : CenteredMomentFirstAmplificationChoice.OriginalData ι) (C : Ideal O) (hC : Supported C)
    (η : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K T Z ξ H : ℝ)
    (hK : 0 < K)
    (hH : ∀ I ∈ commonSecondColumns s C hC,commonSecondBeta s C L I ≠ 0 → (I.absNorm : ℝ) ≤ H)
    (bin : ActiveBlocks (commonSecondColumns s C hC) (commonSecondBeta s C L)
      K (frequencyRadius T Z ξ) H → O → κ) :
    CenteredMomentFirstPhysicalSource.commonEnergy s C hC η t L W K =
      ((K : ℂ)*paperRadialFourier W 0)*
        CenteredMomentSourceSecondZeroEnergy.sourceSecondZero (commonSecondColumns s C hC) (commonSecondBeta s C L) η t +
      (∑ b : κ,actualSecondRowBlocks η t (commonSecondColumns s C hC) (commonSecondBeta s C L)
        W K (frequencyRadius T Z ξ) H (fun q =>
          (retainedRows (frequencyRadius T Z ξ)
            (commonFrequencyGenerator q.1.1.val.1 q.1.1.val.2*
              nonunitFrequencyGenerator q.1.1.val.1 q.1.1.val.2 q.1.2)).filter (fun z => bin q z = b))) +
      CenteredMomentSupportedTailAggregate.secondDiscardedEnergy η t (commonSecondColumns s C hC) (commonSecondBeta s C L)
        W K T Z ξ := by
  rw [commonEnergy_second_blocks s C hC η t L W K T Z ξ H hK hH,
    actualSecondBlocks_eq_rows,actualSecondRowBlocks_bin_partition (κ := κ) _ _ _ _ _ _ _ _ _ bin]

#print axioms actualSecondRowBlocks_bin_partition
#print axioms activePhysicalRows_projected_majorant
#print axioms commonEnergy_actual_second_bins
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowPhysicalAggregate -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSelectedPhysicalKernel ; sha256 fef9a92a1ef8f7990b7f097925489f82ebc5ddd02573977f5865177d8d6b58d8 -/
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
local instance selectedLowPhysicalKernelFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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
open CenteredMomentSecondBlockHarmonicMass
/-- The actual prime cardinality and physical main radius are retained exactly. -/
theorem actual_selected_second_low_physical_kernel_of_common_bin
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
      ∀ (Wkernel : 𝓢(ℝ,ℂ)) (decay : ℕ) (ν tailRows tailV lower tailSaving upper bplain₁ bplain₂ BRmask : ℝ)
        (Sbad : Finset (Ideal O)) (primeLoss : ℝ), 0 < ν → 0 ≤ tailRows → 0 < primeLoss →
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
      0 ≤ pad → nominal+pad ≤ Mcap → nominal+pad+Bmask+ξconductor ≤ d →
      pad+loss+(67/450)*((omegaLoss+profileLoss)+2*clip) ≤ 1/45000 →
      Kcut = Z^(2*A-c-d₁+r₁+e₁-Mparent+max (d₁-c) 0+6*(3/500)+omegaLoss) →
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
      src.upper ≤ upper → src.b₁ ≤ bplain₁ → src.b₂ ≤ bplain₂ →
      (Rmask.absNorm : ℝ) ≤ Z^BRmask →
      vBound ≤ (1+4*Real.pi)*Z^ν → height ≤ Z^ν →
      let target := δcommon+nominal+allowance-1/45000
      lower ≤ target →
      let label : CommonSecondKernelLabel α :=
        ⟨src,Rmask,seed,C₁,Lfirst,hC₁,hseedfirst,parent,p₂,U,Lproj,χL,χR⟩
      let b₂ := (Real.logb Z (C₂.absNorm : ℝ)+Real.logb Z (D₂.absNorm : ℝ))/2
      let outside := A-min c d₁+r₁+e₁-Mparent+5*(3/500)+
        Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))-
        Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)-b₂+omegaLoss
      let Elow := lowFixedCoefficient (ι := α) Cbound Mslot upper bplain₁ bplain₂ p S degree
      let smallLoss := (BRmask+Bcommon)*εmask+ν*(degree : ℝ)
      let Eabs := 2*128^(Fintype.card α+2)*Mslot^Fintype.card α*B₁*B₂*
        (max 1 upper)^Fintype.card α*max 1 bplain₁*max 1 bplain₂
      secondPrecountFactor (Z^(A-c)) (actualHighPrimeCount M H Sbad Z) C₂ D₂ U Kcut n*
        (∑ z ∈ Ω, ‖(((1+SecondKernelLabel.kernelScale n)^decay : ℝ) : ℂ)*
        label.toKernelLabel.kernelRow t z Wkernel Kcut radius n‖) ≤
        Ckernel*((Elow/(aSource*(Lproj.absNorm : ℝ)))*pairWeight C₂ D₂*
          Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-1/45000+smallLoss+primeLoss)+
          (128/aSource)*Eabs^2*pairWeight C₂ D₂*
            Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-1/45000-tailSaving+primeLoss)) := by
  obtain ⟨degree,S,hmain⟩ := actual_selected_second_low_kernel_of_common_bin M H hH W
    aslot bslot a b Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss Mslot εmask hMslot hεmask
    loInput hiInput Bcommon δcommon hBcommon hδcommon ηfirst parentLoss hparentLoss ξconductor hξconductor
  refine ⟨degree,S,?_⟩
  intro Wkernel decay ν tailRows tailV lower tailSaving upper bplain₁ bplain₂ BRmask Sbad primeLoss hν htailRows hprimeLoss
  obtain ⟨Nkernel,Ckernel,hCkernel,hkernel⟩ := hmain Wkernel decay ν tailRows tailV lower tailSaving hν htailRows
  refine ⟨Nkernel,Ckernel,hCkernel,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hkernel η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hmain,eventually_actual_high_prime_ratio M H hH Sbad primeLoss hprimeLoss] with Z hmain hprime
  intro hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ Rmask seed Lproj Lfirst hC₁ hD₁ p₂ C₂ D₂ hC₂ hD₂ hCD₂
    E₁ ξ₁ ξ₂ F
  let u := firstSideDictionaryUnit ηfirst P₁ Q₁ hP₁ E₁ ξ₁ ξ₂ F
  obtain ⟨hu,hbase⟩ := hmain hZ θ w σ freq height hw hwmesh hσlo hσhi hheight hfreq p src hmatch hhi hMs hp₁ hp₂
    hloInput hhiInput hX₁ hX₂ hY₁ hY₂ P₁ Q₁ hP₁ C₁ D₁ Rmask seed Lproj Lfirst hC₁ hD₁ p₂ hCD₂ E₁ ξ₁ ξ₂ F
  refine ⟨hu,?_⟩
  intro left parent U family hfamily hR hseed hLproj hCcap hDcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    c d₁ r₁ e₁ radius nominal pad hpad hMcapSource hconductorSource hbudgetSource hKmain hne χL χR sL sR low abin k holes hholes
    habin habinTop hbaseScale hT hbinL hbinR hfreqGate hheightSource Ω hkeepL hkeepR hnorm
    vBound B₁ B₂ aSource hvBound hB₁ hB₂ haSource hvCube hz₁ hz₂ hW₁ hW₂ hdyadRows hAtail hphysicalL hphysicalR
    hupper hbplain₁ hbplain₂ hRN hvSmall hhSmall target htarget label Elow smallLoss Eabs
  let b₂ := (Real.logb Z (C₂.absNorm : ℝ)+Real.logb Z (D₂.absNorm : ℝ))/2
  let outside := A-min c d₁+r₁+e₁-Mparent+5*(3/500)+
    Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))-
    Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)-b₂+omegaLoss
  have hk := hbase left U family hfamily hR hseed hLproj hCcap hDcap hLcap
    t columns β rows Wrad Kcut n Hsource A Mparent g omegaLoss ξ sourceLoss profileLoss allowance clip
    hKcut hHsource hsource hcapacity hvolume hprofile hg hgCap homega hallowance hprofile0 hclip hclipCost
    hpad hMcapSource hconductorSource hbudgetSource hne χL χR low abin k holes hholes
    habin habinTop hbaseScale hT hbinL hbinR hfreqGate hheightSource Ω hkeepL hkeepR hnorm
    vBound B₁ B₂ aSource hvBound hB₁ hB₂ haSource hvCube hz₁ hz₂ hW₁ hW₂ hdyadRows hAtail hphysicalL hphysicalR htarget
  let BL := Cbound*((Rmask*(C₁*C₂)).radical.absNorm : ℝ)^εmask*profileCost src*
    diagonalControl sL.radial.profile*(p.control S)^2*(1+vBound+height)^degree /
      (((C₁*C₂).absNorm : ℝ)*Lproj.absNorm)
  let BR := Cbound*((Rmask*(C₁*D₂)).radical.absNorm : ℝ)^εmask*profileCost src*
    diagonalControl sR.radial.profile*(p.control S)^2*(1+vBound+height)^degree /
      (((C₁*D₂).absNorm : ℝ)*Lproj.absNorm)
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hElow : 0 ≤ Elow := low_fixed_coefficient_nonneg Cbound Mslot upper bplain₁ bplain₂ p S degree hCbound.le
  have hEabs : 0 ≤ Eabs := by dsimp [Eabs]; positivity
  have hNL : 0 < ((C₁*C₂).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero hC₁.1 hC₂.1))
  have hNR : 0 < ((C₁*D₂).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero hC₁.1 hD₂.1))
  have hLP : 0 < (Lproj.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hLproj.ne_zero)
  have habsL := low_actual_coefficient_absorbed src p S degree Rmask (C₁*C₂) hR (mul_ne_zero hC₁.1 hC₂.1)
    Z Cbound Mslot upper bplain₁ bplain₂ BRmask Bcommon εmask ν vBound height hZ.le hCbound.le hMslot hεmask.le hν.le
    hMs hupper hbplain₁ hbplain₂ hRN hCcap hvBound hheight hvSmall hhSmall
  have habsR := low_actual_coefficient_absorbed src p S degree Rmask (C₁*D₂) hR (mul_ne_zero hC₁.1 hD₂.1)
    Z Cbound Mslot upper bplain₁ bplain₂ BRmask Bcommon εmask ν vBound height hZ.le hCbound.le hMslot hεmask.le hν.le
    hMs hupper hbplain₁ hbplain₂ hRN hDcap hvBound hheight hvSmall hhSmall
  have hBL : BL ≤ (Elow*Z^smallLoss)/(((C₁*C₂).absNorm : ℝ)*Lproj.absNorm) :=
    div_le_div_of_nonneg_right habsL (mul_pos hNL hLP).le
  have hBR : BR ≤ (Elow*Z^smallLoss)/(((C₁*D₂).absNorm : ℝ)*Lproj.absNorm) :=
    div_le_div_of_nonneg_right habsR (mul_pos hNR hLP).le
  have hpair := mul_le_mul_of_nonneg_left
    (mul_le_mul (Real.sqrt_le_sqrt hBL) (Real.sqrt_le_sqrt hBR) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (div_nonneg (volume_pos src.toData).le (Real.sqrt_nonneg (dyadicScale (n 2)*dyadicScale (n 3))))
  have hphys := low_physical_normalized_pair C₂ D₂ hC₂.1 hD₂.1
    Z A c d₁ r₁ e₁ Mparent (3/500) omegaLoss
    (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
    (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ))
    (δcommon+allowance-(3/500)) (1/45000) (volume src.toData) (dyadicScale (n 2)) (dyadicScale (n 3))
    ((C₁*C₂).absNorm : ℝ) ((C₁*D₂).absNorm : ℝ) (Lproj.absNorm : ℝ) (Elow*Z^smallLoss) aSource
    hZ (volume_pos _) (dyadicScale_pos _) (dyadicScale_pos _) hNL hNR hLP
    (mul_nonneg hElow (Real.rpow_nonneg hZ0.le _)) haSource hphysicalL hphysicalR
  have htargeteq : δcommon+allowance-(3/500)+nominal+(3/500)-1/45000 = target := by dsimp [target]; ring
  change Z^outside*(_*Z^(δcommon+allowance-(3/500)+nominal+(3/500)-1/45000)) ≤ _ at hphys
  rw [htargeteq] at hphys
  have hmainpair : Z^outside*((volume src.toData/Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
      (Real.sqrt BL*Real.sqrt BR)*Z^target) ≤
      (Elow/(aSource*(Lproj.absNorm : ℝ)))*pairWeight C₂ D₂*
        Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-1/45000+smallLoss) := by
    apply ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpair (Real.rpow_nonneg hZ0.le _))
      (Real.rpow_nonneg hZ0.le _)).trans hphys).trans_eq
    conv_rhs => rw [Real.rpow_add hZ0]
    have he : A-c+r₁+e₁+(δcommon+allowance-(3/500))-1/45000 =
        A-c+r₁+e₁+δcommon+allowance-(3/500)-1/45000 := by ring
    rw [he]
    ring
  have hAbsBound := originalAbsoluteProfile_le_fixed src Mslot upper bplain₁ bplain₂ B₁ B₂
    hMslot hB₁ hB₂ hMs hupper hbplain₁ hbplain₂
  have hAbs0 : 0 ≤ originalAbsoluteProfile src B₁ B₂ := by
    unfold originalAbsoluteProfile
    have hpm : 0 ≤ ∏ i,src.M i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (src.M_ge_one i))
    positivity
  have htail : (128/aSource)*(originalAbsoluteProfile src B₁ B₂)^2*Z^(outside+target-tailSaving) ≤
      (128/aSource)*Eabs^2*Z^(outside+target-tailSaving) := by gcongr
  have hpower : Z^outside*(∑ z ∈ Ω, ‖(((1+SecondKernelLabel.kernelScale n)^decay : ℝ) : ℂ)*
      label.toKernelLabel.kernelRow t z Wkernel Kcut radius n‖) ≤
      Ckernel*((Elow/(aSource*(Lproj.absNorm : ℝ)))*pairWeight C₂ D₂*
        Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-1/45000+smallLoss)+
        (128/aSource)*Eabs^2*Z^(outside+target-tailSaving)) := by
    apply (mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hZ0.le outside)).trans
    calc
      _ = Ckernel*(Z^outside*((volume src.toData/Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
          (Real.sqrt BL*Real.sqrt BR)*Z^target)+
          (128/aSource)*(originalAbsoluteProfile src B₁ B₂)^2*Z^(outside+target-tailSaving)) := by
        change Z^outside*(Ckernel*((_*_+_)*Z^target)) = _
        simp only [sub_eq_add_neg,Real.rpow_add hZ0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hmainpair htail) hCkernel
  have hid := low_precount_nominal_identity A c d₁ r₁ e₁ Mparent (3/500) omegaLoss
    (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
    (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)) b₂
    (δcommon+allowance-(3/500)) (1/45000)
  change outside+(δcommon+allowance-(3/500)+nominal+(3/500)-1/45000) = _ at hid
  have htailPower : Z^primeLoss*Z^(outside+target-tailSaving) = pairWeight C₂ D₂*
      Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-1/45000-tailSaving+primeLoss) := by
    rw [pairWeight_eq_power C₂ D₂ hC₂.1 hD₂.1 Z hZ,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    congr 1
    change primeLoss+(outside+target-tailSaving) = -b₂+_
    dsimp [target]
    linarith [hid]
  have hpcount : 0 < actualHighPrimeCount M H Sbad Z := hprime.2.1
  have hratio := hprime.2.2
  have hscalar := low_actual_precount_eq C₂ D₂ hC₂ hD₂ U Z A c d₁ r₁ e₁ Mparent omegaLoss
    (actualHighPrimeCount M H Sbad Z) Kcut n hZ hpcount hKmain
  change secondPrecountFactor (Z^(A-c)) (actualHighPrimeCount M H Sbad Z) C₂ D₂ U Kcut n =
    (Z^(3/500 : ℝ)/actualHighPrimeCount M H Sbad Z)*Z^outside at hscalar
  rw [hscalar,mul_assoc]
  apply (mul_le_mul_of_nonneg_left hpower (by positivity)).trans
  calc
    _ ≤ Z^primeLoss*(Ckernel*((Elow/(aSource*(Lproj.absNorm : ℝ)))*pairWeight C₂ D₂*
        Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-1/45000+smallLoss)+
        (128/aSource)*Eabs^2*Z^(outside+target-tailSaving))) := by
      apply mul_le_mul_of_nonneg_right hratio
      have hpw := pairWeight_nonneg C₂ D₂
      positivity
    _ = _ := by
      calc
        _ = Ckernel*((Elow/(aSource*(Lproj.absNorm : ℝ)))*pairWeight C₂ D₂*
            (Z^(A-c+r₁+e₁+δcommon+allowance-(3/500)-1/45000+smallLoss)*Z^primeLoss)+
            (128/aSource)*Eabs^2*(Z^primeLoss*Z^(outside+target-tailSaving))) := by ring
        _ = _ := by
          rw [htailPower,Real.rpow_add hZ0
            (A-c+r₁+e₁+δcommon+allowance-(3/500)-1/45000+smallLoss) primeLoss]
          ring


#print axioms actual_selected_second_low_physical_kernel_of_common_bin
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSelectedPhysicalKernel -/

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowNormalized ; sha256 0b1c3b8c7e54c513c0707a943f86e03ad2810bc2c4af37c3273fa6a03b62e8d3 -/
section




/-! Adapted from OpenAI/math family003, pinned original module Detector.LowNormalized.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical ContDiff
open Filter
namespace LowProbe
open ProbePhysical
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem original_normalized_compensatedPhysicalProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=Submission20261012.Global.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : HeckeFamily.Character,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z/normer‖≤
        C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+loss) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin K) : Function.support (WC j)⊆Set.Icc a b := by
    intro y hy
    apply Set.Ioo_subset_Icc_self (hsupp j _)
    intro hz
    exact hy (by dsimp [WC];rw [hz];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤ B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hW1' : Function.support W1⊆Set.Icc a1 (max b1 (a1+1)) := by
    intro y hy
    exact ⟨(hW1 hy).1,(hW1 hy).2.trans (le_max_left _ _)⟩
  have hab1 : a1< max b1 (a1+1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨Cn,hCn,hnorm⟩ := LowNormalizer.actual_ray_normalizer_inverse M H hH S hS a b ha hab
    ell hell hsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 (loss/2) (by positivity)
  intro η
  obtain ⟨Cp,hCp,hprobe⟩ := original_ray_compensatedPhysicalProbe_low_loss S hS hmax ell
    (fun j=>(hell j).le) hinj hsum.le (RayQuotient.identityClass M H) a b B (loss/2)
    ha hab (by positivity) WC hWC hWCB W0 W1 a0 b0 a1 (max b1 (a1+1))
    (SchwartzMap.seminorm ℝ 0 0 W0) (SchwartzMap.seminorm ℝ 0 0 W1)
    ha0 ha1 hab1 (by positivity) (by positivity) hW0 hW1' (W0.smooth (⊤ : ℕ∞)) (W1.smooth (⊤ : ℕ∞))
    (SchwartzMap.norm_le_seminorm ℝ W0) (SchwartzMap.norm_le_seminorm ℝ W1) η
  refine ⟨Cp*Cn,by positivity,?_⟩
  filter_upwards [hprobe,hnorm,eventually_gt_atTop (0:ℝ)] with Z hp hn hZ
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  calc
    _≤(Cp*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+loss/2))*(Cn*Z^(loss/2)) :=
      mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    _=(Cp*Cn)*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+loss) := by
      rw [mul_mul_mul_comm,←Real.rpow_add hZ]
      congr 2
      ring

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowNormalized -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalUniform ; sha256 7f6447339038f605fc43452aa13caf8c48527eda278e08132185df6e2973a6e1 -/
section



set_option autoImplicit false
set_option maxHeartbeats 1600000
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
open CenteredMomentSecondBlockAggregate CenteredMomentSecondSectorColumns
open CenteredMomentRowNorm CenteredMomentChildAssembly CenteredMomentHeckeColumnWindow
open CenteredMomentSecondScaled CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFiniteProfileExceptionalCommon CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonExceptionalCost CenteredMomentExceptionalAmplitudePair
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSectorLocalization
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentChildRows CenteredMomentForcing
open CenteredMomentFirstSectors
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondExceptionalKernel CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentOriginalCommonHarmonic CenteredMomentRankinRadical
open RayFourExpansion UniqueFactorizationMonoid CompletedGauss
local notation "O" => HeckeFamily.O
local instance coherentExceptionalUniformDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_coherent_exceptional_physical_uniform
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi) (lo hi : ι → ℝ)
    (ε δ θ B Lbound Bsource : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ)
    (hB : 0 ≤ B) (hL : 0 ≤ Lbound) (W : 𝓢(ℝ,ℂ)) :
    ∃ J : ℕ, ∃ Sprofile : Finset (ℕ×ℕ), (0,0) ∈ Sprofile ∧
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
    ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} → ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (src : Input ι) (profile : Profiles wlo whi),
    (∀ i, src.lo i = lo i) → (∀ i, src.hi i = hi i) → (∀ i, 1 ≤ src.P i) →
    src.W₁ = profile.profile 0 → src.W₂ = profile.profile 1 → sourceRadius src ≤ Z^Bsource →
    ∀ (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁), R ≠ 0 → ∀ hseed : seed ∣ C₁,
    ∀ p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁),
    ∀ (η : Character) (U : Finset (CommonIndex p.val.1 p.val.2))
      (family : RayCharacter → Character),
    Family η p.val.1 p.val.2 (lowActiveLeftSupported p) (lowActiveRightSupported p) U family →
    ∀ (χ₀ : RayCharacter) (t Kphys Radius r P : ℝ) (n : Fin 4 → ℤ), 0 < Kphys → 0 < P →
    Z^r ≤ src.X₁ → Z^r ≤ src.X₂ → Z^r ≤ src.Y₁ → Z^r ≤ src.Y₂ →
    idealCoeff η p.val.1 ≠ 0 →
    ∀ m : O, m ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m →
    ∀ rows : Finset O, (∀ z ∈ rows, z ≠ 0) →
    (∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ₀) Q m
      (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) z) →
    (∀ z ∈ rows, ((Ideal.span {z}).absNorm : ℝ) ≤ dyadicScale (n 1)) →
    (∀ χ : RayCharacter, ∀ z ∈ rows, ((family χ).modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*(C₁*p.val.1).absNorm)*(Ideal.span {z}).absNorm : ℝ) ≤ Z^B) →
    (∀ χ : RayCharacter, ∀ z ∈ rows, ((reflected (family χ)).modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*(C₁*p.val.2).absNorm)*(Ideal.span {z}).absNorm : ℝ) ≤ Z^B) →
    (∀ L ∈ divisorPool Finset.univ (fun I : sectorPool p.val.2 (lowActiveRightSupported p).1
        (activeSource (commonSecondColumns (original src R seed) C₁ hC₁)
          (commonSecondBeta (original src R seed) C₁ L₁)) => (I : Ideal O)),
      (moebius L : ℂ) ≠ 0 → (L.absNorm : ℝ) ≤ Z^Lbound) →
    ‖physicalBlock η t
      (activeSource (commonSecondColumns (original src R seed) C₁ hC₁)
        (commonSecondBeta (original src R seed) C₁ L₁))
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.1 p.val.2
      (lowActiveLeftSupported p) (lowActiveRightSupported p) U Radius rows W Kphys n‖/
      (volume src.toData*P) ≤
    ((256*Ckernel)*coherentExceptionalProfile Sprofile src profile J Q K t)*
      (((C₁.absNorm : ℝ)*P)⁻¹*
        ((volume src.toData/(C₁.absNorm : ℝ))^(1/3:ℝ)*Kphys^(5/6:ℝ)*
          (originalLowerProfile src wlo wlo)^(-2/3:ℝ))*
        Z^(2*ε+δ+2*Bsource*θ-2*max (r-Real.logb Z (C₁.absNorm : ℝ)) 0/3)/
          ((commonRadical p.val.1 p.val.2).absNorm : ℝ)) := by
  obtain ⟨J,Sprofile,hSprofile,Ckernel,hCkernel,hbound⟩ := actual_coherent_exceptional_physical_scalar
    wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL W
  refine ⟨J,Sprofile,hSprofile,Ckernel,hCkernel,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩ := hbound Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro src profile hlo hhi hP hW₁ hW₂ hsource R seed C₁ L₁ hC₁ hR hseed
    p η U family hfamily χ₀ t Kphys Radius r P n hKphys hPcount hX₁ hX₂ hY₁ hY₂ hη m hm hml hm2
    rows hn hex hN hcondL hcondR hDs
  have hprofile := coherentExceptionalProfile_nonneg Sprofile src profile J Q K t hK.le
  have hz := zero_lt_one.trans hZ.1
  have ha := originalLowerProfile_pos src wlo wlo hwlo hwlo
  have hV := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  by_cases hne : physicalBlock η t
      (activeSource (commonSecondColumns (original src R seed) C₁ hC₁)
        (commonSecondBeta (original src R seed) C₁ L₁))
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.1 p.val.2
      (lowActiveLeftSupported p) (lowActiveRightSupported p) U Radius rows W Kphys n = 0
  · rw [hne,norm_zero,zero_div]
    positivity
  · have hb := hZ.2 src profile hlo hhi hP hW₁ hW₂ R seed C₁ L₁ hC₁ hR hseed
      p η U family hfamily χ₀ t Kphys Radius r P n hKphys hPcount hX₁ hX₂ hY₁ hY₂
      hη m hm hml hm2 rows hn hex hN hcondL hcondR hDs
    have hs := actual_coherent_exceptional_scalar_uniform src R seed C₁ L₁ hC₁ wlo whi hwlo profile
      hW₁ hW₂ p η t U Radius rows hn W Kphys hKphys n Z P ε δ θ Bsource r
      hZ.1 hPcount hθ.le hsource hne
    apply hb.trans
    calc
      _ = ((256*Ckernel)*coherentExceptionalProfile Sprofile src profile J Q K t)*
          (Z^(2*ε+δ-max (max (r-Real.logb Z ((C₁*p.val.1).absNorm : ℝ)) 0)
            (max (r-Real.logb Z ((C₁*p.val.2).absNorm : ℝ)) 0))*
            (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)^θ*
            coherentExceptionalScalar (volume src.toData) P (C₁.absNorm : ℝ) p.val.1 p.val.2 U Kphys n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg (by norm_num) hCkernel) hprofile)

#print axioms actual_coherent_exceptional_physical_uniform
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalUniform -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentZeroSum ; sha256 6677df58478af042d74af8084e774c8092abdb5e40154fb219ca3e77995dfc3c -/
section



/-! Both coherent zero terms are summed over the literal first common
labels, partitions, dyadic blocks, projectors and rays. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
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

def FirstJointLabel.sideCommon (q : FirstJointLabel ι) (left : Bool) : Ideal O :=
  if left then q.C else q.D

theorem FirstJointLabel.sideCommon_supported (q : FirstJointLabel ι) (left : Bool) :
    Supported (q.sideCommon left) := by cases left <;> simp [sideCommon,q.hC,q.hD]

def firstSideSourceLabels {Λ : Type*} [DecidableEq Λ]
    (labels : Finset Λ) (q : Λ → FirstJointLabel ι) (H : Λ → ℝ) (left : Bool) :=
  if left then firstLeftSourceLabels labels q H else firstRightSourceLabels labels q H

theorem actual_first_coherent_zero_sum (B Lrad Cr ε εsum : ℝ)
    (hB : 0 ≤ B) (hLrad : 0 ≤ Lrad) (hCr : 0 < Cr) (hε : 0 < ε) (hεsum : 0 < εsum) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (s : Input ι) (R seed : Ideal O), Squarefree seed → seed ≠ 0 →
      s.W₁ 0 = 0 → s.W₂ 0 = 0 → 0 < sourceRadius s → sourceRadius s ≤ Z^B →
    ∀ (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ → (∀ x,‖s.W₁ x‖ ≤ B₁) → (∀ x,‖s.W₂ x‖ ≤ B₂) →
    ∀ Kfirst : ℝ, 0 < Kfirst →
    ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
      (∀ p E,radius p E ≤ Cr*Z^Lrad) →
    let q := firstSourceOuterLabel s R seed Kfirst radius
    ∀ (labels : Finset (FirstSourceOuterIndex s R seed Kfirst radius)) (left : Bool)
      (p A M omega primeLoss refwidth : ℝ) (W : 𝓢(ℝ,ℂ)),
      A ≤ 883/1000 → 1 ≤ M →
      (∀ i ∈ labels, ((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^p) →
    let domain := firstSideSourceLabels labels q (fun _ => sourceRadius s) left
    ∀ (η : ((i : FirstSourceOuterIndex s R seed Kfirst radius) × (q i).SourceIndex) → Character)
      (t K P : ((i : FirstSourceOuterIndex s R seed Kfirst radius) × (q i).SourceIndex) → ℝ),
      (∀ k ∈ domain, 0 ≤ K k ∧ 0 < P k ∧ 1/P k ≤ Z^(-(3/500)+primeLoss)) →
      (∀ i ∈ labels,
        let c := Real.logb Z ((q i).sideCommon left).absNorm;
        let d := Real.logb Z ((q i).sideCommon (!left)).absNorm;
        -2*c+(q i).activeWidth Z+(q i).punctureWidth Z ≤ refwidth ∧
        ∀ k : (q i).SourceIndex, K ⟨i,k⟩ ≤
          Z^(2*A-c-d+(q i).activeWidth Z+(q i).punctureWidth Z-M+max (d-c) 0+6*(3/500)+omega)) →
      (∑ k ∈ domain,
        ‖((K k : ℂ)*paperRadialFourier W 0)*
          sourceSecondZero (commonSecondColumns (original s R seed) ((q k.1).sideCommon left)
            ((q k.1).sideCommon_supported left))
            (commonSecondBeta (original s R seed) ((q k.1).sideCommon left) k.2.1.val) (η k) (t k)‖ /
          (volume s.toData*P k)) ≤
      (Cbound*(2*B₁*B₂*∏ j,s.M j)^2*|(∏ j,s.hi j)*s.b₁*s.b₂| *‖paperRadialFourier W 0‖)*
        Z^(p+A+refwidth-87/1000+omega+primeLoss+ε+εsum)/(seed.absNorm : ℝ) := by
  obtain ⟨Czero,hCzero,hzero⟩ := actual_common_second_zero_normalized (ι := ι) B ε hB hε
  obtain ⟨Csum,hCsum,hsum⟩ := actual_first_source_sector_harmonic_mass B Lrad Cr εsum hB hLrad hCr hεsum
  refine ⟨Czero*Csum,mul_pos hCzero hCsum,?_⟩
  filter_upwards [hsum] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s R seed hs hs0 hz₁ hz₂ hsource₀ hsource B₁ B₂ hB₁ hB₂ hb₁ hb₂ Kfirst hKfirst radius hr q
    labels left p A M omega primeLoss refwidth W hA hM hrad domain η t K P hKP hwidth
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  have hmass := hZ.2 ι s R seed hs hs0 hz₁ hz₂ hsource₀ hsource Kfirst hKfirst radius hr labels p hrad
  have hmass' : (∑ k ∈ domain,1/((k.2.1.val).absNorm : ℝ)) ≤ Csum*Z^(p+εsum)/(seed.absNorm : ℝ) := by
    cases left
    · exact hmass.2
    · exact hmass.1
  have hpoint (k) (hk : k ∈ domain) :
      ‖((K k : ℂ)*paperRadialFourier W 0)*
        sourceSecondZero (commonSecondColumns (original s R seed) ((q k.1).sideCommon left)
          ((q k.1).sideCommon_supported left))
          (commonSecondBeta (original s R seed) ((q k.1).sideCommon left) k.2.1.val) (η k) (t k)‖ /
        (volume s.toData*P k) ≤
      (Czero*(2*B₁*B₂*∏ j,s.M j)^2*|(∏ j,s.hi j)*s.b₁*s.b₂| *‖paperRadialFourier W 0‖)*
        Z^(A+refwidth-87/1000+omega+primeLoss+ε)/((k.2.1.val).absNorm : ℝ) := by
    have hg : k.1 ∈ labels ∧ Squarefree k.2.1.val ∧ k.2.1.val ≠ 0 ∧ ((k.2.1.val).absNorm : ℝ) ≤ Z^B := by
      cases left
      · exact firstRightSourceLabels_gates labels q _ Z B hz.le (fun _ _ => hsource) k hk
      · exact firstLeftSourceLabels_gates labels q _ Z B hz.le (fun _ _ => hsource) k hk
    have hn (side : Bool) : 0 < (((q k.1).sideCommon side).absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ((q k.1).sideCommon_supported side).1)
    have hn1 (side : Bool) : (1 : ℝ) ≤ ((q k.1).sideCommon side).absNorm := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ((q k.1).sideCommon_supported side).1)
    have hc (side : Bool) : 0 ≤ Real.logb Z (((q k.1).sideCommon side).absNorm : ℝ) :=
      Real.logb_nonneg hZ.1 (hn1 side)
    have hh := hzero Z hZ.1.le s R seed ((q k.1).sideCommon left) k.2.1.val
      ((q k.1).sideCommon_supported left) hg.2.2.1 B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂
      hsource₀.le hsource (η k) (t k) W A _ _ ((q k.1).activeWidth Z) ((q k.1).punctureWidth Z)
      M omega primeLoss (K k) (P k) (hc left) (hc (!left)) hA hM (hKP k hk).1 (hKP k hk).2.1
      ((hwidth k.1 hg.1).2 k.2) (hKP k hk).2.2
      (le_of_eq (Real.rpow_logb hz hZ.1.ne' (hn left)))
    apply hh.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hZ.1.le
    linarith [(hwidth k.1 hg.1).1]
  apply (Finset.sum_le_sum hpoint).trans
  rw [show (∑ k ∈ domain,
      (Czero*(2*B₁*B₂*∏ j,s.M j)^2*|(∏ j,s.hi j)*s.b₁*s.b₂| *‖paperRadialFourier W 0‖)*
        Z^(A+refwidth-87/1000+omega+primeLoss+ε)/((k.2.1.val).absNorm : ℝ)) =
      (Czero*(2*B₁*B₂*∏ j,s.M j)^2*|(∏ j,s.hi j)*s.b₁*s.b₂| *‖paperRadialFourier W 0‖)*
        Z^(A+refwidth-87/1000+omega+primeLoss+ε)*(∑ k ∈ domain,1/((k.2.1.val).absNorm : ℝ)) by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro k hk;ring]
  apply (mul_le_mul_of_nonneg_left hmass' (by positivity)).trans_eq
  rw [Real.rpow_add hz (p+A+refwidth-87/1000+omega+primeLoss+ε) εsum]
  simp only [Real.rpow_add hz,Real.rpow_sub hz]
  ring

#print axioms actual_first_coherent_zero_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentZeroSum -/

/- BEGIN ORIGINAL MODULE Analytic.JointFiniteAbsoluteSum ; sha256 b7bf4ddee6290c9f80d1d2a4444747008506b2cae83c87b5fe572e2f85ac14c6 -/
section


/-! Uniform bounds for every subset of a complex sector control its
absolute sum with a fixed factor four. Thus common-label phases can be
discarded without paying the number of arithmetic labels. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic

theorem real_sum_abs_le_two_of_subsets {α : Type*} (S : Finset α) (f : α → ℝ) (C : ℝ)
    (h : ∀ T : Finset α,T ⊆ S → |∑ i ∈ T,f i| ≤ C) :
    (∑ i ∈ S,|f i|) ≤ 2*C := by
  let Sp := S.filter (fun i => 0 ≤ f i)
  let Sn := S.filter (fun i => ¬0 ≤ f i)
  have hp := h Sp (Finset.filter_subset _ _)
  have hn := h Sn (Finset.filter_subset _ _)
  have heq : (∑ i ∈ S,|f i|) = (∑ i ∈ Sp,f i)-(∑ i ∈ Sn,f i) := by
    simp only [Sp,Sn,Finset.sum_filter,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hf : 0 ≤ f i
    · simp [hf,abs_of_nonneg hf]
    · simp [hf,abs_of_neg (lt_of_not_ge hf)]
  rw [heq]
  linarith [(le_abs_self (∑ i ∈ Sp,f i)),neg_le_abs (∑ i ∈ Sn,f i)]

theorem complex_sum_norm_le_four_of_subsets {α : Type*} (S : Finset α) (f : α → ℂ) (C : ℝ)
    (h : ∀ T : Finset α,T ⊆ S → ‖∑ i ∈ T,f i‖ ≤ C) :
    (∑ i ∈ S,‖f i‖) ≤ 4*C := by
  have hre : (∑ i ∈ S,|(f i).re|) ≤ 2*C := real_sum_abs_le_two_of_subsets S (fun i => (f i).re) C (by
    intro T hT
    have hh := (Complex.abs_re_le_norm (∑ i ∈ T,f i)).trans (h T hT)
    simpa only [Complex.re_sum] using hh)
  have him : (∑ i ∈ S,|(f i).im|) ≤ 2*C := real_sum_abs_le_two_of_subsets S (fun i => (f i).im) C (by
    intro T hT
    have hh := (Complex.abs_im_le_norm (∑ i ∈ T,f i)).trans (h T hT)
    simpa only [Complex.im_sum] using hh)
  calc
    _ ≤ ∑ i ∈ S,(|(f i).re|+|(f i).im|) := Finset.sum_le_sum (fun i _ => Complex.norm_le_abs_re_add_abs_im (f i))
    _ = (∑ i ∈ S,|(f i).re|)+(∑ i ∈ S,|(f i).im|) := Finset.sum_add_distrib
    _ ≤ _ := by linarith

#print axioms complex_sum_norm_le_four_of_subsets
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFiniteAbsoluteSum -/
