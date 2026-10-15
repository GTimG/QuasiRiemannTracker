/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B009
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B034
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B060
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B061
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B064
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B065
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B067
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B068
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

/- BEGIN ORIGINAL MODULE Analytic.JointFirstTargetBounds ; sha256 7d9152768500f5f9509da0e22ba9647875662374a315fd3bb12003617eabcdea -/
section



/-! A uniform lower target exponent for the first Fourier cutoff follows
from the actual common-ideal caps. It is chosen before the live labels. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentFirstPhysicalSource
open CenteredMomentRankinRadical CompletedGauss CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport
open CenteredMomentFirstCanonicalFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

namespace FirstJointLabel

theorem target_auxiliary_widths_nonneg (s : FirstJointLabel ι) (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ s.radicalWidth Z ∧ 0 ≤ s.activeWidth Z ∧ 0 ≤ s.punctureWidth Z ∧
      0 ≤ s.leftAllowance Z ∧ 0 ≤ s.rightAllowance Z := by
  have hr : 1 ≤ ((commonRadical s.C s.D).absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero s.C s.D))
  have ha : 1 ≤ normValue (activeConductor s.C s.D) :=
    normValue_ge_one _ (supported_element_ne_zero _ (activeConductor_supported s.C s.D s.hC))
  have he : 1 ≤ normValue s.puncture :=
    normValue_ge_one _ (supported_element_ne_zero _ (subsetGenerator_supported s.C s.D s.hC s.E))
  refine ⟨Real.logb_nonneg hZ hr,Real.logb_nonneg hZ ha,?_,?_,?_⟩
  · unfold punctureWidth
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact Real.logb_nonneg hZ he
  · exact div_nonneg (le_max_right _ _) (by norm_num)
  · exact div_nonneg (le_max_right _ _) (by norm_num)

theorem target_widths_lower (s : FirstJointLabel ι) (Z A Amin B : ℝ) (hZ : 1 < Z)
    (hA : Amin ≤ A) (hC : (s.C.absNorm : ℝ) ≤ Z^B) (hD : (s.D.absNorm : ℝ) ≤ Z^B) :
    Amin-B ≤ s.leftTargetWidth Z A ∧ Amin-B ≤ s.rightTargetWidth Z A := by
  obtain ⟨hr,ha,he,hleft,hright⟩ := s.target_auxiliary_widths_nonneg Z hZ
  have hcn : 0 < (s.C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hC.1)
  have hdn : 0 < (s.D.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.hD.1)
  have hc := Real.logb_le_logb_of_le hZ hcn hC
  have hd := Real.logb_le_logb_of_le hZ hdn hD
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hc hd
  change s.leftWidth Z ≤ B at hc
  change s.rightWidth Z ≤ B at hd
  unfold leftTargetWidth rightTargetWidth
  constructor <;> linarith

end FirstJointLabel
#print axioms FirstJointLabel.target_widths_lower
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstTargetBounds -/

/- BEGIN ORIGINAL MODULE Analytic.JointKernelBinPartition ; sha256 1572991a7785b8af03e86e502478a99794cd882f57ab5ac251aa059b6262f59c -/
section




/-! Finite buffered-bin partitions are applied to the literal second
kernel rows after the exact transform. The same bin is used for every
second projector, and injective arithmetic reindexing adds no factor. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily
local notation "O" => HeckeFamily.O
variable {ι Λ κ γ : Type*} [Fintype ι] [DecidableEq ι]

lemma finite_row_bin_partition {Row : Type*} [Fintype κ] [AddCommMonoid γ]
    (rows : Finset Row) (bin : Row → κ) (f : Row → γ) :
    (∑ z ∈ rows, f z) = ∑ b : κ, ∑ z ∈ rows.filter (fun z => bin z = b), f z := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

lemma finite_row_option_bin_partition {Row : Type*} [Fintype κ] [AddCommMonoid γ]
    (rows : Finset Row) (bin : Row → Option κ) (f : Row → γ) :
    (∑ z ∈ rows, f z) = (∑ z ∈ rows.filter (fun z => bin z = none), f z) +
      ∑ b : κ, ∑ z ∈ rows.filter (fun z => bin z = some b), f z := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  cases hb : bin z <;> simp [hb]

theorem joint_second_kernel_bin_partition [Fintype κ]
    (labels : Finset Λ) (s : Λ → CommonSecondKernelLabel ι)
    (Ds : Λ → Finset (Ideal O)) (rows : Λ → Finset O)
    (bin : Λ → O → κ) (t K R : Λ → ℝ) (n : Λ → Fin 4 → ℤ)
    (W : 𝓢(ℝ,ℂ)) (decay : ℕ) (weight : Λ → Ideal O → ℂ) :
    (∑ l ∈ labels, ∑ D ∈ Ds l, ∑ z ∈ rows l,
      (((1+SecondKernelLabel.kernelScale (n l))^decay : ℝ) : ℂ)*weight l D*
        ((s l).withProjector D).toKernelLabel.kernelRow (t l) z W (K l) (R l) (n l)) =
    ∑ b : κ, ∑ l ∈ labels, ∑ D ∈ Ds l,
      ∑ z ∈ (rows l).filter (fun z => bin l z = b),
        (((1+SecondKernelLabel.kernelScale (n l))^decay : ℝ) : ℂ)*weight l D*
          ((s l).withProjector D).toKernelLabel.kernelRow (t l) z W (K l) (R l) (n l) := by
  conv_lhs =>
    enter [2,l,2,D]
    rw [finite_row_bin_partition (rows l) (bin l)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]

theorem joint_second_kernel_norm_le_bins [Fintype κ]
    (labels : Finset Λ) (s : Λ → CommonSecondKernelLabel ι)
    (Ds : Λ → Finset (Ideal O)) (rows : Λ → Finset O)
    (bin : Λ → O → κ) (t K R : Λ → ℝ) (n : Λ → Fin 4 → ℤ)
    (W : 𝓢(ℝ,ℂ)) (decay : ℕ) (weight : Λ → Ideal O → ℂ) :
    ‖∑ l ∈ labels, ∑ D ∈ Ds l, ∑ z ∈ rows l,
      (((1+SecondKernelLabel.kernelScale (n l))^decay : ℝ) : ℂ)*weight l D*
        ((s l).withProjector D).toKernelLabel.kernelRow (t l) z W (K l) (R l) (n l)‖ ≤
    ∑ b : κ, ∑ l ∈ labels, ∑ D ∈ Ds l,
      ∑ z ∈ (rows l).filter (fun z => bin l z = b),
        ‖(((1+SecondKernelLabel.kernelScale (n l))^decay : ℝ) : ℂ)*weight l D*
          ((s l).withProjector D).toKernelLabel.kernelRow (t l) z W (K l) (R l) (n l)‖ := by
  rw [joint_second_kernel_bin_partition labels s Ds rows bin t K R n W decay weight]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l hl
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro D hD
  exact norm_sum_le _ _

/-- A literal arithmetic encoding is used as a change of summation
variable, before the joint population bound. There is no label count. -/
theorem joint_row_reindex [DecidableEq Λ]
    (labels : Finset Λ) (encode : Λ → JointReconstructionLabel)
    (hinj : Set.InjOn encode (↑labels : Set Λ))
    (f : JointReconstructionLabel → ℝ) :
    (∑ l ∈ labels, f (encode l)) = ∑ v ∈ labels.image encode, f v := by
  exact (Finset.sum_image hinj).symm

#print axioms joint_second_kernel_bin_partition
#print axioms joint_second_kernel_norm_le_bins
#print axioms joint_row_reindex
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointKernelBinPartition -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowLiteralGeometry ; sha256 216e135caee194bd5db721bb8da030b87cb0ad04096c72a837c67d8588309b7f -/
section



/-! Nominal low-bin width from the actual second physical block. This
keeps the enlarged first radius and the literal common-frequency norms. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge CenteredMomentSecondPhysicalLedger
open CenteredMomentSourceRow
open RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentSecondChildRadialWidth
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonProfile
open CenteredMomentAmplificationChildSourceCaps CenteredMomentEnergyChildState CenteredMomentEnergyState
open CenteredMomentFirstPhysicalSource

theorem second_selected_supported {C D T : Ideal O} (hC : Supported C) (hD : Supported D)
    (hT : T = C ∨ T = D) : Supported T := by
  rcases hT with rfl | rfl <;> assumption

theorem actual_low_live_source_geometry
    {α : Type*} [Fintype α] [DecidableEq α]
    (src : Input α) (C₁ D₁ C₂ D₂ Rmask : Ideal O)
    (hC₁ : C₁ ≠ 0) (hD₁ : D₁ ≠ 0) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD₂ : primeSupport C₂ = primeSupport D₂) (U : Finset (CommonIndex C₂ D₂))
    (T : Ideal O) (hT : T = C₂ ∨ T = D₂)
    (Z A M g L omegaLoss profileLoss : ℝ) (hZ : 1 < Z) (w : α → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hparent : A+(7/2)*(∑ i,w i) ≤ M+g)
    (hvolume : Real.logb Z (volume src.toData) ≤ A)
    (hprofile : (Fintype.card α : ℝ)*Real.logb Z (max 1 src.upper) ≤ profileLoss)
    (hX₁ : src.X₁ ≤ Z^L) (hX₂ : src.X₂ ≤ Z^L) (hY₁ : src.Y₁ ≤ Z^L) (hY₂ : src.Y₂ ≤ Z^L)
    (τ : Character) (v : ℝ) :
    ∀ B : actualAllocations src.pools (C₁*T),
    frozenCoefficient B.val (C₁*T) Rmask src.ν src.W src.P ≠ 0 →
    let data := commonData (withHeight src τ v) (C₁*T) Rmask B
    data.X₁ ≤ Z^L ∧ data.X₂ ≤ Z^L ∧ data.Y₁ ≤ Z^L ∧ data.Y₂ ≤ Z^L ∧
    A+(7/2)*(∑ i : liveIndices B.val,w i.val) ≤ M+g ∧
    Real.logb Z (data.X₁*data.X₂*∏ i : liveIndices B.val,src.P i.val)-
      jointLowNominal M (Real.logb Z (C₁.absNorm : ℝ)) (Real.logb Z (D₁.absNorm : ℝ))
        (3/500) omegaLoss (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)) ≤
      A-(M+g)+6*(3/500)+g+(omegaLoss+profileLoss) := by
  intro B hB data
  have hn₁ := norm_ge_one (B.val (Sum.inr 0)) (alloc_ne src (C₁*T) B (Sum.inr 0))
  have hn₂ := norm_ge_one (B.val (Sum.inr 1)) (alloc_ne src (C₁*T) B (Sum.inr 1))
  have hsum : (∑ i : liveIndices B.val,w i.val) ≤ ∑ i,w i := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hw i)
  refine ⟨(div_le_self src.X₁_pos.le hn₁).trans hX₁,(div_le_self src.X₂_pos.le hn₂).trans hX₂,
    (div_le_self src.Y₁_pos.le hn₁).trans hY₁,(div_le_self src.Y₂_pos.le hn₂).trans hY₂,by linarith,?_⟩
  have hh := actual_joint_low_volume_shift_selected src C₁ D₁ C₂ D₂ Rmask hC₁ hD₁ hC₂ hD₂ hCD₂ U T hT B hB
    Z A M (3/500) omegaLoss profileLoss hZ hvolume hprofile
  calc
    _ ≤ A-M+6*(3/500)+omegaLoss+profileLoss := hh
    _ = A-(M+g)+6*(3/500)+g+(omegaLoss+profileLoss) := by ring

/-- The actual fixed first parent and nonzero second physical block give
its low state width, with one threshold before every first label. -/
theorem eventually_actual_low_state_width
    (η₀ : Character) (parentLoss : ℝ) (hparentLoss : 0 < parentLoss) :
    ∀ᶠ Z : ℝ in Filter.atTop, ∀ hZ : 1 < Z,
    ∀ (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
      (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
      (F : FixedPair η₀ C₁ D₁ hC₁ E₁ ξ₁ ξ₂) (parent : Character),
    (parent = F.left ∨ parent = F.right) →
    ∀ (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
      (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
    Family parent C₂ D₂ hC₂ hD₂ U family →
    ∀ (t : ℝ) (columns : Finset (Ideal O)) (β : Ideal O → ℂ) (rows : Finset O)
      (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4 → ℤ)
      (H A M omegaLoss ξ sourceLoss Bmask : ℝ),
    0 < K → 0 < H → ∀ hBmask : 0 ≤ Bmask, Real.logb Z H ≤ A+sourceLoss →
    let c := Real.logb Z (C₁.absNorm : ℝ)
    let d := Real.logb Z (D₁.absNorm : ℝ)
    let R := Real.logb Z (normValue (activeConductor C₁ D₁))
    let e := Real.logb Z (normValue (primeSubsetGenerator (fun P : CommonIndex C₁ D₁ => P.val) E₁))
    let radius := frequencyRadius (jointSecondNominal C₁ H Z A c d R e M (3/500) omegaLoss) Z ξ
    ∀ hne : physicalBlock parent t columns β C₂ D₂ hC₂ hD₂ U radius rows W K n ≠ 0,
    ∀ (χ : RayCharacter) (Q : Ideal O),
    (actualState (τ := family) t columns β radius rows W K n hne Z Bmask hZ
      χ Q 1 one_ne_zero (by simpa using Real.one_le_rpow hZ.le hBmask)).width ≤
      jointLowNominal M c d (3/500) omegaLoss
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)) +
      (2*sourceLoss+parentLoss+ξ/2+Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))) := by
  filter_upwards [eventually_first_parent_width η₀ parentLoss hparentLoss] with Z hZ
  intro hZlive C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F parent hparent C₂ D₂ hC₂ hD₂ U family hfamily
    t columns β rows W K n H A M omegaLoss ξ sourceLoss Bmask hK hH hBmask hsource c d R e radius hne χ Q
  have hparentcap : Real.logb Z (parent.modulus.absNorm : ℝ) ≤ R+e+parentLoss := by
    rcases hparent with rfl | rfl
    · exact (hZ.2 C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F).1
    · exact (hZ.2 C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F).2
  exact actual_joint_low_width C₁ C₂ D₂ hC₁.1 parent t columns β hC₂ hD₂ U family hfamily
    rows W K hK n H Z A c d R e M (3/500) omegaLoss ξ sourceLoss parentLoss
    hH hZ.1 rfl hsource hparentcap hne χ

#print axioms actual_low_live_source_geometry
#print axioms eventually_actual_low_state_width
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowLiteralGeometry -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceAdmissible ; sha256 c658810ebd56d8535e122050517e5127746b0d8f60c2430fbfc3cde733aef440 -/
section



/-! A nonzero literal source product produces admissible high-bin data.
The hypotheses are the actual conductor, height and scale gates; there is
no assumed pointwise estimate, Mellin bound, or allocation cardinality. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDyadic ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentRetainedProfile CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentPrimeSlot CenteredMomentHeckeExpansion
open CenteredMomentDivisorRectangle
local notation "O" => HeckeFamily.O

theorem actual_source_allocated_admissible
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ {ι Slot : Type*} [Fintype ι] [DecidableEq ι] [Fintype Slot] [DecidableEq Slot]
        (f : ι ↪ Slot) (orders : Finset Slot → ℕ) (edge e : ℝ), edge ≤ 1 → e ≤ 1/1000 →
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
        (hH : RayOrthogonality.globalUnits M ≤ H)
        (η : Character) (w : NonzeroElement) (parent : JointParentLabel η)
        (N : NaturalRow parent.val w.val) (puncture : Ideal O) (hpuncture : puncture ≠ 0)
        (source : Character) (m A z : O) (t : ℝ),
      (∀ I : Ideal O, rowWeight source m A z t I =
        rowWeight parent.val (fixedBadMask*idealGenerator puncture) 1 w.val t I) →
      ∀ (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
        (Z d X₁ X₂ : ℝ) (η₀ : Slot → Character) (V : Slot → ℝ → ℂ)
        (alo bhi : Slot → ℝ) (P : ι → ℝ) (bin : ℕ)
        (Rwidth τ ηaux σmin σmax T : ℝ),
      1 < Z → d ≠ 0 → 1 < Z^d → 0 < X₁ → 0 < X₂ → 0 ≤ Rwidth →
      X₁ ≤ (Z^d)^Rwidth → X₂ ≤ (Z^d)^Rwidth →
      (∀ i, 1 ≤ P i ∧ P i ≤ (Z^d)^Rwidth) → σmin ≤ 0 → 0 ≤ σmax →
      (∀ label, (bufferedProductFamily M H hH η₀
        (excluded N.character puncture) label).modulus.absNorm ≤ Z^d) →
      |t|+Z^τ/2 ≤ (3*bin+2 : ℕ)*Z^τ →
      (3+(3*bin+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux →
      (3+(3*bin+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux →
      (∀ i : liveIndices D allocation,
        2*(|Real.log (alo (f i.val))|+|Real.log (bhi (f i.val))|)+1 ≤ Real.log (P i.val)) →
      3*(bin+1 : ℕ)*Z^τ ≤ T →
      allocatedPositiveRow source m A z t (fun i => primePool M H (bhi (f i)) (P i))
        (fun i I => idealCoeff (η₀ (f i)).inverse I*V (f i) ((I.absNorm : ℝ)/P i)) P
        D allocation W₁ W₂ X₁ X₂ ≠ 0 →
      ∃ data : SurvivingBufferedData η w Slot orders C edge e,
        data.slots = embeddedSlots (allocationSlotEmbedding f D allocation) ∧
        ‖allocatedPositiveRow source m A z t (fun i => primePool M H (bhi (f i)) (P i))
          (fun i I => idealCoeff (η₀ (f i)).inverse I*V (f i) ((I.absNorm : ℝ)/P i)) P
          D allocation W₁ W₂ X₁ X₂‖ = ‖data.value M H η₀ V bhi Z d‖ ∧
        d*data.length ≤ Real.logb Z (X₁*X₂*∏ i, P i)-
          Real.logb Z (formalReductionFactor D allocation P)+Real.logb Z (max 1 b₁*max 1 b₂) ∧
        data.Admissible M H hH η₀ alo bhi Rwidth τ ηaux σmin σmax Z d T := by
  obtain ⟨C,hC,hdata⟩ := actual_source_allocated_buffered W₁ W₂ a₁ b₁ a₂ b₂
    ha₁ ha₂ hs₁ hW₁ hs₂ hW₂
  refine ⟨C,hC,?_⟩
  intro ι Slot instι instDι instSlot instDSlot f orders edge e hedge he M instM H hH
    η w parent N puncture hpuncture source m A z t hrow D allocation
    Z d X₁ X₂ η₀ V alo bhi P bin Rwidth τ ηaux σmin σmax T
    hZ hd hbase hX₁ hX₂ hR hX₁cap hX₂cap hP hσmin hσmax hconductor
    hfreq hfour htwo hlog hbuffer hn
  have hPpos (i : ι) : 0 < P i := zero_lt_one.trans_le (hP i).1
  obtain ⟨P₁,P₂,h₁,h₂,hσ₁,hσ₂,ht₁,ht₂,hnorm,hlength⟩ :=
    hdata f orders edge e hedge he M H η w parent N puncture hpuncture
      source m A z t hrow D allocation Z d X₁ X₂ η₀ V bhi P bin
      hZ hd hbase hX₁ hX₂ hPpos hn
  let data := embeddedBufferedData (allocationSlotEmbedding f D allocation) orders C edge e
    (allocatedBufferedData parent N puncture hpuncture D allocation P₁ P₂ Z d X₁ X₂ P t bin)
  refine ⟨data,rfl,hnorm,hlength,?_⟩
  apply embeddedBufferedData_admissible
  have hcond : ∀ label, (bufferedProductFamily M H hH (fun i => η₀ (f i))
      (excluded N.character puncture) label).modulus.absNorm ≤ Z^d := by
    rintro (_ | ⟨i,θ⟩)
    · exact hconductor none
    · exact hconductor (some (f i,θ))
  exact allocatedBufferedData_admissible M H hH parent N puncture hpuncture D allocation
    P₁ P₂ Z d X₁ X₂ P t bin (fun i => η₀ (f i))
    (fun i => alo (f i)) (fun i => bhi (f i)) Rwidth τ ηaux σmin σmax T
    hbase hR hX₁.le hX₂.le hX₁cap hX₂cap hP hσmin hσmax hcond ht₁ ht₂
    hfreq hfour htwo hlog hbuffer

#print axioms actual_source_allocated_admissible
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceAdmissible -/

/- BEGIN ORIGINAL MODULE Analytic.JointSourceShortGates ; sha256 c4188ee8025f60671f9939c23aa94cf3bde4f5f775f330a793190efd41b8e2ff -/
section




/-! A nonzero literal source product produces admissible high-bin data.
The hypotheses are the actual conductor, height and scale gates; there is
no assumed pointwise estimate, Mellin bound, or allocation cardinality. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDyadic ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentRetainedProfile CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentPrimeSlot CenteredMomentHeckeExpansion
open CenteredMomentDivisorRectangle
local notation "O" => HeckeFamily.O

theorem actual_source_allocated_short_gates
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ {ι Slot : Type*} [Fintype ι] [DecidableEq ι] [Fintype Slot] [DecidableEq Slot]
        (f : ι ↪ Slot) (orders : Finset Slot → ℕ) (edge e : ℝ), edge ≤ 1 → e ≤ 1/1000 →
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
        (hH : RayOrthogonality.globalUnits M ≤ H)
        (η : Character) (w : NonzeroElement) (parent : JointParentLabel η)
        (N : NaturalRow parent.val w.val) (puncture : Ideal O) (hpuncture : puncture ≠ 0)
        (source : Character) (m A z : O) (t : ℝ),
      (∀ I : Ideal O, rowWeight source m A z t I =
        rowWeight parent.val (fixedBadMask*idealGenerator puncture) 1 w.val t I) →
      ∀ (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
        (Z d X₁ X₂ : ℝ) (η₀ : Slot → Character) (V : Slot → ℝ → ℂ)
        (alo bhi : Slot → ℝ) (P : ι → ℝ) (Pfull : Slot → ℝ) (bin : ℕ)
        (Rwidth τ ηaux σmin σmax T : ℝ),
      (∀ i, P i = Pfull (f i)) →
      1 < Z → d ≠ 0 → 1 < Z^d → 0 < X₁ → 0 < X₂ → 0 ≤ Rwidth →
      X₁ ≤ (Z^d)^Rwidth → X₂ ≤ (Z^d)^Rwidth →
      (∀ i, 1 ≤ P i ∧ P i ≤ (Z^d)^Rwidth) → σmin ≤ 0 → 0 ≤ σmax →
      (∀ label, (bufferedProductFamily M H hH η₀
        (excluded N.character puncture) label).modulus.absNorm ≤ Z^d) →
      |t|+Z^τ/2 ≤ (3*bin+2 : ℕ)*Z^τ →
      (3+(3*bin+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux →
      (3+(3*bin+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux →
      3*(bin+1 : ℕ)*Z^τ ≤ T →
      allocatedPositiveRow source m A z t (fun i => primePool M H (bhi (f i)) (P i))
        (fun i I => idealCoeff (η₀ (f i)).inverse I*V (f i) ((I.absNorm : ℝ)/P i)) P
        D allocation W₁ W₂ X₁ X₂ ≠ 0 →
      ∃ data : SurvivingBufferedData η w Slot orders C edge e,
        data.slots = embeddedSlots (allocationSlotEmbedding f D allocation) ∧
        ‖allocatedPositiveRow source m A z t (fun i => primePool M H (bhi (f i)) (P i))
          (fun i I => idealCoeff (η₀ (f i)).inverse I*V (f i) ((I.absNorm : ℝ)/P i)) P
          D allocation W₁ W₂ X₁ X₂‖ = ‖data.value M H η₀ V bhi Z d‖ ∧
        d*data.length ≤ Real.logb Z (X₁*X₂*∏ i, P i)-
          Real.logb Z (formalReductionFactor D allocation P)+Real.logb Z (max 1 b₁*max 1 b₂) ∧
        data.ShortSlotGates M H hH η₀ Rwidth τ ηaux σmin σmax Z d T ∧
        (∀ j : data.slots, (Z^d)^(data.data.r j) = Pfull j.val) ∧
        (∀ j, data.data.σ j = 0 ∧ data.data.v j = 0) ∧ data.data.t = t ∧ data.data.bin = bin := by
  obtain ⟨C,hC,hdata⟩ := actual_source_allocated_buffered W₁ W₂ a₁ b₁ a₂ b₂
    ha₁ ha₂ hs₁ hW₁ hs₂ hW₂
  refine ⟨C,hC,?_⟩
  intro ι Slot instι instDι instSlot instDSlot f orders edge e hedge he M instM H hH
    η w parent N puncture hpuncture source m A z t hrow D allocation
    Z d X₁ X₂ η₀ V alo bhi P Pfull bin Rwidth τ ηaux σmin σmax T
    hPfull hZ hd hbase hX₁ hX₂ hR hX₁cap hX₂cap hP hσmin hσmax hconductor
    hfreq hfour htwo hbuffer hn
  have hPpos (i : ι) : 0 < P i := zero_lt_one.trans_le (hP i).1
  obtain ⟨P₁,P₂,h₁,h₂,hσ₁,hσ₂,ht₁,ht₂,hnorm,hlength⟩ :=
    hdata f orders edge e hedge he M H η w parent N puncture hpuncture
      source m A z t hrow D allocation Z d X₁ X₂ η₀ V bhi P bin
      hZ hd hbase hX₁ hX₂ hPpos hn
  let data := embeddedBufferedData (allocationSlotEmbedding f D allocation) orders C edge e
    (allocatedBufferedData parent N puncture hpuncture D allocation P₁ P₂ Z d X₁ X₂ P t bin)
  refine ⟨data,rfl,hnorm,hlength,?_,?_,(fun _ => ⟨rfl,rfl⟩),rfl,rfl⟩
  · have hscale : 1 ≤ (Z^d)^Rwidth := Real.one_le_rpow hbase.le hR
    have hc (X : ℝ) : 0 < clippedScale X := zero_lt_one.trans_le (clippedScale_ge_one X)
    refine ⟨Real.logb_nonneg hbase (clippedScale_ge_one _),?_,
      Real.logb_nonneg hbase (clippedScale_ge_one _),?_,?_,?_,?_,?_,?_,hfour,htwo,hbuffer⟩
    · exact (Real.logb_le_iff_le_rpow hbase (hc _)).mpr
        (allocated_plain_scale_le D allocation 0 X₁ _ hX₁.le hscale hX₁cap)
    · exact (Real.logb_le_iff_le_rpow hbase (hc _)).mpr
        (allocated_plain_scale_le D allocation 1 X₂ _ hX₂.le hscale hX₂cap)
    · intro j
      let i := ((embeddedSlotsEquiv (allocationSlotEmbedding f D allocation)).symm j).val
      exact ⟨Real.logb_nonneg hbase (hP i).1,
        (Real.logb_le_iff_le_rpow hbase (hPpos i)).mpr (hP i).2,hσmin,hσmax⟩
    · rintro (_ | ⟨j,θ⟩)
      · exact hconductor none
      · exact hconductor (some (j.val,θ))
    · simpa only [data,embeddedBufferedData,JointBufferedProductData.reindex,allocatedBufferedData,ht₁] using hfreq
    · simpa only [data,embeddedBufferedData,JointBufferedProductData.reindex,allocatedBufferedData,ht₂] using hfreq
    · intro j
      simpa only [data,embeddedBufferedData,JointBufferedProductData.reindex,allocatedBufferedData,add_zero] using hfreq
  · intro j
    change (Z^d)^Real.logb (Z^d)
      (P (((embeddedSlotsEquiv (allocationSlotEmbedding f D allocation)).symm j).val)) = Pfull j.val
    rw [Real.rpow_logb (zero_lt_one.trans hbase) (ne_of_gt hbase) (hPpos _),hPfull]
    congr 1
    exact embeddedSlotsEquiv_symm_val (allocationSlotEmbedding f D allocation) j

#print axioms actual_source_allocated_short_gates
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceShortGates -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Endpoint ; sha256 529de648decd1beab08e1748e11806143cdffb0f611aa0f17dd15252a468f7d8 -/
section



noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace Cycle25.Energy

open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyWidthRanges

local notation "O" => HeckeFamily.O

/-- Independent of the arithmetic family, slot count, profiles and target height. -/
def commonMesh (Mcap Bmask L ε : ℝ) : ℝ := fineMesh Mcap Bmask L (3 / 4) ε

theorem commonMesh_pos (Mcap Bmask L ε : ℝ) (hM : 0 ≤ Mcap)
    (hB : 0 ≤ Bmask) (hε : 0 < ε) : 0 < commonMesh Mcap Bmask L ε := by
  exact (bounds Mcap (finalSourceCap Mcap Bmask L ε) (3 / 4) ε hM
    (sourceCap_nonneg Mcap Bmask L hM hB _) (by norm_num) hε).2.2.2.2.1

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The original canonical ray-prime family with one common smooth slot profile.
The zero-slot input is supplied by the completed unconditional endpoint. -/
theorem terminal_positive_at
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap κ ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1 / 4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap)
    (hκlo : 7 / 10 ≤ κ) (hκhi : κ ≤ 3 / 4) (hε : 0 < ε)
    (hbeta : 51 / 100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2 * HeckeZeroSupremum.beta - 1 ≤ κ) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        PositiveAt (α := α) M H hH W bslot a b radial Bmask L
          (commonMesh Mcap Bmask L ε) lo hi Mcap ε κ Z η₀ Q J S C := by
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκlo hε hbeta hκbeta
  obtain ⟨J, S, hbound⟩ := certified_terminal (α := α) M H hH W bslot a b radial
    Bmask L lo hi Mcap κ ε hmask hMcap.le (by linarith) hε hcert
  have hmesh := compact_mesh_le Mcap Bmask L κ ε hMcap.le hmask hε hκlo hκhi
  refine ⟨J, S, ?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cz, Cp, _, hCp, hz⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cp, hCp, ?_⟩
  filter_upwards [hz] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p
    X₁ X₂ hX₁ hX₂ hLX₁ hLX₂ hcapacity
  exact hZ.2.2 T θ w σ v t height hw (fun i => (hwL i).trans hmesh)
    hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hLX₁ hLX₂ hcapacity

end Cycle25.Energy
end
/- END ORIGINAL MODULE Cycle25.Energy.Endpoint -/
