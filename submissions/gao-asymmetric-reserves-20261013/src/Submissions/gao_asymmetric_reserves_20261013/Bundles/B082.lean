/- Asymmetric reserve and endpoint refinement: Zhongpai Gao, with AI assistance. Adapts Kari Roegnvaldsson’s affine/reserve source at 14ab1618c5133a7d12e06aa76661bbcb34e843cd, following accepted c707738a659786b9a44a79c629bed8c801cca8f3. Original notices below are retained. -/
/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B005
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B013
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B014
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B047
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B056
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B059
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B075
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B080
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B081
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass

/- BEGIN ORIGINAL MODULE Analytic.JointCommonAnchorBins ; sha256 540c8fa0fbec2310cab0733cbb5cf914471119acf06f92b0381f706dbc0d3d2a -/
section



/-! With the actual common slot anchor, duplicate slot labels do not alter
the dictionary maximum. One finite bin assignment therefore supplies both
the low Unit-dictionary gate and the full high source-family bin. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDetectorZeros HeckePrimeRay HeckeInverseAmplification
open HeckeFiniteDeletion
open LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile ProbeHighRowFamily
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance commonAnchorBinsFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def commonAnchorMomentFamily (Slot : Type*) (η η₀ : Character) (w : NonzeroElement) :
    JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Character :=
  fun label => (momentData (jointRelativeParent η
    (relativeSlotTranslate M H hH (fun _ : Slot => η₀)) label)).character w

theorem commonAnchor_zeroMaximum {Slot : Type*} [Fintype Slot] [Nonempty Slot]
    (η η₀ : Character) (w : NonzeroElement)
    (hSlot : ∀ j,(commonAnchorMomentFamily M H hH Slot η η₀ w j).residue ≠ 1)
    (hUnit : ∀ j,(commonAnchorMomentFamily M H hH Unit η η₀ w j).residue ≠ 1)
    (T : ℝ) :
    zeroMaximum (commonAnchorMomentFamily M H hH Slot η η₀ w) hSlot T =
      zeroMaximum (commonAnchorMomentFamily M H hH Unit η η₀ w) hUnit T := by
  apply le_antisymm
  · apply zeroMaximum_le_of_zero_inclusion
    rintro ⟨parent,label⟩
    rcases label with _ | ⟨i,θ⟩
    · exact ⟨(parent,none),fun _ _ hz => hz⟩
    · exact ⟨(parent,some ((),θ)),fun _ _ hz => hz⟩
  · apply zeroMaximum_le_of_zero_inclusion
    rintro ⟨parent,label⟩
    rcases label with _ | ⟨i,θ⟩
    · exact ⟨(parent,none),fun _ _ hz => hz⟩
    · exact ⟨(parent,some (Classical.choice (inferInstance : Nonempty Slot),θ)),fun _ _ hz => hz⟩

/-- The source upper bin for all original slots implies the Unit-dictionary
upper bound used in low-slot removal, even with arbitrary source punctures. -/
theorem commonAnchor_source_bin_upper {Slot : Type*} [Fintype Slot] [Nonempty Slot]
    (η η₀ : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQM : Q ≤ M) (hQη₀ : Q ≤ η₀.modulus)
    (R : JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
    (hR : ∀ label,R label ≠ 0)
    (a e T : ℝ) (he : 0 < e) (w : NonzeroElement)
    (hbin : jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH (fun _ : Slot => η₀))
      Q hQ72 (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀) Q hQM (fun _ => hQη₀))
      R hR a (a+e) T w) :
    ∃ hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val,
      zeroMaximum (commonAnchorMomentFamily M H hH Unit η η₀ w)
        (jointRelativeMoment_nonprincipal η (relativeSlotTranslate M H hH (fun _ : Unit => η₀))
          Q hQ72 (relativeSlotTranslate_fixedQ M H hH (fun _ : Unit => η₀) Q hQM
            (fun _ => hQη₀)) w hex) T < a+2*e := by
  obtain ⟨hex,hlo,hupper⟩ := hbin
  rw [jointRelativeSource_zeroMaximum η (relativeSlotTranslate M H hH (fun _ : Slot => η₀))
    Q hQ72 (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀) Q hQM
      (fun _ => hQη₀)) w hex R hR T] at hupper
  have hmax := commonAnchor_zeroMaximum (Slot := Slot) M H hH η η₀ w
    (jointRelativeMoment_nonprincipal η (relativeSlotTranslate M H hH (fun _ : Slot => η₀))
      Q hQ72 (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀) Q hQM
        (fun _ => hQη₀)) w hex)
    (jointRelativeMoment_nonprincipal η (relativeSlotTranslate M H hH (fun _ : Unit => η₀))
      Q hQ72 (relativeSlotTranslate_fixedQ M H hH (fun _ : Unit => η₀) Q hQM
        (fun _ => hQη₀)) w hex) T
  change zeroMaximum (commonAnchorMomentFamily M H hH Slot η η₀ w) _ T ≤ a+e at hupper
  rw [hmax] at hupper
  exact ⟨hex,by linarith⟩

open CenteredMomentEnergyState

theorem eventually_supported_low_gate_of_common_bin
    {Slot : Type*} [Fintype Slot] [Nonempty Slot]
    (η₀ : Character) (radial ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (Bmask d : ℝ) (s : NaturalState Z Bmask radial),
      s.width+Bmask+ξ ≤ d →
      ∀ (η : Character) (Q : Ideal O) (hQM : Q ≤ M)
        (hQ : s.fixedModulus = internalQ Q η₀)
        (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)})
        (w : NonzeroElement) (parent : JointParentLabel η) (N : NaturalRow parent.val w.val)
        (R : Ideal O), R ≠ 0 →
      ∀ (z : O) (hz : (supportedNaturalState s).radial.keep z),
      (∀ I : Ideal O,
        idealCoeff (excluded (naturalRow s.character z (s.row_ne_zero z hz.1)).character s.puncture) I =
          idealCoeff (excluded N.character R) I) →
      ∀ (τ e a : ℝ) (k : ℕ), 0 < e →
      ∀ (holes : JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hholes : ∀ label,holes label ≠ 0),
      jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH (fun _ : Slot => η₀))
        (internalQ Q η₀) hQ72
        (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀) (internalQ Q η₀)
          (inf_le_left.trans hQM) (fun _ => inf_le_right))
        holes hholes a (a+e) (3*(k+1 : ℕ)*Z^τ) w →
      NaturalLowGate M H hH (supportedNaturalState s) η₀ Q hQM hQ d τ e a k z hz := by
  filter_upwards [eventually_supported_low_gate M H hH η₀ radial ξ hξ] with Z hgate
  refine ⟨hgate.1,?_⟩
  intro Bmask d s hd η Q hQM hQ hQ72 w parent N R hR z hz hcoeff τ e a k he holes hholes hbin
  obtain ⟨hex,hupper⟩ := commonAnchor_source_bin_upper M H hH η η₀ (internalQ Q η₀)
    hQ72 (inf_le_left.trans hQM) inf_le_right holes hholes a e (3*(k+1 : ℕ)*Z^τ) he w hbin
  exact hgate.2 Bmask d s hd η Q hQM hQ hQ72 w hex parent N R hR z hz hcoeff
    τ e a k hupper

/-- The local positive total prime width guarantees that collapsing the
duplicate anchors to Unit does not introduce a missing slot translate. -/
theorem slot_nonempty_of_positive_total {Slot : Type*} [Fintype Slot]
    (w : Slot → ℝ) (hw : 0 < ∑ i,w i) : Nonempty Slot := by
  rcases isEmpty_or_nonempty Slot with h | h
  · letI : IsEmpty Slot := h
    simpa using hw
  · exact h

theorem buffered_edge_low_or_high (a : ℝ) (hupper : a ≤ 7/8) :
    a ≤ 167/200 ∨ (67/100 ≤ 2*a-1 ∧ 2*a-1 ≤ 3/4) := by
  by_cases h : a ≤ 167/200
  · exact Or.inl h
  · exact Or.inr ⟨by linarith,by linarith⟩

/-- Choose one finite bin function on the reconstructed rows. It supplies
both the full source-family bin, for every finite deletion, and the Unit
upper maximum used by the low source theorem. No allocation is counted
by choosing a second bin. -/
theorem exists_common_anchor_source_bins
    {Row Slot : Type*} [Fintype Slot] [Nonempty Slot]
    (η η₀ : Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQM : Q ≤ M) (hQη₀ : Q ≤ η₀.modulus)
    (w : Row → NonzeroElement)
    (hex : ∀ u, ¬FixedInducingRow η Q fixedBadMask 1 (w u).val)
    (T e : ℝ) (hT : 2 < T) (he : 0 < e)
    (I : ℕ) (hI : 0 < I) (hwidth : (49/100 : ℝ) ≤ I*(e/2))
    (hβupper : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ bin : Row → Fin (I+1) × Fin (I+1), ∀ u,
      1 ≤ (bin u).1.val ∧
      let a : ℝ := 51/100+(e/2)*((bin u).2.val : ℝ)
      51/100 ≤ a ∧ a ≤ 7/8 ∧
      (a ≤ 167/200 ∨ (67/100 ≤ 2*a-1 ∧ 2*a-1 ≤ 3/4)) ∧
      (∀ (R : JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ label, R label ≠ 0),
        jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH (fun _ : Slot => η₀))
          Q hQ72 (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀)
            Q hQM (fun _ => hQη₀)) R hR a (a+e)
          ((3*((bin u).1.val+1) : ℕ)*T) (w u)) ∧
      zeroMaximum (commonAnchorMomentFamily M H hH Unit η η₀ (w u))
        (jointRelativeMoment_nonprincipal η (relativeSlotTranslate M H hH (fun _ : Unit => η₀))
          Q hQ72 (relativeSlotTranslate_fixedQ M H hH (fun _ : Unit => η₀)
            Q hQM (fun _ => hQη₀)) (w u) (hex u))
        ((3*((bin u).1.val+1) : ℕ)*T) < a+2*e := by
  obtain ⟨bin,hbin⟩ := exists_joint_source_buffered_bins η
    (relativeSlotTranslate M H hH (fun _ : Slot => η₀)) Q hQ72
    (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀) Q hQM (fun _ => hQη₀))
    w hex T e hT he I hI hwidth hβupper
  refine ⟨bin,?_⟩
  intro u
  obtain ⟨hi,ha,hsource⟩ := hbin u
  refine ⟨hi,?_,ha,buffered_edge_low_or_high _ ha,hsource,?_⟩
  · have hnonneg : 0 ≤ (e/2)*((bin u).2.val : ℝ) := by positivity
    linarith
  · obtain ⟨_,hupper⟩ := commonAnchor_source_bin_upper (Slot := Slot) M H hH η η₀ Q
      hQ72 hQM hQη₀ (fun _ => 1) (fun _ => one_ne_zero)
      _ e ((3*((bin u).1.val+1) : ℕ)*T) he (w u)
      (hsource (fun _ => 1) (fun _ => one_ne_zero))
    exact hupper

#print axioms commonAnchor_zeroMaximum
#print axioms commonAnchor_source_bin_upper
#print axioms eventually_supported_low_gate_of_common_bin
#print axioms exists_common_anchor_source_bins
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCommonAnchorBins -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighScalar ; sha256 5add2cfead5846e05e01566aa2538fcfbf732e1786f4a0b03b07313b9441dca0 -/
section


/-! Exact scalar normalization for the high physical kernel. The actual
annular-prime cardinality is paid by its source theorem; the second projector
is already included in the retained allocation mass and is not counted again. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentFirstAmplificationChoice CenteredMomentPrimePool
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

def actualHighPrimeCount (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (Z : ℝ) : ℝ :=
  (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(3/500 : ℝ))).card

theorem eventually_actual_high_prime_ratio (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (Sbad : Finset (Ideal O)) (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ 0 < actualHighPrimeCount M H Sbad Z ∧
      Z^(3/500 : ℝ)/actualHighPrimeCount M H Sbad Z ≤ Z^loss := by
  filter_upwards [eventually_actual_pool_card M H hH Sbad (3/500) loss (by norm_num) hloss,
    eventually_gt_atTop (1 : ℝ)] with Z hcard hZ
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hp : 0 < actualHighPrimeCount M H Sbad Z := (Real.rpow_pos_of_pos hz _).trans_le hcard
  refine ⟨hZ,hp,(div_le_iff₀ hp).mpr ?_⟩
  calc
    Z^(3/500 : ℝ) = Z^loss*Z^((3/500 : ℝ)-loss) := by
      rw [←Real.rpow_add hz]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard (by positivity)

theorem secondPrecountFactor_change_prime (H p q : ℝ)
    (hH : H ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (K : ℝ) (n : Fin 4 → ℤ) :
    secondPrecountFactor H p C D U K n = (q/p)*secondPrecountFactor H q C D U K n := by
  unfold secondPrecountFactor
  field_simp

/-- The direct-common amplifier uses original source volume. Passing from
that denominator to common volume retains its exact inverse first-common
norm factor. -/
theorem secondPrecountFactor_common_volume (V P N : ℝ)
    (hV : V ≠ 0) (hN : N ≠ 0)
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (K : ℝ) (n : Fin 4 → ℤ) :
    secondPrecountFactor V P C D U K n =
      N⁻¹*secondPrecountFactor (V/N) P C D U K n := by
  unfold secondPrecountFactor
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  field_simp

namespace CommonSecondKernelLabel
variable {Slot : Type*} [Fintype Slot]

def actualPrecount (s : CommonSecondKernelLabel Slot)
    (Z A c primeCount K : ℝ) (n : Fin 4 → ℤ) : ℝ :=
  secondPrecountFactor (Z^(A-c)) primeCount s.second.val.1 s.second.val.2 s.partition K n

theorem actualPrecount_eq (s : CommonSecondKernelLabel Slot)
    (Z A c d R₁ E₁ omega g₂ t₂ b₂ primeCount K : ℝ) (n : Fin 4 → ℤ)
    (hZ : 1 < Z) (hp : 0 < primeCount)
    (hK : K = Z^(2*A-c-d+R₁+E₁-1+max (d-c) 0+6*(3/500)+omega))
    (hg : Real.logb Z ((Ideal.span {commonFrequencyGenerator s.second.val.1 s.second.val.2}).absNorm : ℝ) = g₂)
    (ht : Real.logb Z ((∏ Q ∈ s.partition, Q.val).absNorm : ℝ) = t₂)
    (hb : (Real.logb Z (s.second.val.1.absNorm : ℝ)+Real.logb Z (s.second.val.2.absNorm : ℝ))/2 = b₂) :
    s.actualPrecount Z A c primeCount K n =
      (Z^(3/500 : ℝ)/primeCount)*Z^(A-min c d+R₁+E₁-1+5*(3/500)+g₂-t₂-b₂+omega) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  unfold actualPrecount
  rw [secondPrecountFactor_change_prime _ primeCount (Z^(3/500 : ℝ))
    (Real.rpow_pos_of_pos hz _).ne' hp.ne' (Real.rpow_pos_of_pos hz _).ne',hK,
    enlarged_second_precount_factor Z A c d R₁ E₁ 1 (3/500) omega hZ
      s.second.val.1 s.second.val.2 s.toKernelLabel.hC s.toKernelLabel.hD s.partition n,
    hg,ht,hb]
  congr 2
  ring

end CommonSecondKernelLabel

/-- Exact normalization of the complete weighted joint kernel sum, before
using any high-bin bound. The actual prime count is the only added scalar. -/
theorem joint_actual_precount_norm_sum
    {α Slot : Type*} [Fintype Slot]
    (S : Finset α) (s : α → CommonSecondKernelLabel Slot) (Ds : α → Finset (Ideal O))
    (t K Radius : α → ℝ) (n : α → Fin 4 → ℤ) (z : α → O) (rayWeight : α → ℂ)
    (Wkernel : SchwartzMap ℝ ℂ) (decay : ℕ)
    (Z A c d R₁ E₁ omega g₂ t₂ b₂ primeCount : ℝ)
    (hZ : 1 < Z) (hp : 0 < primeCount)
    (hK : ∀ v ∈ S, K v = Z^(2*A-c-d+R₁+E₁-1+max (d-c) 0+6*(3/500)+omega))
    (hg : ∀ v ∈ S, Real.logb Z ((Ideal.span {commonFrequencyGenerator (s v).second.val.1 (s v).second.val.2}).absNorm : ℝ) = g₂)
    (ht : ∀ v ∈ S, Real.logb Z ((∏ Q ∈ (s v).partition, Q.val).absNorm : ℝ) = t₂)
    (hb : ∀ v ∈ S, (Real.logb Z ((s v).second.val.1.absNorm : ℝ)+Real.logb Z ((s v).second.val.2.absNorm : ℝ))/2 = b₂) :
    (∑ v ∈ S, ∑ D ∈ Ds v,
      ‖(((1+SecondKernelLabel.kernelScale (n v))^decay : ℝ) : ℂ)*
        ((UniqueFactorizationMonoid.moebius D : ℂ)*
          ((s v).actualPrecount Z A c primeCount (K v) (n v) : ℂ)*rayWeight v)*
        ((s v).withProjector D).toKernelLabel.kernelRow (t v) (z v) Wkernel (K v) (Radius v) (n v)‖) =
    (Z^(3/500 : ℝ)/primeCount)*
      (∑ v ∈ S, ∑ D ∈ Ds v,
        ‖(((1+SecondKernelLabel.kernelScale (n v))^decay : ℝ) : ℂ)*
          ((UniqueFactorizationMonoid.moebius D : ℂ)*
            ((Z^(A-min c d+R₁+E₁-1+5*(3/500)+g₂-t₂-b₂+omega) : ℝ) : ℂ)*rayWeight v)*
          ((s v).withProjector D).toKernelLabel.kernelRow (t v) (z v) Wkernel (K v) (Radius v) (n v)‖) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro D hD
  rw [(s v).actualPrecount_eq Z A c d R₁ E₁ omega g₂ t₂ b₂ primeCount (K v) (n v)
    hZ hp (hK v hv) (hg v hv) (ht v hv) (hb v hv)]
  rw [Complex.ofReal_mul]
  have he (a b q x y : ℂ) : a*(b*(q*x)*y) = q*(a*(b*x*y)) := by ring
  rw [he,mul_assoc,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < Z^(3/500 : ℝ)/primeCount)]

#print axioms eventually_actual_high_prime_ratio
#print axioms joint_actual_precount_norm_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighScalar -/

/- BEGIN ORIGINAL MODULE Analytic.JointLocalErrorCores ; sha256 e4cea540269d86a2a97b7ed5f896371c337e46cd39a95ec07351619b9b1d6e9d -/
section




/-! The actual local source geometry pays all four error entries. The
first entry uses the refined affine defect; the exceptional entry uses
the genuine minimum plain scale; diagonal and tail retain the source
volume saving. The literal prime average remains normalized. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedNormalization
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentFirstMixedAllowance CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentFirstMixedDiagonal CenteredMomentAmplifiedRetainedRadius RayFourExpansion
open CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstPhysicalSource
local notation "O" => HeckeFamily.O

def localErrorExponents (paid eps Mcap saving delta reserve : ℝ) : Fin 4 → ℝ :=
  ![paid-1/1250, -9/100+5*(delta+reserve)/6,
    -49/500+delta+reserve+eps*Mcap, -49/500+delta+reserve-saving]

/-- All four literal error cores are bounded using source gates only.
The plain-scale lower cap is supplied by `actual_errorInput_plain_lower`. -/
theorem actual_refined_local_error_cores
    (η τ : Character) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (E : Finset (CommonIndex C D))
    (K V Z delta reserve paid eps saving Mgeom Mdecl Mcap : ℝ)
    (hK : 0 < K) (hV : 0 < V) (hZ : 1 < Z) (heps : 0 ≤ eps)
    (hdef : Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)) ≤ 1/241)
    (hgeom : 1 ≤ Mgeom)
    (hwidth : Mgeom ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+
      Real.logb Z fixedPresentationCost)
    (hvolume : Real.logb Z V ≤ (883/1000)*Mgeom)
    (hcap : Real.logb Z V ≤ Mcap)
    (hfixed : Real.logb Z fixedPresentationCost ≤ 1/1000)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*activeConductor C D})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (p : O) (hp : p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hlog : 9/2000 ≤ Real.logb Z (normValue p)) :
    let M0 := Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)
    let Kerror := errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K V Z)
      (Real.logb Z (C.absNorm : ℝ)) (9/500) delta reserve p k
    ∀ j : Fin 4,
      errorCores p k (τ.modulus.absNorm : ℝ) V (C.absNorm : ℝ) Z
        (allowance C D Z) Kerror (refinedErrorDeficit p Z k (9/500) (Mdecl-M0))
        paid eps saving (Mgeom/4-Real.logb Z (C.absNorm : ℝ)-errorRemoval p Z k) j ≤
      Z^(localErrorExponents paid eps Mcap saving delta reserve j) := by
  dsimp only
  have hpdata := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad _ _ _ Q hQ).2) p hp
  have hp0 := hpdata.1.ne_zero
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hgap : Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ))+9/500 ≤
      -(49/500 : ℝ) := by linarith
  intro j
  fin_cases j
  · exact refined_error_main_core p hp0 k hk _ V _ Z _ _ _ paid eps saving _
      (norm_pos τ.modulus τ.modulus_ne_bot) hV (norm_pos C hC.1) hZ
      (allowance_nonneg _ _ _) hdef hlog
  · exact actual_local_error_core_one η τ C D hC hD hCD E K V Z (9/500)
      delta reserve Mgeom _ paid eps saving hZ hK hV le_rfl hmod M H Sbad hbad p hp k hk
      hgeom hwidth hvolume
  · have hh := actual_error_diagonal η τ C D hC hD hCD E K V Z (9/500) delta reserve eps
      hK hV hZ heps hmod p hp0 k hk
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [localErrorExponents]
    have hhcap := mul_le_mul_of_nonneg_left hcap heps
    linarith
  · have hh := actual_error_diagonal η τ C D hC hD hCD E K V Z (9/500) delta reserve 0
      hK hV hZ (by norm_num) hmod p hp0 k hk
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    rw [← Real.rpow_add hz] at ht
    have hcore : errorCores p k (τ.modulus.absNorm : ℝ) V (C.absNorm : ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K V Z)
          (Real.logb Z (C.absNorm : ℝ)) (9/500) delta reserve p k)
        (refinedErrorDeficit p Z k (9/500) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ))))
        paid eps saving (Mgeom/4-Real.logb Z (C.absNorm : ℝ)-errorRemoval p Z k) 3 ≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ))+
          9/500+delta+reserve-saving) := by
      convert ht using 1 <;> dsimp [errorCores,reference] <;> ring
    apply hcore.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [localErrorExponents]
    linarith

theorem actual_refined_local_error_average
    (η τ : Character) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (E : Finset (CommonIndex C D))
    (K V Z delta reserve paid eps saving Mgeom Mdecl Mcap : ℝ)
    (hK : 0 < K) (hV : 0 < V) (hZ : 1 < Z) (heps : 0 ≤ eps)
    (hdef : Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)) ≤ 1/241)
    (hgeom : 1 ≤ Mgeom)
    (hwidth : Mgeom ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+
      Real.logb Z fixedPresentationCost)
    (hvolume : Real.logb Z V ≤ (883/1000)*Mgeom)
    (hcap : Real.logb Z V ≤ Mcap)
    (hfixed : Real.logb Z fixedPresentationCost ≤ 1/1000)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*activeConductor C D})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (hP : (primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))).Nonempty)
    (hlog : ∀ p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))),
      9/2000 ≤ Real.logb Z (normValue p)) :
    let P := primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))
    let M0 := Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)
    let Kerror := fun (p : elementPool P) (i : Fin 3) =>
      errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K V Z)
        (Real.logb Z (C.absNorm : ℝ)) (9/500) delta reserve p (errorIndex i+1)
    ∀ j : Fin 4,
      (56/(P.card : ℝ))*(∑ p : elementPool P, ∑ i : Fin 3,
        16*(errorIndex i+2 : ℝ)^2*∑ _χ : RayCharacter,
          errorCores p (errorIndex i+1) (τ.modulus.absNorm : ℝ) V (C.absNorm : ℝ) Z
            (allowance C D Z) (Kerror p i)
            (refinedErrorDeficit p Z (errorIndex i+1) (9/500) (Mdecl-M0))
            paid eps saving (Mgeom/4-Real.logb Z (C.absNorm : ℝ)-errorRemoval p Z (errorIndex i+1)) j) ≤
      (56*1872*(Fintype.card RayCharacter : ℝ))*
        Z^(localErrorExponents paid eps Mcap saving delta reserve j) := by
  dsimp only
  intro j
  let P := primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))
  have hp : ∀ Q ∈ P, Prime Q := fun Q hQ =>
    (primePool_data M H Sbad hbad _ _ _ Q hQ).1
  have hb : ∀ Q ∈ P, Q ∉ fixedBadPrimes := fun Q hQ =>
    (primePool_data M H Sbad hbad _ _ _ Q hQ).2
  have hh := actual_error_average P hP hp hb
    (fun p i _χ => errorCores p (errorIndex i+1) (τ.modulus.absNorm : ℝ) V (C.absNorm : ℝ) Z
      (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K V Z)
        (Real.logb Z (C.absNorm : ℝ)) (9/500) delta reserve p (errorIndex i+1))
      (refinedErrorDeficit p Z (errorIndex i+1) (9/500)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ))))
      paid eps saving (Mgeom/4-Real.logb Z (C.absNorm : ℝ)-errorRemoval p Z (errorIndex i+1)) j)
    (Z^(localErrorExponents paid eps Mcap saving delta reserve j))
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) ?_
  · convert mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 56 by norm_num) using 1 <;> ring
  · intro p i χ
    exact actual_refined_local_error_cores η τ C D hC hD hCD E K V Z delta reserve paid eps saving
      Mgeom Mdecl Mcap hK hV hZ heps hdef hgeom hwidth hvolume hcap hfixed hmod
      M H Sbad hbad p p.property (errorIndex i+1) (first_extracted_error_indices i)
      (hlog p p.property) j

/-- The four source losses remain under the same first-label sum and
the same normalized prime average. There is no label cardinality factor. -/
theorem joint_error_four_average {Λ : Type*}
    (labels : Finset Λ) (weight : Λ → ℝ) (Hcoef exponent : Λ → Fin 4 → ℝ)
    (P : Finset (Ideal O)) (hne : P.Nonempty)
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (Z : ℝ) (hZ : 0 ≤ Z)
    (f : elementPool P → Λ → Fin 3 → RayCharacter → Fin 4 → ℝ)
    (hw : ∀ l ∈ labels, 0 ≤ weight l)
    (hH : ∀ l ∈ labels, ∀ j, 0 ≤ Hcoef l j)
    (hf : ∀ p l, l ∈ labels → ∀ i χ j, f p l i χ j ≤ Z^(exponent l j)) :
    (56/(P.card : ℝ))*(∑ p : elementPool P, ∑ l ∈ labels, weight l*
      ∑ i : Fin 3, 16*(errorIndex i+2 : ℝ)^2*
        ∑ χ : RayCharacter, ∑ j : Fin 4, Hcoef l j*f p l i χ j) ≤
      (56*1872*(Fintype.card RayCharacter : ℝ))*
        (∑ l ∈ labels, weight l*∑ j : Fin 4, Hcoef l j*Z^(exponent l j)) := by
  apply joint_amplification_error_average labels weight
    (fun l => ∑ j : Fin 4, Hcoef l j*Z^(exponent l j)) P hne hp hbad
    (fun p l i χ => ∑ j : Fin 4, Hcoef l j*f p l i χ j) hw
  · intro l hl
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hH l hl j) (Real.rpow_nonneg hZ _))
  · intro p l hl i χ
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hf p l hl i χ j) (hH l hl j))

/-- A concrete open reserve remains after paying small Gaussian source
losses. This is only arithmetic; the preceding theorem supplies the actual
four analytic error estimates. -/
lemma local_error_source_reserve
    (paid eps Mcap saving delta reserve : ℝ) (loss : Fin 4 → ℝ)
    (hpaid : paid ≤ 1/10000) (hloss : ∀ j, loss j ≤ 1/10000)
    (hfrequency : delta+reserve ≤ 1/1000) (heps : eps*Mcap ≤ 1/1000)
    (hsaving : 0 ≤ saving) :
    ∀ j : Fin 4, loss j+localErrorExponents paid eps Mcap saving delta reserve j ≤ -(1/2000 : ℝ) := by
  intro j
  have hj := hloss j
  fin_cases j <;> norm_num [localErrorExponents] at hj ⊢ <;> linarith

#print axioms actual_refined_local_error_cores
#print axioms actual_refined_local_error_average
#print axioms joint_error_four_average
#print axioms local_error_source_reserve
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLocalErrorCores -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowCommon ; sha256 68ffc860b369bc5e48f946c73c0b12fa0241221451fde8803ff2cd76c879732a -/
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
local instance lowCommonFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


variable {α : Type*} [Fintype α] [DecidableEq α]

theorem actual_common_low_from_parent
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap εmoment : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
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
    (Mslot εmask : ℝ) (hMslot : 0 ≤ Mslot) (hεmask : 0 < εmask) :
    ∃ (degree : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M), internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
        (v height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
      ∀ (s : NaturalState Z Bmask radial) (hQ : s.fixedModulus = internalQ Q η₀),
      s.puncture = 1 → s.width ≤ Mcap → ∀ (low : O → Prop) (abin : ℝ) (k : ℕ),
      51/100 ≤ abin → abin ≤ 167/200 → 2 ≤ Z^d → 2 < Z^τ →
      (∀ z, ∀ hz : (supportedNaturalState s).radial.keep z, low z →
        NaturalLowGate M H hH (supportedNaturalState s) η₀ Q hQM hQ d τ e abin k z hz) →
      (∀ i, |v+freq i|+Z^τ/2 ≤ (3*k+2 : ℕ)*Z^τ) →
      (3+(3*k+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηheight →
      ∀ (p : Profiles a b),
      ∀ src : Input α, Matches M H hH src η₀ θ w σ freq W bslot Z →
      (∀ i,src.hi i ≤ bslot) → (∀ i,src.M i ≤ Mslot) →
      p.profile 0 = src.W₁ → p.profile 1 = src.W₂ →
      ∀ (C R : Ideal O) (B : actualAllocations src.pools C) (D : Ideal O)
        (alloc : Allocation D (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2))),
      R ≠ 0 →
      let data := commonData (withHeight src s.character v) C R B
      data.X₁ ≤ Z^L → data.X₂ ≤ Z^L → data.Y₁ ≤ Z^L → data.Y₂ ≤ Z^L →
      ∀ A Mparent nominal pad g allowance geometryLoss clip : ℝ,
      A+(7/2)*(∑ i : CenteredMomentCommonProfile.liveIndices B.val,w i.val) ≤ Mparent →
      Real.logb Z (data.X₁*data.X₂*∏ i : CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-nominal ≤
        A-Mparent+6*(3/500)+g+geometryLoss →
      0 ≤ pad → s.width ≤ nominal+pad → 0 ≤ g → g ≤ 1/241 →
      3/500 ≤ allowance → 0 ≤ geometryLoss → 0 ≤ clip →
      Real.logb Z (max 1 b*max 1 b) ≤ 2*clip →
      pad+loss+(67/450)*(geometryLoss+2*clip) ≤ 1/2000000 →
      childEnergy data (restrictedLowRadial s.radial low) D alloc ≤
      Cbound*((R*C).radical.absNorm : ℝ)^εmask*diagonalControl s.radial.profile*(p.control S)^2*(1+|v|+height)^degree *
        Z^(nominal+allowance-1/48000) := by
  obtain ⟨degree,S,hmain⟩ := actual_allocated_low_from_parent (α := α) M H hH W
    aslot bslot a b radial Bmask L lo hi Mcap εmoment haslot hWs hW hbslot
    ha haUpper hb hrad hmask hMcap hL hεmoment hbeta hbetaTop
    Rwidth d τ εslot e κ ηheight loss hRw hd hτ hεslot he he' hκ hη hbudget
    mesh hmesh hmeshInc hmeshWidth hmeshLoss
  obtain ⟨Cm,hCm,hcommon⟩ := actual_common_from_energy (α := α) (fun _ => bslot) (fun _ => Mslot)
    (fun _ => hMslot) εmask hεmask
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hmain⟩ := hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨2*Cm*Cbound,by positivity,?_⟩
  filter_upwards [hmain] with Z hmain
  refine ⟨hmain.1,?_⟩
  intro θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq s hQ hunit hs low abin k
    habin habinTop hbase hT hlow hfreqGate hheightSource p src hmatch hhi hMs hp₁ hp₂
    C R B D alloc hR data hX₁ hX₂ hY₁ hY₂
    A Mparent nominal pad g allowance geometryLoss clip hparent hshift
    hpad hwidth hg hgcap hallowance hgeometry hclip hclipCost hbudgetLoss
  let V₁ := sourcePlain a b ha (p.profile 0) (p.support 0)
  let V₂ := sourcePlain a b ha (p.profile 1) (p.support 1)
  let rad := restrictedLowRadial (supportedNaturalState s).radial low
  let E := Cbound*diagonalControl s.radial.profile*(p.control S)^2*(1+|v|+height)^degree*
    Z^(nominal+allowance-1/48000)
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hZpos : 0 < Z := zero_lt_one.trans hmain.1
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hleft : ∀ X₁ X₂ : ℝ,∀ h₁ : 0 < X₁,∀ h₂ : 0 < X₂,X₁ ≤ Z^L → X₂ ≤ Z^L →
      X₁*X₂ = data.X₁*data.X₂ →
      ∀ F₁ F₂ : Finset (Ideal O),(∀ I ∈ F₁,I ≠ 0) → (∀ I ∈ F₂,I ≠ 0) →
      ∀ J,allocatedEnergy s.character rad D alloc V₁ V₂ data.slots data.coefficient data.P
        v X₁ X₂ h₁ h₂ F₁ F₂ J ≤ E := by
    intro X₁ X₂ h₁ h₂ hc₁ hc₂ hprod F₁ F₂ hF₁ hF₂ J
    exact hmain.2 θ w σ freq v height hw hwmesh hσlo hσhi hheight hfreq
      (supportedNaturalState s) hQ hunit hs low abin k habin habinTop hbase hT hlow hfreqGate hheightSource
      p X₁ X₂ h₁ h₂ hc₁ hc₂ src hmatch C R B D alloc J F₁ F₂ hF₁ hF₂
      A Mparent nominal pad g allowance geometryLoss clip hparent
      (by simpa only [hprod] using hshift) hpad hwidth hg hgcap hallowance
      hgeometry hclip hclipCost hbudgetLoss
  have hh := hcommon src hhi hMs s.character v C R hR B D alloc V₁ V₂ hp₁ hp₂ rad
    (fun z hz => s.row_ne_zero z hz.1.1) E E hE hE (by
      intro left F₁ hF₁ F₂ hF₂ J hJ
      have hf₁ : ∀ I ∈ F₁,I ≠ 0 := fun I hi =>
        (CenteredMomentNaturalRowSource.support_prime (R*C) I ((Finset.mem_powerset.mp hF₁) hi)).ne_zero
      have hf₂ : ∀ I ∈ F₂,I ≠ 0 := fun I hi =>
        (CenteredMomentNaturalRowSource.support_prime (R*C) I ((Finset.mem_powerset.mp hF₂) hi)).ne_zero
      cases left
      · exact hleft data.Y₁ data.Y₂ data.Y₁_pos data.Y₂_pos hY₁ hY₂ data.same_product F₁ F₂ hf₁ hf₂ J
      · exact hleft data.X₁ data.X₂ data.X₁_pos data.X₂_pos hX₁ hX₂ rfl F₁ F₂ hf₁ hf₂ J)
  change childEnergy data (restrictedLowRadial (supportedNaturalState s).radial low) D alloc ≤ _ at hh
  rw [supportedNaturalState_childEnergy] at hh
  apply hh.trans_eq
  dsimp [E,rad,restrictedLowRadial,supportedNaturalState]
  ring

#print axioms actual_common_low_from_parent
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowCommon -/

/- BEGIN ORIGINAL MODULE Analytic.JointSecondAbsolute ; sha256 51e6a761d9c5ba2075e08f60269bc5edb0fd95810693e248a36e1b8efc45894c -/
section


/-! Absolute coefficient control of the actual projected children. This
estimate is uniform in all three Fourier variables and keeps the joint
arithmetic sum intact. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSecondSectorColumns CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentAbsoluteEnergy
open CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

def sourceAbsoluteMass (S : Finset (Ideal O)) (β : Ideal O → ℂ) : ℝ :=
  ∑ I ∈ S, ‖β I‖

theorem sourceAbsoluteMass_nonneg (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    0 ≤ sourceAbsoluteMass S β := Finset.sum_nonneg (fun I _ => norm_nonneg _)

theorem sourceAbsoluteMass_le_card (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (B : ℝ) (hB : ∀ I ∈ S, ‖β I‖ ≤ B) :
    sourceAbsoluteMass S β ≤ (S.card : ℝ)*B := by
  simpa only [sourceAbsoluteMass, Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hB

theorem sourceAbsoluteMass_le_power (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (Z A B : ℝ) (hZ : 0 < Z) (hcard : (S.card : ℝ) ≤ Z^A)
    (hβ : ∀ I ∈ S, ‖β I‖ ≤ Z^B) : sourceAbsoluteMass S β ≤ Z^(A+B) := by
  exact (sourceAbsoluteMass_le_card S β (Z^B) hβ).trans
    ((mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq
      (Real.rpow_add hZ A B).symm)

theorem residual_absolute_mass_le (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (C : Ideal O) (hC : C ≠ 0) :
    (∑ I ∈ supportedColumns (residualPool C hC S), ‖β (C*I)‖) ≤
      sourceAbsoluteMass S β := by
  let Q := supportedColumns (residualPool C hC S)
  have hsub : Q.image (fun I => C*I) ⊆ S := by
    intro J hJ
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact (mem_residualPool C hC S I).mp (Finset.mem_filter.mp hI).1
  calc
    _ = ∑ I ∈ Q.image (fun I => C*I), ‖β I‖ := by
      rw [Finset.sum_image]
      intro I hI J hJ he
      exact mul_left_cancel₀ hC he
    _ ≤ sourceAbsoluteMass S β :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ => norm_nonneg _)

theorem secondChildValue_absolute (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C : Ideal O) (hC : Supported C)
    (A : O) (L : Ideal O) (χ : RayCharacter) (z : O) (H : ℝ) :
    ‖secondChildValue η t S β C hC A L χ z H‖ ≤
      (Real.sqrt H)⁻¹ * sourceAbsoluteMass S β := by
  rw [secondChildValue, second_child_sum_eq_source, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg H)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg H))
  apply (norm_sum_le _ _).trans
  apply le_trans _ (residual_absolute_mass_le S β C hC.1)
  apply Finset.sum_le_sum
  intro I hI
  by_cases hc : IsCoprime C I
  · by_cases hL : L ∣ I
    · simp only [hc,hL,if_true,mul_one,norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (rowWeight_norm_le_one_all _ _ _ _ _ _)
    · simp [hL]
  · simp [hc]

namespace SecondKernelLabel

def absoluteEnvelope (s : SecondKernelLabel) (H₁ H₂ : ℝ) : ℝ :=
  (Real.sqrt H₁)⁻¹*(Real.sqrt H₂)⁻¹*(sourceAbsoluteMass s.columns s.beta)^2

theorem absoluteEnvelope_nonneg (s : SecondKernelLabel) (H₁ H₂ : ℝ) :
    0 ≤ s.absoluteEnvelope H₁ H₂ := by unfold absoluteEnvelope; positivity

theorem values_le_absoluteEnvelope (s : SecondKernelLabel) (t₁ t₂ : ℝ)
    (z : O) (H₁ H₂ : ℝ) :
    ‖s.leftValue t₁ z H₁‖*‖s.rightValue t₂ z H₂‖ ≤ s.absoluteEnvelope H₁ H₂ := by
  have hL := secondChildValue_absolute s.parent t₁ s.columns s.beta s.C s.hC
    s.frequency s.projector s.leftRay z H₁
  have hR := secondChildValue_absolute s.parent t₂ s.columns s.beta s.D s.hD
    s.frequency s.projector (s.rightRay⁻¹) (-z) H₂
  exact (mul_le_mul hL hR (norm_nonneg _) (mul_nonneg
    (inv_nonneg.mpr (Real.sqrt_nonneg _)) (sourceAbsoluteMass_nonneg _ _))).trans_eq
      (by unfold absoluteEnvelope; ring)

end SecondKernelLabel

/-- Unit phases turn the joint integral estimate into a sum of physical
block norms without a cardinality loss. -/
theorem joint_second_kernel_norm_sum_from_values (W : 𝓢(ℝ,ℂ)) (decay P J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {κ : Type*} (labels : Finset κ)
      (s : κ → SecondKernelLabel) (t K R : κ → ℝ) (n : κ → Fin 4 → ℤ)
      (z : κ → O) (weight : κ → ℂ) (E : ℝ),
      (∀ θ u v : ℝ, (∑ k ∈ labels, ‖weight k‖ *
        ‖(s k).leftValue (t k+2*Real.pi*(u-θ)) (z k) (dyadicScale (n k 2))‖ *
        ‖(s k).rightValue (t k+2*Real.pi*(v-(-θ))) (z k) (dyadicScale (n k 3))‖) ≤
          (E*(1+‖θ‖)^P)*(1+‖u‖)^J₁*(1+‖v‖)^J₂) →
      (∑ k ∈ labels, ‖(((1+SecondKernelLabel.kernelScale (n k))^decay : ℝ) : ℂ) *
        weight k * (s k).kernelRow (t k) (z k) W (K k) (R k) (n k)‖) ≤ C*E := by
  obtain ⟨C,hC,hkernel⟩ := joint_second_kernel_from_values W decay P J₁ J₂
  refine ⟨C,hC,?_⟩
  intro κ labels s t K R n z weight E he
  apply finite_norm_sum_of_unit_phases
  intro phase hp
  have hh := hkernel labels s t K R n z (fun k => phase k*weight k) E (by
    intro θ u v
    simpa only [norm_mul,hp,one_mul] using he θ u v)
  convert hh using 1 <;> simp only [mul_assoc,mul_left_comm,mul_comm]

#print axioms secondChildValue_absolute
#print axioms joint_second_kernel_norm_sum_from_values
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSecondAbsolute -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.Physical.OriginalFourth ; sha256 1db7f64f244cc850f9b0a027ba7de880cfb467ec83989fef6a91521cc772dfa6 -/
section




noncomputable section
set_option maxHeartbeats 1200000
open scoped Classical BigOperators SchwartzMap
open Filter
namespace Cycle25.Weighted.Numerator.PhysicalMoment
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor CenteredMomentUniformReflectionApproximation
open Cycle25WeightedNumeratorPhysical Cycle25.Weighted.Numerator.PhysicalTail Cycle25.Weighted.Numerator CenteredMomentRetainedWeightedSource
local notation "O" => HeckeFamily.O

theorem certified_original_numerator_fourth {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (G : 𝓢(ℝ,ℂ)) (loss xi q b Cslot : ℝ)
    (hloss : 0< loss) (hxi : 0< xi) (hb : 0< b) (hCslot : 0< Cslot) :
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      1< U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(data : ∀i:rows,PhysicalReflectionData F.S F.exclusions.prime i.val)
        (N : rows→ℝ)(Y m : ℝ),
      0< Y → (∀i,0< N i ∧ N i ≤ b*Y) → 0 ≤ m → m+xi ≤ 2 →
      (∀i,(data i).combinedConductor ≤ (fixedConductorConstant F.S:ℝ)*U^m*(Y/N i)) →
      ∀T:Finset (Fin D.N),∀width:T→ℝ,∀z:T→ℂ,∀height:ℝ,
      (∀i,0 ≤ width i) →
      (∀i,width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i,(z i).re=17/50) → 0 ≤ height → (∀i,|(z i).im| ≤ height) →
      (2*(m+xi)+6*κ*(∑i,width i) ≤ 1 ∨ T=∅) →
      (∀i:rows,‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(width s)) (z s)‖ ≤ Cslot*U^q) →
      (∑i:rows,‖HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0‖^4*
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2) ≤ C*(1+height)^degree*U^(1+D.t+loss) := by
  let Ccond : ℝ := fixedConductorConstant F.S
  have hCcond : 0< Ccond := by dsimp [Ccond];exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  obtain ⟨degree,Cr,hCr,hret⟩ := certified_retained_fixed_profile F κ hκlo hκhi hbeta hκbeta G loss Ccond Ccond xi
    hloss hCcond hCcond hxi
  obtain ⟨Ct,hCt,htail⟩ := subtype_discarded_fourth_negligible (xi/2) 0 q b Ccond Cslot
    (by positivity) hb hCcond hCslot G
  refine ⟨degree,8*(Cr+Ct),by positivity,?_⟩
  filter_upwards [hret] with U hret
  have hU := hret.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows data N Y m hY hN hm hmmax hcombined T width z height hw hwmax hz hheight hzim hcap hQ
  let τ (i:rows) := (data i).presentation
  let ψ (i:rows) := (data i).primitive
  let R (i:rows) := retainedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/4))
  let tail (i:rows) := discardedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/4))
  let Q (i:rows) := ∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
    (U^(width s)) (z s)
  let P (i:rows) := HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false G (Y/N i) 0 0
  have hc (i:rows) : (data i).combinedConductor ≤ Ccond*U :=
    (data i).combined_le_row.trans (mul_le_mul_of_nonneg_left (hrows i.val i.property).2 hCcond.le)
  have hred (i:rows) : (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Ccond*U :=
    (data i).redundant_le_combined.trans (hc i)
  have hr := hret.2 rows hrows τ ψ (fun i=> Y/N i) m (fun i=>(data i).element_eq)
    (fun i=> div_pos hY (hN i).1) hm hmmax hred hcombined T width z height
    hw hwmax hz hheight hzim hcap
  have ht := htail rows τ ψ N Q Y U hY hU.le hN (fun u hu=>(hrows u hu).2) hc hQ
  simp only [show (xi/2)/2=xi/4 by ring,neg_zero,Real.rpow_zero,mul_one] at ht
  have hsplit (i:rows) : P i=(data i).phase*(R i+tail i) :=
    (data i).split G (Y/N i) (U^(xi/4)) (div_pos hY (hN i).1)
  have hh := original_split_weighted_fourth Finset.univ P R tail (fun i=>(data i).phase) Q
    (fun _=>1) (Cr*(1+height)^degree*U^(1+D.t+loss)) Ct
    (fun _ _=> le_rfl) (fun i _=>(data i).phase_norm) (fun i _=> hsplit i)
    (by simpa only [Complex.ofReal_one,div_one] using hr) ht
  simp only [Complex.ofReal_one,div_one] at hh
  have hH : 1 ≤ (1+height)^degree := one_le_pow₀ (by linarith)
  have hpow : 1 ≤ U^(1+D.t+loss) := Real.one_le_rpow hU.le (by linarith [D.t_pos])
  have hcost : 1 ≤ (1+height)^degree*U^(1+D.t+loss) := one_le_mul_of_one_le_of_one_le hH hpow
  have hCt' := mul_le_mul_of_nonneg_left hcost hCt.le
  exact hh.trans (by nlinarith)

end Cycle25.Weighted.Numerator.PhysicalMoment
end

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/
end
/- END ORIGINAL MODULE Cycle25.Energy.Physical.OriginalFourth -/
