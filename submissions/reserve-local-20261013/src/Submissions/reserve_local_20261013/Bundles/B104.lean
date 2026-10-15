/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.reserve_local_20261013.Bundles.B047
import Submissions.reserve_local_20261013.Bundles.B084
import Submissions.reserve_local_20261013.Bundles.B092
import Submissions.reserve_local_20261013.Bundles.B094
import Submissions.reserve_local_20261013.Bundles.B096
import Submissions.reserve_local_20261013.Bundles.B099
import Submissions.reserve_local_20261013.Bundles.B102
import Submissions.reserve_local_20261013.Bundles.B103

/- BEGIN ORIGINAL MODULE Analytic.JointFirstAbsoluteAnnularSector ; sha256 0feec216f9bdd2b1940dabc48e01e52c4f945da47a47c4687c320401fa991c36 -/
section


/-! The actual joint targets control the sum of absolute first blocks.
Positivity makes each target uniform over subsets, allowing an absolute
sum at the fixed cost four instead of the number of common labels. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT RayFourExpansion
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance firstAbsoluteAnnularSectorDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open CenteredMomentFirstAnnularMajorant CenteredMomentSecondRetainedRows CenteredMomentLogDyadic
theorem eventually_actual_first_absolute_annular_sector_from_local_targets
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Wkernel : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (hVrow : V 1 = logAnnulus)
    (Mwin : Fin 4 → ℝ) (hMwin : ∀ i, 0 ≤ Mwin i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ Mwin i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (Ncap : ℕ) (ν F U b₁ b₂ B₁ B₂ B L Cr Amin Amax : ℝ)
    (hν : 0 < ν) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hCr : 0 < Cr) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ (s : Input ι) (R seed : Ideal O),
    Fintype.card ι ≤ Ncap → (∀ i, s.M i ≤ F) → s.upper ≤ U → s.b₁ ≤ b₁ → s.b₂ ≤ b₂ →
    s.W₁ 0 = 0 → s.W₂ 0 = 0 →
    (∀ x, ‖s.W₁ x‖ ≤ B₁) → (∀ x, ‖s.W₂ x‖ ≤ B₂) →
    0 < sourceRadius s → sourceRadius s ≤ Z^B →
    ∀ (M A δ a window Ch : ℝ), Amin ≤ A → A ≤ Amax → 0 < a → 0 ≤ Ch →
    volume s.toData = Z^A →
    ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
    (∀ p E, radius p E ≤ Cr*Z^L) →
    let Outer := FirstSourceOuterIndex s R seed (Z^M) radius
    let q := firstSourceOuterLabel s R seed (Z^M) radius
    ∀ (labels : Finset Outer) (ref : Outer) (t : Outer → ℝ),
    (∀ i ∈ labels, a*Z^A ≤ ((q i).C.absNorm : ℝ)*Real.exp window*dyadicScale (i.2.2 2)) →
    (∀ i ∈ labels, a*Z^A ≤ ((q i).D.absNorm : ℝ)*Real.exp window*dyadicScale (i.2.2 3)) →
    (∀ i ∈ labels, ((q i).C.absNorm : ℝ) ≤ Z^δ*((q ref).C.absNorm : ℝ)) →
    (∀ i ∈ labels, ((q i).D.absNorm : ℝ) ≤ Z^δ*((q ref).D.absNorm : ℝ)) →
    (∀ i ∈ labels, (q ref).activeWidth Z/2+(q ref).punctureWidth Z ≤
      (q i).activeWidth Z/2+(q i).punctureWidth Z) →
    (∀ i ∈ labels, ‖V 0 ((q i).sourceRowLog (Z^M) (dyadicScale (i.2.2 0)))‖ ≤ 1) →
    (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).leftEnergy (t k.1+2*Real.pi*(w-θ)) profile (dyadicScale (k.1.2.2 1))) ≤
        (Z^A/((q ref).C.absNorm : ℝ))*(Ch*Z^((q ref).leftTargetWidth Z A))) →
    (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
      (∑ k ∈ firstSourceLabels labels q,
        ((q k.1).sourceChild k.2).rightEnergy (t k.1+2*Real.pi*(w-(-θ))) profile (dyadicScale (k.1.2.2 1))) ≤
        (Z^A/((q ref).D.absNorm : ℝ))*(Ch*Z^((q ref).rightTargetWidth Z A))) →
    (∑ i ∈ labels, ‖firstPhysicalValue s R seed (Z^M) radius t Wkernel V i‖)/Z^A ≤
      C*(Ch+firstSourceCoarseConstant Ncap F U b₁ b₂ B₁ B₂ (QuadraticInitialBound.diagonalControl profile))*(Real.exp window/a)*Z^(M+δ) := by
  obtain ⟨degree,C,hC,hsector⟩ := eventually_actual_first_annular_sector_from_local_targets
    (ι := ι) Wkernel V hVrow Mwin hMwin hV hV₂c hV₂s hV₃c hV₃s 0 Ncap ν
    F U b₁ b₂ B₁ B₂ B L Cr Amin Amax hν hB₁ hB₂ hB hL hCr
  refine ⟨degree,4*C,by positivity,?_⟩
  filter_upwards [hsector,eventually_gt_atTop (0:ℝ)] with Z hsector hZ
  intro s R seed hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hsourcepos hsource
    M A δ a window Ch hAmin hAmax ha hCh hvolume radius hr
  dsimp only
  intro labels ref t hl hr' hNC hND hscalarWidth hV₀ hleft hright
  let q := firstSourceOuterLabel s R seed (Z^M) radius
  let bound := C*(Ch+firstSourceCoarseConstant Ncap F U b₁ b₂ B₁ B₂
    (QuadraticInitialBound.diagonalControl profile))*(Real.exp window/a)*Z^(M+δ)
  have hZA : 0 < Z^A := Real.rpow_pos_of_pos hZ A
  have hsub (T : Finset (FirstSourceOuterIndex s R seed (Z^M) radius)) (hT : T ⊆ labels) :
      ‖∑ i ∈ T,firstPhysicalValue s R seed (Z^M) radius t Wkernel V i‖ ≤ bound*Z^A := by
    have hlabels := firstSourceLabels_subset T labels q hT
    have hl' (θ w : ℝ) (hθ : ‖θ‖ ≤ Z^ν) (hw : ‖w‖ ≤ Z^ν) :
        (∑ k ∈ firstSourceLabels T q,
          ((q k.1).sourceChild k.2).leftEnergy (t k.1+2*Real.pi*(w-θ)) profile
            (dyadicScale (k.1.2.2 1))) ≤
          (Z^A/((q ref).C.absNorm : ℝ))*(Ch*Z^((q ref).leftTargetWidth Z A)) := by
      apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hlabels ?_) (hleft θ w hθ hw)
      intro k hk hk'
      exact ((q k.1).sourceChild k.2).leftEnergy_nonneg _ _ _ (dyadicScale_pos _)
        (fun z => profile_nonneg _)
    have hr'' (θ w : ℝ) (hθ : ‖θ‖ ≤ Z^ν) (hw : ‖w‖ ≤ Z^ν) :
        (∑ k ∈ firstSourceLabels T q,
          ((q k.1).sourceChild k.2).rightEnergy (t k.1+2*Real.pi*(w-(-θ))) profile
            (dyadicScale (k.1.2.2 1))) ≤
          (Z^A/((q ref).D.absNorm : ℝ))*(Ch*Z^((q ref).rightTargetWidth Z A)) := by
      apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hlabels ?_) (hright θ w hθ hw)
      intro k hk hk'
      exact ((q k.1).sourceChild k.2).rightEnergy_nonneg _ _ _ (dyadicScale_pos _)
        (fun z => profile_nonneg _)
    have hh := hsector s R seed hN hF hU hb₁ hb₂ hz₁ hz₂ hbound₁ hbound₂ hsourcepos hsource
      M A δ a window Ch hAmin hAmax ha hCh hvolume radius hr T ref t
      (fun i hi => hl i (hT hi)) (fun i hi => hr' i (hT hi))
      (fun i hi => hNC i (hT hi)) (fun i hi => hND i (hT hi))
      (fun i hi => hscalarWidth i (hT hi)) (fun i hi => hV₀ i (hT hi)) hl' hr''
    apply (div_le_iff₀ hZA).mp
    simpa only [pow_zero,Complex.ofReal_one,one_mul,firstPhysicalValue] using hh
  have hh := complex_sum_norm_le_four_of_subsets labels
    (firstPhysicalValue s R seed (Z^M) radius t Wkernel V) (bound*Z^A) hsub
  apply (div_le_iff₀ hZA).mpr
  calc
    _ ≤ 4*(bound*Z^A) := hh
    _ = _ := by dsimp only [bound]; ring

#print axioms eventually_actual_first_absolute_annular_sector_from_local_targets
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstAbsoluteAnnularSector -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstErrorReference ; sha256 bb3e45173a64c750afa5390013a9965af746cd8ead91eaf9bcafef4078436666 -/
section


/-! Exact source reference powers for the independent first errors.
The common-source amplifier is normalized by the original volume, so
returning to a raw first energy multiplies the extracted error by that
volume once. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CenteredMomentFirstScale CenteredMomentFirstMixedAllowance
open CenteredMomentFirstMixedRightTransport CenteredMomentFirstCommonTransport
open CenteredMomentCommonRadialData CenteredMomentPrimeElements
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization CenteredMomentFirstMixedRoot
open CenteredMomentFirstCanonicalFamily CenteredMomentAmplificationChildInput
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

namespace FirstJointLabel

def parentCost (s : FirstJointLabel ι) : ℝ :=
  (s.parent.modulus.absNorm : ℝ)*(Ideal.span {fixedBadMask}).absNorm*
    (Ideal.span {(72 : O)}).absNorm

theorem parentCost_pos (s : FirstJointLabel ι) : 0 < s.parentCost := by
  have hη := norm_pos s.parent.modulus s.parent.modulus_ne_bot
  have hbad := norm_pos (Ideal.span {fixedBadMask})
    (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero)
  have h72 := norm_pos (Ideal.span {(72 : O)})
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  dsimp [parentCost]
  positivity

theorem pair_modulus_powers (s : FirstJointLabel ι) (Z : ℝ) (hZ : 1 < Z) :
    (s.pair.left.modulus.absNorm : ℝ) = s.parentCost*Z^(s.activeWidth Z+s.punctureWidth Z) ∧
    (s.pair.right.modulus.absNorm : ℝ) = s.parentCost*Z^(s.activeWidth Z+s.punctureWidth Z) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have ha := normValue_ge_one (activeConductor s.C s.D)
    (supported_element_ne_zero _ (activeConductor_supported s.C s.D s.hC))
  have hp := normValue_ge_one s.puncture
    (supported_element_ne_zero _ (subsetGenerator_supported s.C s.D s.hC s.E))
  have he : (s.parent.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {s.puncture*activeConductor s.C s.D}).absNorm =
      s.parent.modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72 : O)}).absNorm*
        ((Ideal.span {s.puncture}).absNorm*(Ideal.span {activeConductor s.C s.D}).absNorm) := by
    rw [←Ideal.span_singleton_mul_span_singleton]
    simp only [map_mul]
  dsimp only [normValue] at ha hp
  have hpow : Z^(s.activeWidth Z+s.punctureWidth Z) =
      ((Ideal.span {activeConductor s.C s.D}).absNorm : ℝ)*(Ideal.span {s.puncture}).absNorm := by
    rw [Real.rpow_add hz]
    unfold activeWidth punctureWidth
    rw [eisEmbedding_norm_sq_eq_absNorm_span,
      Real.rpow_logb hz hZ.ne' (zero_lt_one.trans_le ha),
      Real.rpow_logb hz hZ.ne' (zero_lt_one.trans_le hp)]
  have hreal : ((s.parent.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {s.puncture*activeConductor s.C s.D}).absNorm : ℝ) =
      s.parentCost*Z^(s.activeWidth Z+s.punctureWidth Z) := by
    rw [he]
    push_cast
    rw [hpow]
    dsimp [parentCost]
    ring
  rw [s.pair.left_modulus,s.pair.right_modulus]
  exact ⟨hreal,hreal⟩

theorem allowances_eq (s : FirstJointLabel ι) (Z : ℝ) :
    allowance s.C s.D Z = s.leftAllowance Z ∧ allowance s.D s.C Z = s.rightAllowance Z := by
  constructor
  · rfl
  · unfold allowance rightAllowance leftWidth rightWidth activeWidth
    rw [active_span_swap]

def leftErrorReference (s : FirstJointLabel ι) (Z A : ℝ) : ℝ :=
  (s.pair.left.modulus.absNorm : ℝ)*(Z^A/(s.C.absNorm : ℝ)^2)*Z^(allowance s.C s.D Z)

def rightErrorReference (s : FirstJointLabel ι) (Z A : ℝ) : ℝ :=
  (s.pair.right.modulus.absNorm : ℝ)*(Z^A/(s.D.absNorm : ℝ)^2)*Z^(allowance s.D s.C Z)

theorem error_reference_pos (s : FirstJointLabel ι) (Z A : ℝ) (hZ : 0 < Z) :
    0 < s.leftErrorReference Z A ∧ 0 < s.rightErrorReference Z A := by
  have hc := norm_pos s.C s.hC.1
  have hd := norm_pos s.D s.hD.1
  have hτl := norm_pos s.pair.left.modulus s.pair.left.modulus_ne_bot
  have hτr := norm_pos s.pair.right.modulus s.pair.right.modulus_ne_bot
  dsimp [leftErrorReference,rightErrorReference]
  constructor <;> positivity

/-- Exact central normalization: the original volume cancels to the
same `V/NC` and `V/ND` convention used by the first sector theorem. -/
theorem raw_error_reference_target (s : FirstJointLabel ι) (Z A : ℝ) (hZ : 1 < Z) :
    Z^A*s.leftErrorReference Z A*Z^(s.radicalWidth Z) =
      (Z^A/(s.C.absNorm : ℝ))*s.parentCost*Z^(s.leftTargetWidth Z A) ∧
    Z^A*s.rightErrorReference Z A*Z^(s.radicalWidth Z) =
      (Z^A/(s.D.absNorm : ℝ))*s.parentCost*Z^(s.rightTargetWidth Z A) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc := norm_pos s.C s.hC.1
  have hd := norm_pos s.D s.hD.1
  have hcPow : Z^(s.leftWidth Z) = (s.C.absNorm : ℝ) := Real.rpow_logb hz hZ.ne' hc
  have hdPow : Z^(s.rightWidth Z) = (s.D.absNorm : ℝ) := Real.rpow_logb hz hZ.ne' hd
  obtain ⟨hleft,hright⟩ := s.pair_modulus_powers Z hZ
  obtain ⟨hal,har⟩ := s.allowances_eq Z
  dsimp only [leftErrorReference,rightErrorReference,leftTargetWidth,rightTargetWidth]
  rw [hleft,hright,hal,har]
  simp only [Real.rpow_add hz,Real.rpow_sub hz,hcPow,hdPow]
  constructor <;> field_simp <;> ring

/-- A single geometric sector controls the independent error reference.
The conditions concern only the source norms and explicit exponent widths. -/
theorem error_reference_sector_cap (s q : FirstJointLabel ι) (Z A δ : ℝ) (hZ : 1 < Z)
    (hparent : s.parent = q.parent)
    (hC : (q.C.absNorm : ℝ) ≤ s.C.absNorm) (hD : (q.D.absNorm : ℝ) ≤ s.D.absNorm)
    (hleft : s.activeWidth Z+s.punctureWidth Z+s.leftAllowance Z ≤
      q.activeWidth Z+q.punctureWidth Z+q.leftAllowance Z+δ)
    (hright : s.activeWidth Z+s.punctureWidth Z+s.rightAllowance Z ≤
      q.activeWidth Z+q.punctureWidth Z+q.rightAllowance Z+δ) :
    s.leftErrorReference Z A ≤ q.leftErrorReference Z A*Z^δ ∧
    s.rightErrorReference Z A ≤ q.rightErrorReference Z A*Z^δ := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hqc := norm_pos q.C q.hC.1
  have hqd := norm_pos q.D q.hD.1
  have hc := norm_pos s.C s.hC.1
  have hd := norm_pos s.D s.hD.1
  have hp : s.parentCost = q.parentCost := by simp only [parentCost,hparent]
  obtain ⟨hsl,hsr⟩ := s.pair_modulus_powers Z hZ
  obtain ⟨hql,hqr⟩ := q.pair_modulus_powers Z hZ
  have hel : s.leftErrorReference Z A =
      s.parentCost*(Z^A/(s.C.absNorm : ℝ)^2)*Z^(s.activeWidth Z+s.punctureWidth Z+s.leftAllowance Z) := by
    unfold leftErrorReference
    rw [hsl,(s.allowances_eq Z).1]
    simp only [Real.rpow_add hz]
    ring
  have her : s.rightErrorReference Z A =
      s.parentCost*(Z^A/(s.D.absNorm : ℝ)^2)*Z^(s.activeWidth Z+s.punctureWidth Z+s.rightAllowance Z) := by
    unfold rightErrorReference
    rw [hsr,(s.allowances_eq Z).2]
    simp only [Real.rpow_add hz]
    ring
  have hql' : q.leftErrorReference Z A*Z^δ =
      q.parentCost*(Z^A/(q.C.absNorm : ℝ)^2)*Z^(q.activeWidth Z+q.punctureWidth Z+q.leftAllowance Z+δ) := by
    unfold leftErrorReference
    rw [hql,(q.allowances_eq Z).1]
    simp only [Real.rpow_add hz]
    ring
  have hqr' : q.rightErrorReference Z A*Z^δ =
      q.parentCost*(Z^A/(q.D.absNorm : ℝ)^2)*Z^(q.activeWidth Z+q.punctureWidth Z+q.rightAllowance Z+δ) := by
    unfold rightErrorReference
    rw [hqr,(q.allowances_eq Z).2]
    simp only [Real.rpow_add hz]
    ring
  rw [hel,her,hql',hqr',hp]
  constructor
  · exact mul_le_mul (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) (sq_pos_of_pos hqc)
        (sq_le_sq₀ hqc.le hc.le |>.mpr hC)) q.parentCost_pos.le)
      (Real.rpow_le_rpow_of_exponent_le hZ.le hleft) (Real.rpow_nonneg hz.le _) (by positivity [q.parentCost_pos])
  · exact mul_le_mul (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) (sq_pos_of_pos hqd)
        (sq_le_sq₀ hqd.le hd.le |>.mpr hD)) q.parentCost_pos.le)
      (Real.rpow_le_rpow_of_exponent_le hZ.le hright) (Real.rpow_nonneg hz.le _) (by positivity [q.parentCost_pos])

/-- The complete reference exponent, with no ordering assumption on
individual common ideals inside the sector. -/
theorem error_reference_powers (s : FirstJointLabel ι) (Z A : ℝ) (hZ : 1 < Z) :
    s.leftErrorReference Z A = s.parentCost*
      Z^(A-2*s.leftWidth Z+s.activeWidth Z+s.punctureWidth Z+s.leftAllowance Z) ∧
    s.rightErrorReference Z A = s.parentCost*
      Z^(A-2*s.rightWidth Z+s.activeWidth Z+s.punctureWidth Z+s.rightAllowance Z) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hc := norm_pos s.C s.hC.1
  have hd := norm_pos s.D s.hD.1
  have hcPow : Z^(s.leftWidth Z) = (s.C.absNorm : ℝ) := Real.rpow_logb hz hZ.ne' hc
  have hdPow : Z^(s.rightWidth Z) = (s.D.absNorm : ℝ) := Real.rpow_logb hz hZ.ne' hd
  obtain ⟨hleft,hright⟩ := s.pair_modulus_powers Z hZ
  dsimp only [leftErrorReference,rightErrorReference]
  rw [hleft,hright,(s.allowances_eq Z).1,(s.allowances_eq Z).2]
  rw [show 2*s.leftWidth Z = s.leftWidth Z+s.leftWidth Z by ring,
    show 2*s.rightWidth Z = s.rightWidth Z+s.rightWidth Z by ring]
  simp only [Real.rpow_add hz,Real.rpow_sub hz,hcPow,hdPow]
  constructor <;> ring

theorem error_reference_combined_sector_cap (s q : FirstJointLabel ι) (Z A δ : ℝ) (hZ : 1 < Z)
    (hparent : s.parent = q.parent)
    (hleft : s.activeWidth Z+s.punctureWidth Z+s.leftAllowance Z-2*s.leftWidth Z ≤
      q.activeWidth Z+q.punctureWidth Z+q.leftAllowance Z-2*q.leftWidth Z+δ)
    (hright : s.activeWidth Z+s.punctureWidth Z+s.rightAllowance Z-2*s.rightWidth Z ≤
      q.activeWidth Z+q.punctureWidth Z+q.rightAllowance Z-2*q.rightWidth Z+δ) :
    s.leftErrorReference Z A ≤ q.leftErrorReference Z A*Z^δ ∧
    s.rightErrorReference Z A ≤ q.rightErrorReference Z A*Z^δ := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hp : s.parentCost = q.parentCost := by simp only [parentCost,hparent]
  rw [(s.error_reference_powers Z A hZ).1,(s.error_reference_powers Z A hZ).2,
    (q.error_reference_powers Z A hZ).1,(q.error_reference_powers Z A hZ).2,hp]
  simp only [mul_assoc,←Real.rpow_add hz]
  constructor <;> apply mul_le_mul_of_nonneg_left _ q.parentCost_pos.le
  · exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

end FirstJointLabel

namespace ExtractedErrorRun
variable {s : Input ι} {C : Ideal O} {P : Finset (Ideal O)}
lemma normalizedValue_nonneg (x : ExtractedErrorRun s C P) (N : ℕ) (D R seed : Ideal O)
    (E : Finset (CommonIndex C D)) (τ : Character) (upper Z K sigma delta reserve : ℝ)
    (hZ : 0 < Z) : 0 ≤ x.normalizedValue N D R seed E τ upper Z K sigma delta reserve := by
  have hv := volume_pos s
  apply div_nonneg (x.value_nonneg N D R seed E τ upper Z K sigma delta reserve hZ)
  positivity
lemma value_eq_normalized_reference (x : ExtractedErrorRun s C P) (N : ℕ) (D R seed : Ideal O)
    (E : Finset (CommonIndex C D)) (τ : Character) (upper Z K sigma delta reserve : ℝ)
    (hZ : 0 < Z) (hC : C ≠ 0) :
    x.value N D R seed E τ upper Z K sigma delta reserve =
      ((τ.modulus.absNorm : ℝ)*(volume s/(C.absNorm : ℝ)^2)*Z^(allowance C D Z))*
        x.normalizedValue N D R seed E τ upper Z K sigma delta reserve := by
  have hv := volume_pos s
  have hc := norm_pos C hC
  have ht := norm_pos τ.modulus τ.modulus_ne_bot
  have hden : (τ.modulus.absNorm : ℝ)*(volume s/(C.absNorm : ℝ)^2)*Z^(allowance C D Z) ≠ 0 := by
    positivity
  unfold normalizedValue value
  exact (mul_div_cancel₀ _ hden).symm

end ExtractedErrorRun

#print axioms FirstJointLabel.pair_modulus_powers
#print axioms FirstJointLabel.raw_error_reference_target
#print axioms FirstJointLabel.error_reference_sector_cap
#print axioms FirstJointLabel.error_reference_combined_sector_cap
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstErrorReference -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstIndependentErrorsFull ; sha256 2034b801e377375767e042a583dcd4ccd46786dbde451bba11ec77c1db3bd25b -/
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
local instance actualFirstIndependentErrorsDecEqFull {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
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
local instance actualFirstIndependentErrorsFiniteFull : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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

theorem actual_first_independent_extracted_errors_full
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
    (hCrfirst : 0 < Crfirst) (hallocSmall : εalloc*Bfirst ≤ 1/10000)
    (qParent εconductor : ℝ) (hεconductor : 0 < εconductor)
    (hcostSource : CenteredMomentFirstSourceConductorCaps.rayCost ≤ cost)
    (hconductorBudget : qParent+2*Bfirst+sigma/3+εconductor ≤ qmoving)
    (εouter : ℝ) (hεouter : 0 < εouter) (hseedBudget : Bfirst ≤ Bseed):
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
    (src.η.modulus.absNorm : ℝ) ≤ Z^qParent →
    ∀ (R seedOuter : Ideal O), R ≠ 0 →
    Squarefree seedOuter → seedOuter ≠ 0 →
    src.W₁ 0=0 → src.W₂ 0=0 → volume src≤ Z^Avol → (R.absNorm : ℝ)≤ Z^Pmask →
    0 < sourceRadius src → sourceRadius src ≤ Z^Bfirst →
    ∀ profile : Profiles a b, profile.profile 0=src.W₁ → profile.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀ (K delta reserve asource : ℝ),
    0 < K → 0 < asource →
    0 ≤ delta → 0 ≤ reserve → a0 ≤ asource →
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
    Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm : ℝ))≤1/250 →
    (Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh ≤ 1/10000 →
    delta+reserve ≤ 1/1000 → εsrc*Mvolume ≤ 1/1000 →
    ∀ radius : (p : Labels src R seedOuter) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
    (∀ p E, radius p E ≤ Crfirst*Z^Lfirst) →
    let q := firstSourceOuterLabel src R seedOuter K radius
    ∀ (labels : Finset (FirstSourceOuterIndex src R seedOuter K radius)) (p : ℝ),
    (∀ i ∈ labels, ((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^p) →
    ∀ left : (k : (i : FirstSourceOuterIndex src R seedOuter K radius) × (q i).SourceIndex) →
      ExtractedErrorRun src (q k.1).C P,
    ∀ right : (k : (i : FirstSourceOuterIndex src R seedOuter K radius) × (q i).SourceIndex) →
      ExtractedErrorRun src (q k.1).D P,
    (∀ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
      (left k).SourceAdmissible (q k.1).D R (q k.1).E ((q k.1).sourceChild k.2).pair.left
        Z K sigma delta reserve Dscale heightCap) →
    (∀ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
      (right k).SourceAdmissible (q k.1).C R (swapSubset (q k.1).C (q k.1).D (q k.1).E)
        ((q k.1).sourceChild k.2).pair.right Z K sigma delta reserve Dscale heightCap) →
    (∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
      (left k).normalizedValue N (q k.1).D R k.2.1.val (q k.1).E
        ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve) ≤
      Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2*
        Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ) ∧
    (∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
      (right k).normalizedValue N (q k.1).C R k.2.1.val
        (swapSubset (q k.1).C (q k.1).D (q k.1).E)
        ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve) ≤
      Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2*
        Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ) := by
  obtain ⟨Calloc,hCalloc,Uprofile,Jheight,hactual⟩ := actual_allocated_extracted_errors_uniform_full (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ Sbad hbad sigma cost hsigma hξsmall hcost hsigma_eq
    Avol Dscale Pmask qmoving εgeo hεgeo hbudget εalloc hεalloc hloss hsaving
  obtain ⟨Cmass,hCmass,hmass⟩ := actual_first_source_sector_harmonic_mass
    Bfirst Lfirst Crfirst εouter hBfirst hLfirst hCrfirst hεouter
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Calloc*Cbound*Cmass,mul_pos (mul_pos hCalloc hCbound) hCmass,?_⟩
  filter_upwards [hactualZ,hmass,eventually_fixed_pair_error_source_caps M H Sbad hbad εconductor hεconductor]
    with Z hZ hmass hcaps
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max hParent
    R seedOuter hR hseedOuter hseedOuter0
    hzero1 hzero2 hvolumeCap hmaskCap hHsource hHcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hP Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
    Mgeom Mvolume heightCap hgeom hheightCap hplainX₁ hplainX₂ hplainY₁ hplainY₂
    hwidth hvolGeom hvolCap hfixed hdef hpaid hfrequency hepsSmall radius hr
  let q := firstSourceOuterLabel src R seedOuter K radius
  intro labels p hrad left right hleft hright
  let F := Calloc*Cbound*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  have hm := hmass.2 α src R seedOuter hseedOuter hseedOuter0 hzero1 hzero2
    hHsource hHcap K hK radius hr labels p hrad
  have hsingle (C D seed : Ideal O) (hC : Supported C) (hD : Supported D)
      (hCD : primeSupport C=primeSupport D) (E : Finset (CommonIndex C D)) (τ : Character)
      (hmod : τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
        Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E*activeConductor C D})
      (hseed : Squarefree seed) (hseed0 : seed ≠ 0) (hseedcap : (seed.absNorm : ℝ) ≤ Z^Bseed)
      (x : ExtractedErrorRun src C (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
      (hx : x.Admissible D R E τ Z K sigma delta reserve cost Dscale qmoving Bfirst heightCap) :
      x.normalizedValue N D R seed E τ upper Z K sigma delta reserve ≤
        F*Z^(-1/2500 : ℝ)/(seed.absNorm : ℝ) := by
    exact hZ.2 θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
      C D R hC hD hCD E τ x.height hmod K delta reserve asource hK hasource hdelta hreserve haSource
      hP hx.slot_coprime x.family hx.radical_cap hx.moving_cap
      hzero1 hzero2 hvolumeCap hmaskCap hR hx.radius_inv hx.conductor_cap
      seed hseed hseed0 hseedcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower Mgeom Mvolume hgeom hplainX₁ hplainX₂
      hplainY₁ hplainY₂ hwidth hvolGeom hvolCap hfixed hdef
      Bfirst heightCap hheightCap hx.height_le hx.common_cap hallocSmall hpaid hfrequency hepsSmall
  have hnorm (i : FirstSourceOuterIndex src R seedOuter K radius) :=
    actual_first_label_norm_caps src R seedOuter hseedOuter hzero1 hzero2 Z Bfirst hHcap i.1
  have hleftBound (k : (i : FirstSourceOuterIndex src R seedOuter K radius) × (q i).SourceIndex)
      (hk : k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src)) :
      (left k).normalizedValue N (q k.1).D R k.2.1.val (q k.1).E
        ((q k.1).sourceChild k.2).pair.left upper Z K sigma delta reserve ≤
        F*Z^(-1/2500 : ℝ)/(k.2.1.val.absNorm : ℝ) := by
    obtain ⟨_,hs,hs0,hscap⟩ := firstLeftSourceLabels_gates labels q (fun _ => sourceRadius src)
      Z Bfirst hz.le (fun _ _ => hHcap) k hk
    have hx := hleft k hk
    let v := (q k.1).sourceChild k.2
    have hcs := hcaps.2 src.η v.C v.D v.hC v.E v.leftRay v.rightRay v.pair
      qParent Bfirst sigma cost qmoving hParent (hnorm k.1).1 hcostSource hconductorBudget
    apply hsingle v.C v.D k.2.1.val v.hC v.hD v.hCD v.E v.pair.left v.pair.left_modulus hs hs0
      (hscap.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hseedBudget)) (left k)
    refine ⟨hx.height_le,(hnorm k.1).1,hx.slot_coprime,hx.radical_cap,?_,hx.radius_inv,?_⟩
    · intro B hB prime i χ
      exact (hcs v.pair.left ((left k).family B prime i χ) (Or.inl rfl) χ prime i
        (hx.radical_cap B hB prime i χ)).1
    · intro B hB prime i χ
      exact (hcs v.pair.left ((left k).family B prime i χ) (Or.inl rfl) χ prime i
        (hx.radical_cap B hB prime i χ)).2
  have hrightBound (k : (i : FirstSourceOuterIndex src R seedOuter K radius) × (q i).SourceIndex)
      (hk : k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src)) :
      (right k).normalizedValue N (q k.1).C R k.2.1.val
        (swapSubset (q k.1).C (q k.1).D (q k.1).E)
        ((q k.1).sourceChild k.2).pair.right upper Z K sigma delta reserve ≤
        F*Z^(-1/2500 : ℝ)/(k.2.1.val.absNorm : ℝ) := by
    obtain ⟨_,hs,hs0,hscap⟩ := firstRightSourceLabels_gates labels q (fun _ => sourceRadius src)
      Z Bfirst hz.le (fun _ _ => hHcap) k hk
    have hx := hright k hk
    let v := (q k.1).sourceChild k.2
    have hcs := hcaps.2 src.η v.C v.D v.hC v.E v.leftRay v.rightRay v.pair
      qParent Bfirst sigma cost qmoving hParent (hnorm k.1).1 hcostSource hconductorBudget
    apply hsingle v.D v.C k.2.1.val v.hD v.hC v.hCD.symm (swapSubset v.C v.D v.E) v.pair.right
      (right_modulus src.η v.C v.D v.hC v.E v.leftRay v.rightRay v.pair) hs hs0
      (hscap.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hseedBudget)) (right k)
    refine ⟨hx.height_le,(hnorm k.1).2,hx.slot_coprime,hx.radical_cap,?_,hx.radius_inv,?_⟩
    · intro B hB prime i χ
      exact (hcs v.pair.right ((right k).family B prime i χ) (Or.inr rfl) χ prime i
        (hx.radical_cap B hB prime i χ)).1
    · intro B hB prime i χ
      exact (hcs v.pair.right ((right k).family B prime i χ) (Or.inr rfl) χ prime i
        (hx.radical_cap B hB prime i χ)).2
  have hscalar : (F*Z^(-1/2500 : ℝ))*(Cmass*Z^(p+εouter)/(seedOuter.absNorm : ℝ)) =
      (Calloc*Cbound*Cmass)*profile.control Uprofile^2*(1+heightCap+height)^Jheight*mass src^2*
        Z^(p-1/2500+εouter)/(seedOuter.absNorm : ℝ) := by
    rw [show p-1/2500+εouter = (-1/2500)+(p+εouter) by ring]
    simp only [Real.rpow_add hz]
    dsimp [F]
    ring
  constructor
  · calc
      _ ≤ ∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
          F*Z^(-1/2500 : ℝ)/(k.2.1.val.absNorm : ℝ) := Finset.sum_le_sum hleftBound
      _ = (F*Z^(-1/2500 : ℝ))*(∑ k ∈ firstLeftSourceLabels labels q (fun _ => sourceRadius src),
          1/(k.2.1.val.absNorm : ℝ)) := by simp only [Finset.mul_sum,mul_one_div]
      _ ≤ (F*Z^(-1/2500 : ℝ))*(Cmass*Z^(p+εouter)/(seedOuter.absNorm : ℝ)) :=
        mul_le_mul_of_nonneg_left hm.1 (mul_nonneg hF (Real.rpow_nonneg hz.le _))
      _ = _ := hscalar
  · calc
      _ ≤ ∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
          F*Z^(-1/2500 : ℝ)/(k.2.1.val.absNorm : ℝ) := Finset.sum_le_sum hrightBound
      _ = (F*Z^(-1/2500 : ℝ))*(∑ k ∈ firstRightSourceLabels labels q (fun _ => sourceRadius src),
          1/(k.2.1.val.absNorm : ℝ)) := by simp only [Finset.mul_sum,mul_one_div]
      _ ≤ (F*Z^(-1/2500 : ℝ))*(Cmass*Z^(p+εouter)/(seedOuter.absNorm : ℝ)) :=
        mul_le_mul_of_nonneg_left hm.2 (mul_nonneg hF (Real.rpow_nonneg hz.le _))
      _ = _ := hscalar

#print axioms actual_first_independent_extracted_errors_full
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstIndependentErrorsFull -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstSecondReindex ; sha256 b827cd42b7482baaffd33806da067f879ff90d532698990062fe03a793dbae5e -/
section






/-! Literal first-source and second-block indices, reindexed without any
arithmetic multiplicity loss. Both ray labels and both dyadic indices are
retained alongside the single joint arithmetic row. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
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
variable (src : Input ι) (R seed : Ideal O) (Kfirst : ℝ)
  (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)

abbrev First := (i : FirstSourceOuterIndex src R seed Kfirst radius) ×
  (firstSourceOuterLabel src R seed Kfirst radius i).SourceIndex

def columns (side : Bool) (k : First src R seed Kfirst radius) :=
  commonSecondColumns (original src R seed) (sourceFirstCommon side k.1.1.val)
    (sourceFirstCommon_supported (original src R seed) side k.1.1)

def beta (side : Bool) (k : First src R seed Kfirst radius) :=
  commonSecondBeta (original src R seed) (sourceFirstCommon side k.1.1.val) k.2.1.val

abbrev Blocks (side : Bool) (K Radius H : First src R seed Kfirst radius → ℝ)
    (k : First src R seed Kfirst radius) :=
  ActiveBlocks (columns src R seed Kfirst radius side k)
    (beta src R seed Kfirst radius side k) (K k) (Radius k) (H k)

abbrev Packet (side : Bool) (K Radius H : First src R seed Kfirst radius → ℝ) :=
  (k : First src R seed Kfirst radius) × (b : Blocks src R seed Kfirst radius side K Radius H k) × O

variable {src R seed Kfirst radius}
  {side : Bool} {K Radius H : First src R seed Kfirst radius → ℝ}

def row (x : Packet src R seed Kfirst radius side K Radius H) :
    ActualJointSourceRow (original src R seed) side :=
  ⟨x.1.1.1,x.1.1.2.1.val,x.1.2.1.val,x.2.1.1.1,x.2.1.1.2,x.2.2⟩

def key (x : Packet src R seed Kfirst radius side K Radius H) :
    ActualJointSourceRow (original src R seed) side × RayCharacter × RayCharacter ×
      (Fin 4 → ℤ) × (Fin 4 → ℤ) :=
  (row x,x.1.2.2.1,x.1.2.2.2,(fun j => (x.1.1.2.2 j : ℤ)),(fun j => (x.2.1.2 j : ℤ)))

theorem key_injective : Function.Injective
    (key (src := src) (R := R) (seed := seed) (Kfirst := Kfirst) (radius := radius)
      (side := side) (K := K) (Radius := Radius) (H := H)) := by
  rintro ⟨⟨⟨p,E,n⟩,L,χ,ξ⟩,⟨⟨r,U⟩,m⟩,z⟩ ⟨⟨⟨p',E',n'⟩,L',χ',ξ'⟩,⟨⟨r',U'⟩,m'⟩,z'⟩ he
  have hp : p=p' := congrArg (fun k => k.1.first) he
  subst p'
  have hE : E=E' := Subtype.ext
    (Finset.image_injective Subtype.val_injective (congrArg (fun k => k.1.E.image Subtype.val) he))
  subst E'
  have hn : n=n' := funext (fun j => Subtype.ext (congrFun (congrArg (fun k => k.2.2.2.1) he) j))
  subst n'
  have hL : L=L' := Subtype.ext (congrArg (fun k => k.1.L) he)
  subst L'
  have hχ : χ=χ' := congrArg (fun k => k.2.1) he
  subst χ'
  have hξ : ξ=ξ' := congrArg (fun k => k.2.2.1) he
  subst ξ'
  have hr : r=r' := Subtype.ext (congrArg (fun k => k.1.second.val) he)
  subst r'
  have hU : U=U' := Finset.image_injective Subtype.val_injective
    (congrArg (fun k => k.1.U.image Subtype.val) he)
  subst U'
  have hm : m=m' := funext (fun j => Subtype.ext (congrFun (congrArg (fun k => k.2.2.2.2) he) j))
  subst m'
  have hz : z=z' := congrArg (fun k => k.1.z) he
  subst z'
  rfl

end ActualFirstSecondSource
#print axioms ActualFirstSecondSource.key_injective
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstSecondReindex -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstSideEnergy ; sha256 b69a186eaf26e03717230fc34578c5e6805affaec117bd20ae6f5460012e5d34 -/
section



/-! Selecting either first energy retains its original fixed pair. The
supported projector sum and original-volume normalization are exact. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstPhysicalSource
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι Λ : Type*} [Fintype ι] [DecidableEq Λ]

namespace FirstJointLabel

def sideParent (q : FirstJointLabel ι) (left : Bool) : Character :=
  if left then q.pair.left else q.pair.right

def sideEnergy (q : FirstJointLabel ι) (left : Bool)
    (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  if left then q.leftEnergy t W K else q.rightEnergy t W K

def sideWidth (q : FirstJointLabel ι) (left : Bool) (Z : ℝ) : ℝ :=
  Real.logb Z ((q.sideCommon left).absNorm : ℝ)

def sideAllowance (q : FirstJointLabel ι) (left : Bool) (Z : ℝ) : ℝ :=
  if left then q.leftAllowance Z else q.rightAllowance Z

def sideTargetWidth (q : FirstJointLabel ι) (left : Bool) (Z A : ℝ) : ℝ :=
  if left then q.leftTargetWidth Z A else q.rightTargetWidth Z A

theorem sideEnergy_eq_commonEnergy (q : FirstJointLabel ι) (left : Bool)
    (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    q.sideEnergy left t W K =
      (commonEnergy q.data (q.sideCommon left) (q.sideCommon_supported left)
        (q.sideParent left) t q.projector W K).re := by
  cases left <;> rfl

theorem sideTargetWidth_formula (q : FirstJointLabel ι) (left : Bool) (Z A : ℝ) :
    q.sideTargetWidth left Z A = q.radicalWidth Z+A-q.sideWidth left Z+
      q.activeWidth Z+q.punctureWidth Z+q.sideAllowance left Z := by
  cases left <;> rfl

theorem side_target_power (q : FirstJointLabel ι) (left : Bool) (Z A C loss : ℝ)
    (hZ : 1 < Z) :
    C*Z^(q.radicalWidth Z+A-2*q.sideWidth left Z+q.activeWidth Z+
      q.punctureWidth Z+q.sideAllowance left Z+loss) =
      (1/(q.sideCommon left).absNorm : ℝ)*
        (C*Z^(q.sideTargetWidth left Z A+loss)) := by
  have hn : 0 < ((q.sideCommon left).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (q.sideCommon_supported left).1)
  have hz := zero_lt_one.trans hZ
  have he := Real.rpow_logb hz hZ.ne' hn
  change Z^(q.sideWidth left Z) = _ at he
  rw [q.sideTargetWidth_formula]
  rw [show q.radicalWidth Z+A-2*q.sideWidth left Z+q.activeWidth Z+
      q.punctureWidth Z+q.sideAllowance left Z+loss =
      (q.radicalWidth Z+A-q.sideWidth left Z+q.activeWidth Z+
        q.punctureWidth Z+q.sideAllowance left Z+loss)-q.sideWidth left Z by ring,
    Real.rpow_sub hz,he]
  ring

end FirstJointLabel

theorem first_sideEnergy_eq_supported (labels : Finset Λ) (q : Λ → FirstJointLabel ι)
    (H : Λ → ℝ)
    (hsource : ∀ l ∈ labels, ∀ I, (q l).data.beta I ≠ 0 → (I.absNorm : ℝ) ≤ H l)
    (left : Bool) (t : ((l : Λ) × (q l).SourceIndex) → ℝ)
    (W : ((l : Λ) × (q l).SourceIndex) → 𝓢(ℝ,ℂ))
    (K : ((l : Λ) × (q l).SourceIndex) → ℝ) :
    (∑ k ∈ firstSourceLabels labels q,
      ((q k.1).sourceChild k.2).sideEnergy left (t k) (W k) (K k)) =
      ∑ k ∈ firstSideSourceLabels labels q H left,
        ((q k.1).sourceChild k.2).sideEnergy left (t k) (W k) (K k) := by
  cases left
  · exact first_rightEnergy_eq_supported labels q H hsource t W K
  · exact first_leftEnergy_eq_supported labels q H hsource t W K

/-- This changes normalization without counting the source labels again. -/
theorem first_sideEnergy_from_supported_normalized
    (labels : Finset Λ) (q : Λ → FirstJointLabel ι) (ref : FirstJointLabel ι)
    (H : Λ → ℝ)
    (hsource : ∀ l ∈ labels, ∀ I, (q l).data.beta I ≠ 0 → (I.absNorm : ℝ) ≤ H l)
    (left : Bool) (t : ((l : Λ) × (q l).SourceIndex) → ℝ)
    (W : ((l : Λ) × (q l).SourceIndex) → 𝓢(ℝ,ℂ))
    (K : ((l : Λ) × (q l).SourceIndex) → ℝ)
    (V Z A C loss : ℝ) (hV : 0 < V) (hZ : 1 < Z)
    (hbound : (∑ k ∈ firstSideSourceLabels labels q H left,
      ((q k.1).sourceChild k.2).sideEnergy left (t k) (W k) (K k)/V) ≤
      C*Z^(ref.radicalWidth Z+A-2*ref.sideWidth left Z+ref.activeWidth Z+
        ref.punctureWidth Z+ref.sideAllowance left Z+loss)) :
    (∑ k ∈ firstSourceLabels labels q,
      ((q k.1).sourceChild k.2).sideEnergy left (t k) (W k) (K k)) ≤
      (V/(ref.sideCommon left).absNorm : ℝ)*
        (C*Z^(ref.sideTargetWidth left Z A+loss)) := by
  rw [first_sideEnergy_eq_supported labels q H hsource left t W K]
  rw [←Finset.sum_div,ref.side_target_power left Z A C loss hZ] at hbound
  have hh := (div_le_iff₀ hV).mp hbound
  convert hh using 1 <;> ring

#print axioms first_sideEnergy_from_supported_normalized
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstSideEnergy -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighSourceGeometry ; sha256 69c7267e1fc961cc7587f2d5ac16576c50183cbae8a8728c29aa6ec34c459e1d -/
section




/-! The genuine high-source estimate summed over both actual dyadic block
families. Maximization pays their subpower mass without recounting arithmetic rows. -/
set_option autoImplicit false
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

theorem actual_joint_high_source_geometry
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
      ∀ (d P W : ℝ), dmin ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (input : Input Slot) (puncture seed : Ideal O)
        (hpuncture : puncture ≠ 0) (hseed : Squarefree seed)
        (hz₁ : input.W₁ 0 = 0) (hz₂ : input.W₂ 0 = 0)
        (side : Bool) (ξ₁ ξ₂ : RayCharacter)
        (fallback : NonzeroJointSourceRow (original input puncture seed) side)
        (qs : Finset (NonzeroJointSourceRow (original input puncture seed) side)),
      let S := qs.image NonzeroJointSourceRow.label
      let unit := sourceUnit fallback η ξ₁ ξ₂
      let w := sourceRow fallback η ξ₁ ξ₂
      let s := sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ 1 1
      let first := sourceFirst fallback η ξ₁ ξ₂
      let z := sourceFrequency fallback
      let Ds := fun v => (s v).physicalProjectors
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ q ∈ qs, Squarefree q.val.L) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      sourceRadius input ≤ Z^B →
      ∀ Kfirst Rfirst Hfirst : NonzeroJointSourceRow (original input puncture seed) side → ℝ,
      (∀ q ∈ qs, 0 < Kfirst q ∧ 0 < Hfirst q ∧
        Rfirst q ≤ Crdyad₁*Z^Ldyad₁ ∧ Hfirst q ≤ Z^Bdyad₁) →
      ∀ Ksecond Rsecond Hsecond : (q : NonzeroJointSourceRow (original input puncture seed) side) → q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q) → ℝ,
      (∀ q ∈ qs, ∀ n₁, 0 < Ksecond q n₁ ∧
        Rsecond q n₁ ≤ Crdyad₂*Z^Ldyad₂ ∧ Hsecond q n₁ ≤ Z^Bdyad₂) →
      ∀ (t tbase firstU firstTheta : (q : NonzeroJointSourceRow (original input puncture seed) side) → q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q) → ℝ)
        (good : (q : NonzeroJointSourceRow (original input puncture seed) side) → q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q) → Prop)
        (σ freq : JointReconstructionLabel → Slot → ℝ)
        (θ : JointReconstructionLabel → Slot → RayQuotient.Characters M H)
        (slotWidth : JointReconstructionLabel → Slot → ℝ),
      (∀ v ∈ S, (∀ j, (s v).input.M j ≤ Mslot) ∧ (s v).input.upper ≤ upper ∧
        (s v).input.b₁ ≤ b₁ ∧ (s v).input.b₂ ≤ b₂plain) →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        ∃ rows : Finset O, physicalBlock (s q.label).parent (t q b.1)
          (s q.label).toKernelLabel.columns (s q.label).toKernelLabel.beta
          (s q.label).second.val.1 (s q.label).second.val.2
          (s q.label).toKernelLabel.hC (s q.label).toKernelLabel.hD (s q.label).partition
          (Rsecond q b.1) rows Wkernel (Ksecond q b.1) (fun j => b.2 j) ≠ 0) →
      ∀ Bmask : ℝ, W+Bmask+conductorReserve ≤ d →
      (∀ v ∈ S, (((first v).leftPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask ∧
        (((first v).rightPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask) →
      (∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂) →
      (∀ v ∈ S, CenteredMomentAllocatedRayDictionary.Matches M H hH (s v).input
        ηcommon (θ v) (slotWidth v) (σ v) (freq v) Wslot bslot Z) →
      (∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth) →
      (∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        t q b.1 = tbase q b.1+2*Real.pi*(firstU q b.1-firstTheta q b.1)) →
      (∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        |tbase q b.1| ≤ Z^ν ∧ |firstU q b.1| ≤ Z^ν ∧ |firstTheta q b.1| ≤ Z^ν) →
      (∀ v ∈ S, ∀ j, σmin ≤ σ v j ∧ σ v j ≤ σmax) →
      (∀ v ∈ S, ∀ j, |freq v j| ≤ Z^ν) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      ∀ supportLoss clipLoss commonLoss : ℝ, supportLoss+clipLoss+commonLoss ≤ lengthLoss →
      (∀ v ∈ S, CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData ≤ Z^A) →
      (∀ v ∈ S, Z^(c+c₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ∧
        Z^(c+d₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ)) →
      (∀ v ∈ S, (max 1 (s v).input.upper)^Fintype.card Slot ≤ Z^supportLoss) →
      Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ clipLoss →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss ≤ tailA →

      targetLower ≤ π+A-c+R₁+E+Bc-144011/109800000 →
      ∀ scalarLoss : ℝ,
      (∀ q ∈ qs, ∀ b : q.val.DyadicFiber (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
        Ksecond q b.1 ≤ Z^(2*A-c-d₁+R₁+E-1+max (d₁-c) 0+6*(3/500)+(omegaLoss-scalarLoss))) →
      (∀ v ∈ S, (s v).secondLogCost Z ≤ g₂-t₂cost-b₂+scalarLoss) →
      ∀ (rowc rowd rowR rowe rowomega rowL sourceLoss subsetLoss ξ
        pMissing rMissing eMissing cancelMissing : ℝ),
      sourceRadius input ≤ Z^(A+sourceLoss) →
      1-rowR-max (rowc-rowd) 0+rowL-6*(3/500)-rowomega+
        2*sourceLoss+subsetLoss+ξ/2+rowAbsorb ≤ W →
      pMissing-rMissing-eMissing+cancelMissing ≤ P →
      (∀ q ∈ qs, q.val.E ∈ (principalSupport Finset.univ
        (leftExponent q.val.first.val.1 q.val.first.val.2)
        (rightExponent q.val.first.val.1 q.val.first.val.2)).powerset) →
      (∀ q ∈ qs, Z^rowc ≤ (q.label.C₁.absNorm : ℝ) ∧
        normValue (primeSubsetGenerator (fun P : CommonIndex q.label.C₁ q.label.D₁ => P.val) q.label.E) ≤ Z^(rowe+subsetLoss) ∧
        normValue (leftEffectiveFactor q.label.C₁ q.label.D₁) ≤ Z^rowL ∧
        Z^rMissing ≤ normValue (activeConductor q.label.C₁ q.label.D₁) ∧
        Z^eMissing ≤ normValue (primeSubsetGenerator (fun P : CommonIndex q.label.C₁ q.label.D₁ => P.val) q.label.E) ∧
        ((commonRadical q.label.C₁ q.label.D₁).absNorm : ℝ) ≤ Z^pMissing ∧
        ((canceledIdeal q.label.C₁ q.label.D₁ 5).absNorm : ℝ) ≤ Z^cancelMissing) →
      (∀ q ∈ qs, ∃ n₁ : q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q),
        Z^(2*A-rowc-rowd+rowR+rowe-1+max (rowd-rowc) 0+6*(3/500)+rowomega) ≤ Ksecond q n₁ ∧
        Rsecond q n₁ = frequencyRadius
          ((sourceRadius input/(q.label.C₁.absNorm : ℝ))^2/Ksecond q n₁) Z ξ ∧
        q.val.z ∈ ActualJointSourceRow.liveFrequencyRows q.val.second.val.1 q.val.second.val.2
          q.val.U (Rsecond q n₁)) →
      ∀ volumeLoss : ℝ,
      Z^(A-volumeLoss) ≤ CenteredMomentExceptionalAmplitudePair.volume input.toData →
      (∑ q ∈ qs, ∑ n₁ : q.val.FirstDyadic (Kfirst q) (Rfirst q) (Hfirst q),
        ∑ n₂ : q.val.SecondDyadic (Ksecond q n₁) (Rsecond q n₁) (Hsecond q n₁),
          if good q ⟨n₁,n₂⟩ then
            ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ∑ D ∈ Ds q.label,
              ‖((s q.label).withRays χ ξ).physicalRowTerm
                (CenteredMomentExceptionalAmplitudePair.volume input.toData)
                (actualHighPrimeCount M H Sbad Z)
                (t q n₁) q.val.z Wkernel (Ksecond q n₁) (Rsecond q n₁) (fun j => n₂ j) D‖
          else 0) ≤ C*Z^(π+A-2*c+R₁+E+Bc+volumeLoss-144011/219600000+dyadicLoss) := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_source_dyadic η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
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
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,?_⟩
  filter_upwards [hhigh,eventually_source_row_geometry rowAbsorb hrowAbsorb] with Z hZ hrowZ
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
    input puncture seed hpuncture hseed hz₁ hz₂ side ξ₁ ξ₂ fallback qs
  dsimp only
  let S := qs.image NonzeroJointSourceRow.label
  let w := sourceRow fallback η ξ₁ ξ₂
  let s := sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ 1 1
  let first := sourceFirst fallback η ξ₁ ξ₂
  let Ds := fun v => (s v).physicalProjectors
  intro R hR hprojSource hbin hsourceRadius
    Kfirst Rfirst Hfirst hfirstDyadic Ksecond Rsecond Hsecond hsecondDyadic
    t tbase firstU firstTheta good σ freq θ slotWidth
    hprofileCaps hsourceIntervals hphysicalSource
    Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hKactual hcost
    rowc rowd rowR rowe rowomega rowL sourceLoss subsetLoss ξ
    pMissing rMissing eMissing cancelMissing hsourceRow hrowBudget hmissingBudget
    hprincipal hfirstGeometry hrowSupport volumeLoss hVolumeLower
  have hradiusPos := fallback.val.sourceRadius_pos input puncture seed hz₁ hz₂
  have hsinput (v : JointReconstructionLabel) : (s v).input = input := rfl
  have hnorm : ∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧
      (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧
      (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B := by
    intro v hv
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
    have hh := q.val.actual_four_common_norms input puncture seed hz₁ hz₂
    exact ⟨hh.1.trans hsourceRadius,hh.2.1.trans hsourceRadius,
      hh.2.2.1.trans hsourceRadius,hh.2.2.2.trans hsourceRadius⟩
  have hNw : ∀ v ∈ S, ((Ideal.span {(w v).val}).absNorm : ℝ) ≤ Z^W := by
    intro v hv
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨n₁,hK,hradius,hlive⟩ := hrowSupport q hq
    have hh := hrowZ.2 (original input puncture seed) side q.val η ξ₁ ξ₂ q.property
      A rowc rowd rowR rowe 1 (3/500) rowomega rowL (sourceRadius input)
      sourceLoss subsetLoss ξ (Ksecond q n₁) W hradiusPos.le hsourceRow
      (hfirstGeometry q hq).1 (hfirstGeometry q hq).2.1 (hfirstGeometry q hq).2.2.1
      hK hrowBudget
      (CenteredMomentSecondRetainedRows.retainedRows
        (frequencyRadius ((sourceRadius input/(q.label.C₁.absNorm : ℝ))^2/Ksecond q n₁) Z ξ)
        (commonFrequencyGenerator q.val.second.val.1 q.val.second.val.2*
          nonunitFrequencyGenerator q.val.second.val.1 q.val.second.val.2 q.val.U))
      (by simpa only [ActualJointSourceRow.liveFrequencyRows,hradius,NonzeroJointSourceRow.label] using hlive)
    simpa only [w,sourceRow,recover_label] using hh
  have hNr : ∀ v ∈ S, ((jointMissingRadical v.C₁ (w v).val).absNorm : ℝ) ≤ Z^P := by
    intro v hv
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
    have hh := q.val.source_missing_geometry η ξ₁ ξ₂ q.property (hprincipal q hq)
      Z pMissing rMissing eMissing cancelMissing hZ.1
      (hfirstGeometry q hq).2.2.2.1 (hfirstGeometry q hq).2.2.2.2.1
      (hfirstGeometry q hq).2.2.2.2.2.1 (hfirstGeometry q hq).2.2.2.2.2.2
    have hbound := hh.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hmissingBudget)
    change ((jointMissingRadical q.label.C₁ (sourceRow fallback η ξ₁ ξ₂ q.label).val).absNorm : ℝ) ≤ Z^P
    simp only [sourceRow,recover_label]
    change ((jointMissingRadical q.val.label.C₁
      (q.val.reconstructed η ξ₁ ξ₂ q.property).val).absNorm : ℝ) ≤ Z^P
    exact hbound
  have hsourceRadius₂ : sourceRadius input ≤ Z^(2*B) := hsourceRadius.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  have hsourceNorm : ∀ v ∈ S,
      (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^(2*B) ∧
      (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^(2*B) := by
    intro v hv
    exact ((s v).actual_norm_power_caps hz₁ hz₂ Z (2*B) hsourceRadius₂).1
  have hprojectorNorm : ∀ v ∈ S, ∀ D ∈ Ds v,
      (UniqueFactorizationMonoid.moebius D : ℂ) ≠ 0 → (D.absNorm : ℝ) ≤ Z^(2*B) := by
    intro v hv D hD _
    exact ((s v).actual_norm_power_caps hz₁ hz₂ Z (2*B) hsourceRadius₂).2 D hD
  have hphysical : ∀ q ∈ qs, ∀ b : q.val.DyadicFiber
      (Kfirst q) (Rfirst q) (Hfirst q) (Ksecond q) (Rsecond q) (Hsecond q), good q b →
      0 < dyadicScale (b.2 2) ∧ 0 < dyadicScale (b.2 3) ∧
      aSource*CenteredMomentExceptionalAmplitudePair.volume (s q.label).input.toData/
        (((s q.label).firstCommon*(s q.label).second.val.1).absNorm : ℝ) ≤ dyadicScale (b.2 2) ∧
      aSource*CenteredMomentExceptionalAmplitudePair.volume (s q.label).input.toData/
        (((s q.label).firstCommon*(s q.label).second.val.2).absNorm : ℝ) ≤ dyadicScale (b.2 3) := by
    intro q hq b hgood
    obtain ⟨rows,hblock⟩ := hphysicalSource q hq b hgood
    have hq' : q.label ∈ S := Finset.mem_image.mpr ⟨q,hq,rfl⟩
    have h₁ : ∀ x, (s q.label).input.W₁ x ≠ 0 → a₁ ≤ x := by
      intro x hx
      rw [(hplain q.label hq').1] at hx
      exact (hs₁ hx).1
    have h₂ : ∀ x, (s q.label).input.W₂ x ≠ 0 → a₂ ≤ x := by
      intro x hx
      rw [(hplain q.label hq').2] at hx
      exact (hs₂ hx).1
    have hlower : originalLowerProfile (s q.label).input a₁ a₂ = aSource := by
      rw [originalLowerProfile,haSource_eq]
      congr 2
      apply Finset.prod_congr rfl
      intro j hj
      exact (hsourceIntervals q.label hq').1 j
    have hh := (s q.label).actual_physical_lower_dyads a₁ a₂ ha₁ ha₂ h₁ h₂
      (t q b.1) (Rsecond q b.1) rows Wkernel (Ksecond q b.1) (fun j => b.2 j) hblock
    simpa only [hlower] using hh
  exact hZ.2 d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
    input puncture seed hpuncture hseed hz₁ hz₂ side ξ₁ ξ₂ fallback qs
    R hR hprojSource hbin hnorm hNw hNr
    Kfirst Rfirst Hfirst hfirstDyadic Ksecond Rsecond Hsecond hsecondDyadic
    t tbase firstU firstTheta good σ freq θ slotWidth
    hprofileCaps hsourceIntervals hsourceNorm hprojectorNorm hphysical
    Bmask hconductorBalance hmaskNorm hplain hmatch hscale hprimeScale
    hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hKactual hcost volumeLoss hVolumeLower

end FixedData
#print axioms actual_joint_high_source_geometry
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighSourceGeometry -/
