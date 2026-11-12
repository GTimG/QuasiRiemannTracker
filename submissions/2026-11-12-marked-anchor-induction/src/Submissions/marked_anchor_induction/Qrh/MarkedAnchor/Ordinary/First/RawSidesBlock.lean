/- Copyright (c) 2026 Sil. Apache-2.0.
Seam 0 consumer at block level (`block_of_summed_raw_sides`, BALANCED form).

The actual first physical block is expanded exactly (`actual_block_expansion`), the
first artificial-divisor sum is restricted to the squarefree divisors and moved INSIDE the
ray expansion (`summed_projector_regroup`), the summed matrix is bounded once by the joint
kernel estimate fed by the balanced side bounds (`Second.Concrete.balanced_kernel`), the
window pair is priced by FP's `window_pair_reference` at the unit divisor, and the ray
projector costs `256`. Compared with FP `block_of_raw_sides` the factor
`artificialMass s C D` is GONE; the right-hand side is otherwise identical.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.sil_density_split_20261026.CubeFree.First.RawSides
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RepairedFirstRawBlock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.First
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.First
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentFirstColumns CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentSecondWindowBudget CenteredMomentLogDyadic
open FP.MixedPrincipalPair FP.MixedPrincipalWindow FP.MixedFirstAveragedWindow
open FP.MixedFirstPhysicalApplication FP.MixedFirstPhysicalBudget FP.MixedFirstCommonSum
open FP.RepairedFirstRawSides FP.RepairedFirstRawScalar FP.RepairedFirstRawBlock
open ActualEisensteinCubic FP.MixedInnerExceptionalBlock CenteredMomentHeckeExpansion
open Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- FP's per-divisor side budget at the unit divisor is the joint budget. -/
theorem sideBudget_one (s : Source ι a b) (τ : Character) (G opp : Id) (A Z loss : ℝ) :
    sideBudget s τ G opp 1 A Z loss = concreteJointBudget s τ G opp A Z loss := by
  unfold sideBudget concreteJointBudget
  simp only [map_one, Nat.cast_one, div_one]

/-- The squarefree restriction of the first artificial-divisor sum is exact. -/
theorem artificial_sum_squarefree (s : Source ι a b) (C D : Id) (hD : D ≠ 0) (f : Id → ℂ) :
    (∑ u ∈ concreteArtificial s C D hD, (UniqueFactorizationMonoid.moebius u : ℂ)*f u) =
      ∑ u ∈ artificialDivisors s C D hD, (UniqueFactorizationMonoid.moebius u : ℂ)*f u := by
  unfold concreteArtificial
  apply Finset.sum_filter_of_ne
  intro u _ hu
  exact left_ne_zero_of_mul hu

set_option maxHeartbeats 1400000 in
/-- **Balanced Seam 0 at block level**: the same
right-hand side as FP `block_of_raw_sides` WITHOUT the artificial-divisor mass. -/
theorem block_of_summed_raw_sides (Φ : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
    ∀ s : Source ι a b, ∀ ha : 0 < a, s.d = (1,1) →
    ∀ (η : Character) (t : ℝ) (C D : Id) (hC : Supported C) (hD : Supported D),
    CompletedGauss.primeSupport C = CompletedGauss.primeSupport D →
    ∀ E : Finset (CommonIndex C D), ∀ rows : Finset O, (∀ z ∈ rows, z ≠ 0) →
    ∀ K K₀ H₀ A₀ B₀ KL KR Z A loss : ℝ,
      0 < K → 0 < K₀ → 0 < H₀ → 0 < A₀ → 0 < B₀ → 0 < KL → 0 < KR → 1 < Z → 0 ≤ A →
      (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KL) → (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KR) →
      BalancedSummedRawSideBounds s ha η C D hC hD E KL KR A Z loss J →
    ‖blockTerm s ha η t C D hC hD E rows Φ K K₀ H₀ A₀ B₀‖/sourceVolume s ≤
      (256*Ckernel*(4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*
        (windowMass J t)^2*A*Z^loss)*commonWeight C D E := by
  obtain ⟨Ckernel, hCkernel, hkernel⟩ := balanced_kernel (ι := ι) (a := a) (b := b) Φ J
  refine ⟨Ckernel, hCkernel, ?_⟩
  intro s ha hunit η t C D hC hD hCD E rows hrows K K₀ H₀ A₀ B₀ KL KR Z A loss
    hK hK₀ hH₀ hA₀ hB₀ hKL hKR hZ hA hrowsL hrowsR hside
  have hz : 0 < Z := zero_lt_one.trans hZ
  let pref := referencePrefactor s η C D E K (Real.log 4)
  let H := Ckernel*(pref*(windowMass J t)^2*(A*Z^loss/((1:Id).absNorm:ℝ)))
  let r := ‖scalar C D hC E K A₀ B₀‖/sourceVolume s
  let phase := activeRow C D hC (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
  let Us := concreteArtificial s C D hD.1
  let mat := fun (χ ξ : RayCharacter) => summedMatrix s ha C D hC hD E Us
    (fixedPair η C D hC E χ (ξ⁻¹)).left (fixedPair η C D hC E χ (ξ⁻¹)).right
    t rows Φ K K₀ H₀ A₀ B₀
  have hr : 0 ≤ r := div_nonneg (norm_nonneg _) (sourceVolume_pos s).le
  have hpref : 0 ≤ pref := referencePrefactor_nonneg s η C D E K (Real.log 4) hK.le
  have hphase : ‖phase‖ ≤ 1 := QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _
  have hheight : ‖commonHeight s η t C D‖ ≤ 1 := by
    rw [commonHeight, norm_mul, norm_star]
    exact (mul_le_mul (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η
        (fixedBadMask*idealGenerator s.R) 1 1 t C hC.1)
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η
        (fixedBadMask*idealGenerator s.R) 1 1 t D hD.1)
      (norm_nonneg _) zero_le_one).trans_eq (by ring)
  have hRHS : 0 ≤ (256*Ckernel*(4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*
      (windowMass J t)^2*A*Z^loss)*commonWeight C D E := by
    have hw := common_weight_nonneg C D E
    have hf := fixedPresentationCost_pos
    positivity
  by_cases hzero : block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
      (sourceCoefficient s ha 1) C D hC hD E rows Φ (fun _ => logAnnulus) K K₀ H₀ A₀ B₀ = 0
  · simp only [blockTerm, hzero, mul_zero, norm_zero, zero_div]
    exact hRHS
  have hmat : ∀ χ ξ, r*‖mat χ ξ‖ ≤ H := by
    intro χ ξ
    have hk := hkernel s ha η C D hC hD E t K K₀ H₀ A₀ B₀ KL KR A Z loss hK₀ hH₀ hA₀ hB₀ hKL hKR
      hA hz.le rows hrowsL hrowsR hside χ ξ
    have hnorm := window_pair_reference s ha η t C D hC hD hCD E χ ξ rows Φ
      K K₀ H₀ A₀ B₀ Z A loss hK hA₀ hB₀ hZ hA 1 J hzero
    simp only [sideBudget_one] at hnorm
    calc
      r*‖mat χ ξ‖ ≤ r*(Ckernel*(windowBudget J t
            (concreteJointBudget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss)*
          windowBudget J t
            (concreteJointBudget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss))) :=
        mul_le_mul_of_nonneg_left hk hr
      _ = Ckernel*(r*(windowBudget J t
            (concreteJointBudget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss)*
          windowBudget J t
            (concreteJointBudget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss))) := by ring
      _ ≤ H := mul_le_mul_of_nonneg_left hnorm hCkernel
  have hproj := summed_ray_projector r H hr mat hmat
  have hexp := actual_block_expansion s ha η t C D hC hD hCD E rows hrows Φ K K₀ H₀ A₀ B₀
    hK hK₀ hH₀ hA₀ hB₀
  have hregroup : (∑ u ∈ artificialDivisors s C D hD.1,
      (UniqueFactorizationMonoid.moebius u : ℂ)*phase*
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ*
          FP.RepairedFirstRawKernel.matrix s ha C D hC hD E u (fixedPair η C D hC E χ (ξ⁻¹)).left
            (fixedPair η C D hC E χ (ξ⁻¹)).right t rows Φ K K₀ H₀ A₀ B₀) =
      phase*∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ*mat χ ξ := by
    have h1 := artificial_sum_squarefree s C D hD.1 (fun u => phase*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ*
        FP.RepairedFirstRawKernel.matrix s ha C D hC hD E u (fixedPair η C D hC E χ (ξ⁻¹)).left
          (fixedPair η C D hC E χ (ξ⁻¹)).right t rows Φ K K₀ H₀ A₀ B₀)
    simp only [← mul_assoc] at h1
    rw [← h1, summed_projector_regroup]
    rfl
  rw [hexp]
  have hsum := hregroup
  simp only [mul_assoc] at hsum ⊢
  rw [show (∑ u ∈ artificialDivisors s C D hD.1,
      (UniqueFactorizationMonoid.moebius u : ℂ)*(phase*
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ*
          FP.RepairedFirstRawKernel.matrix s ha C D hC hD E u (fixedPair η C D hC E χ (ξ⁻¹)).left
            (fixedPair η C D hC E χ (ξ⁻¹)).right t rows Φ K K₀ H₀ A₀ B₀)) =
      phase*∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ*mat χ ξ from hsum]
  set T := ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ*mat χ ξ with hT
  have hstep : ‖commonHeight s η t C D*(scalar C D hC E K A₀ B₀*(phase*T))‖/sourceVolume s ≤
      r*‖T‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    have hb : ‖commonHeight s η t C D‖*(‖scalar C D hC E K A₀ B₀‖*(‖phase‖*‖T‖)) ≤
        ‖scalar C D hC E K A₀ B₀‖*‖T‖ := by
      have h1 : ‖phase‖*‖T‖ ≤ ‖T‖ := mul_le_of_le_one_left (norm_nonneg _) hphase
      have h2 : ‖scalar C D hC E K A₀ B₀‖*(‖phase‖*‖T‖) ≤ ‖scalar C D hC E K A₀ B₀‖*‖T‖ :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      exact (mul_le_of_le_one_left (by positivity) hheight).trans h2
    calc _ ≤ ‖scalar C D hC E K A₀ B₀‖*‖T‖/sourceVolume s :=
          div_le_div_of_nonneg_right hb (sourceVolume_pos s).le
      _ = r*‖T‖ := by dsimp only [r]; ring
  refine hstep.trans (hproj.trans_eq ?_)
  dsimp only [H, pref]
  rw [unit_prefactor s hunit η C D E K]
  simp only [map_one, Nat.cast_one, div_one]
  ring

end
end Qrh.MarkedAnchor.Ordinary.First
