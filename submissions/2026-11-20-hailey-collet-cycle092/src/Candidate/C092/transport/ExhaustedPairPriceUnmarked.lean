/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Independent ordinary characters and heights on actual regular core subrows.
The fourth suppliers are the original zero-slot source at the same U^V. -/
import Candidate.C092.transport.StrongPairOrdinaryUnmarked
import Candidate.C092.transport.StrongPairSmallUnmarked
import Candidate.C092.transport.TinyCoreUnmarked
import Candidate.C092.transport.TinyCoreBridgeData

namespace QRH.Cycle092.ExhaustedPairPrice
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ConcreteTraceCRT
open CenteredMomentCoreFloor CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore
open QRH.Cycle092.CofactorOrdinary QRH.Cycle092.StrongPair
local notation "O" => ActualEisensteinCubic.O

theorem exhausted_fourth_source
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (bΦ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hbΦ : 0 < bΦ)
    (hsΦ : Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (η η₀ : Character) (Q : Ideal O)
    (hQray : Q ≤ rayM) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)}) :
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop, ∀ hU : 1 ≤ U,
      ∀ V : ℝ, 0 ≤ V → V ≤ 1 →
      ∀ (p : Profiles (1/4) (9/4)) (j : Fin 2) (t height X : ℝ),
        0 ≤ height → 0 < X → X ≤ U →
      ∀ (s : Finset FreeRow),
        (∀ u ∈ s, initialKeep η (internalQ Q η₀) u.val) →
        (∀ u ∈ s, rowNorm u ≤ U^V) →
      (∑ u ∈ s, ‖original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^4) ≤
        C*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl controls (p.profile j))^4*
          (1+|t|+height)^degree*U^(V+ε) := by
  obtain ⟨degree,controls,C,hC,hsource⟩ := QRH.Cycle092.StrongPair.freely_small_unmarked_source hβ rayM Hr hHr
    bΦ ε hbΦ hε hε1 η η₀ Q hQray hQ0 hQt hQ72
  refine ⟨degree,controls,C,hC,hsource.mono ?_⟩
  intro U hsource hU V hV0 hV1 p j t height X hh hX hXU s hk hy
  have hfinite := finite_original_fourth η (internalQ Q η₀) (p.profile j) t X (9/4) (U^V)
    (fun _ hx => (p.support j hx).2) hX (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) s hk hy
  have hsource' := hsource hU V hV0 hV1 radialMajorant hsΦ radialMajorant_nonneg
    (repeatedProfile p j) t height X X hh hX hX hXU hXU
  apply hfinite.trans
  rw [repeated_control] at hsource'
  simpa only [repeatedProfile,← pow_mul] using hsource'


theorem exhausted_pair_unit_source
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (bΦ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hbΦ : 0 < bΦ)
    (hsΦ : Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ η₀₁ η₀₂ : Character) (Q₁ Q₂ : Ideal O)
    (hQ₁ray : Q₁ ≤ rayM) (hQ₁0 : internalQ Q₁ η₀₁ ≠ 0) (hQ₁t : internalQ Q₁ η₀₁ ≠ ⊤)
    (hQ₁72 : internalQ Q₁ η₀₁ ≤ Ideal.span {(72 : O)})
    (hQ₂ray : Q₂ ≤ rayM) (hQ₂0 : internalQ Q₂ η₀₂ ≠ 0) (hQ₂t : internalQ Q₂ η₀₂ ≠ ⊤)
    (hQ₂72 : internalQ Q₂ η₀₂ ≤ Ideal.span {(72 : O)}) :
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop, ∀ hU : 1 ≤ U,
      ∀ V : ℝ, 0 ≤ V → V ≤ 1 →
      ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
        0 ≤ height → 0 < X₁ → 0 < X₂ → X₁ ≤ U → X₂ ≤ U →
      ∀ (s : Finset FreeRow),
        (∀ u ∈ s, initialKeep η₁ (internalQ Q₁ η₀₁) u.val) →
        (∀ u ∈ s, initialKeep η₂ (internalQ Q₂ η₀₂) u.val) →
        (∀ u ∈ s, rowNorm u ≤ U^V) →
      (∑ u ∈ s,
        ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^2*
        ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 1) t₂ X₂‖^2) ≤
        C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
          (1+|t₁|+|t₂|+height)^degree*U^(V+ε) := by
  obtain ⟨d₁,S₁,C₁,hC₁,hfirst⟩ := exhausted_fourth_source hβ rayM Hr hHr
    bΦ ε hε hε1 hbΦ hsΦ η₁ η₀₁ Q₁ hQ₁ray hQ₁0 hQ₁t hQ₁72
  obtain ⟨d₂,S₂,C₂,hC₂,hsecond⟩ := exhausted_fourth_source hβ rayM Hr hHr
    bΦ ε hε hε1 hbΦ hsΦ η₂ η₀₂ Q₂ hQ₂ray hQ₂0 hQ₂t hQ₂72
  refine ⟨max d₁ d₂,S₁∪S₂,C₁+C₂+1,by positivity,?_⟩
  filter_upwards [hfirst,hsecond] with U hf hs
  intro hU V hV0 hV1 p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hX₁U hX₂U s hk₁ hk₂ hy
  have h₁ := hf hU V hV0 hV1 p 0 t₁ height X₁ hh hX₁ hX₁U s hk₁ hy
  have h₂ := hs hU V hV0 hV1 p 1 t₂ height X₂ hh hX₂ hX₂U s hk₂ hy
  let G := (C₁+C₂+1)*QuadraticInitialBound.diagonalControl radialMajorant*
    (1+|t₁|+|t₂|+height)^(max d₁ d₂)*U^(V+ε)
  let A := sourceControl (S₁∪S₂) (p.profile 0)
  let B := sourceControl (S₁∪S₂) (p.profile 1)
  have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hA := control_mono S₁ (S₁∪S₂) Finset.subset_union_left (p.profile 0)
  have hB := control_mono S₂ (S₁∪S₂) Finset.subset_union_right (p.profile 1)
  have hheight : 1 ≤ 1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hpow₁ : (1+|t₁|+height)^d₁ ≤ (1+|t₁|+|t₂|+height)^(max d₁ d₂) := by
    have hc : 1+|t₁|+height ≤ 1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₂]
    apply (pow_le_pow_left₀ (by positivity) hc d₁).trans
    exact pow_le_pow_right₀ hheight (le_max_left _ _)
  have hpow₂ : (1+|t₂|+height)^d₂ ≤ (1+|t₁|+|t₂|+height)^(max d₁ d₂) := by
    have hc : 1+|t₂|+height ≤ 1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₁]
    apply (pow_le_pow_left₀ (by positivity) hc d₂).trans
    exact pow_le_pow_right₀ hheight (le_max_right _ _)
  have hL : (∑ u ∈ s, ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^4) ≤ G*A^4 := by
    apply h₁.trans
    rw [show G*A^4 = (C₁+C₂+1)*QuadraticInitialBound.diagonalControl radialMajorant*
      (sourceControl (S₁∪S₂) (p.profile 0))^4*
      (1+|t₁|+|t₂|+height)^(max d₁ d₂)*U^(V+ε) by dsimp [G,A]; ring]
    have hC : C₁ ≤ C₁+C₂+1 := by linarith
    have hA0 := sourceControl_nonneg S₁ (p.profile 0)
    gcongr
  have hR : (∑ u ∈ s, ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 1) t₂ X₂‖^4) ≤ G*B^4 := by
    apply h₂.trans
    rw [show G*B^4 = (C₁+C₂+1)*QuadraticInitialBound.diagonalControl radialMajorant*
      (sourceControl (S₁∪S₂) (p.profile 1))^4*
      (1+|t₁|+|t₂|+height)^(max d₁ d₂)*U^(V+ε) by dsimp [G,B]; ring]
    have hC : C₂ ≤ C₁+C₂+1 := by linarith
    have hB0 := sourceControl_nonneg S₂ (p.profile 1)
    gcongr
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun u => ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^2)
    (fun u => ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 1) t₂ X₂‖^2)
  simp only [←pow_mul] at hcs
  have h := hcs.trans (common_cauchy_factor hG hL hR)
  convert h using 1 <;> dsimp [G,A,B,Profiles.control] <;> ring


#print axioms exhausted_fourth_source
#print axioms exhausted_pair_unit_source
end
end QRH.Cycle092.ExhaustedPairPrice
