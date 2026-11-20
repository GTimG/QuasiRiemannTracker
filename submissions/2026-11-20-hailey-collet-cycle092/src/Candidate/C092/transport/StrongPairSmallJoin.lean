/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The two authentic native arms yield the finite independent-character pair. -/
import Candidate.C092.transport.StrongPairSmallArm

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
local notation "O" => ActualEisensteinCubic.O

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

/-- Joining genuine arm estimates preserves both profiles, independent
ordinary pitches and every original physical mark. -/
theorem small_join_arms {U expo C₁ C₂ : ℝ} {η₁ η₂ : Character}
    {d₁ d₂ : ℕ} {S₁ S₂ : Finset (ℕ×ℕ)}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hU : 0<U)
    (T F : Finset Slot) (hFT : F⊆T) (s : Finset FreeRow)
    (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ) (hh : 0 ≤ height)
    (mark : Slot→FreeRow→ℂ)
    (hL : (∑ u∈s,(‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^2*
      ∏ i∈F,‖mark i u‖^2)^2) ≤
      C₁*QuadraticInitialBound.diagonalControl radialMajorant*
      (sourceControl S₁ (p.profile 0))^4*(1+|t₁|+height)^d₁*U^expo)
    (hR : (∑ u∈s,(‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 1) t₂ X₂‖^2*
      ∏ i∈T\F,‖mark i u‖^2)^2) ≤
      C₂*QuadraticInitialBound.diagonalControl radialMajorant*
      (sourceControl S₂ (p.profile 1))^4*(1+|t₂|+height)^d₂*U^expo) :
    finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      (C₁+C₂+1)*QuadraticInitialBound.diagonalControl radialMajorant*(p.control (S₁∪S₂))^2*
      (1+|t₁|+|t₂|+height)^(max d₁ d₂)*U^expo := by
  let G := (C₁+C₂+1)*QuadraticInitialBound.diagonalControl radialMajorant*
    (1+|t₁|+|t₂|+height)^(max d₁ d₂)*U^expo
  let A := sourceControl (S₁∪S₂) (p.profile 0)
  let B := sourceControl (S₁∪S₂) (p.profile 1)
  have hd := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hheight : 1≤1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hG : 0≤G := by dsimp [G]; positivity
  have hp₁ : (1+|t₁|+height)^d₁ ≤ (1+|t₁|+|t₂|+height)^(max d₁ d₂) := by
    exact (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg t₂]) _).trans
      (pow_le_pow_right₀ hheight (le_max_left _ _))
  have hp₂ : (1+|t₂|+height)^d₂ ≤ (1+|t₁|+|t₂|+height)^(max d₁ d₂) := by
    exact (pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg t₁]) _).trans
      (pow_le_pow_right₀ hheight (le_max_right _ _))
  have hA := control_mono S₁ (S₁∪S₂) Finset.subset_union_left (p.profile 0)
  have hB := control_mono S₂ (S₁∪S₂) Finset.subset_union_right (p.profile 1)
  have hL' : (∑ u∈s,(‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^2*
      ∏ i∈F,‖mark i u‖^2)^2) ≤ G*A^4 := by
    apply hL.trans
    dsimp [G,A]
    have hc : C₁≤C₁+C₂+1 := by linarith
    have ha := sourceControl_nonneg S₁ (p.profile 0)
    calc
      _ ≤ (C₁+C₂+1)*QuadraticInitialBound.diagonalControl radialMajorant*
        (sourceControl (S₁∪S₂) (p.profile 0))^4*
        (1+|t₁|+|t₂|+height)^(max d₁ d₂)*U^expo := by gcongr
      _ = _ := by ring
  have hR' : (∑ u∈s,(‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 1) t₂ X₂‖^2*
      ∏ i∈T\F,‖mark i u‖^2)^2) ≤ G*B^4 := by
    apply hR.trans
    dsimp [G,B]
    have hc : C₂≤C₁+C₂+1 := by linarith
    have hb := sourceControl_nonneg S₂ (p.profile 1)
    calc
      _ ≤ (C₁+C₂+1)*QuadraticInitialBound.diagonalControl radialMajorant*
        (sourceControl (S₁∪S₂) (p.profile 1))^4*
        (1+|t₁|+|t₂|+height)^(max d₁ d₂)*U^expo := by gcongr
      _ = _ := by ring
  have h := (finite_split_cauchy_on T F hFT s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark).trans
    (common_cauchy_factor hG hL' hR')
  convert h using 1 <;> dsimp [G,A,B,Profiles.control] <;> ring


#print axioms small_join_arms
end
end QRH.Cycle092.StrongPair
