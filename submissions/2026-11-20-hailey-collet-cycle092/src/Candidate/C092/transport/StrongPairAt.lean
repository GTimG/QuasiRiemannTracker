/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The two authentic native arms yield the finite independent-character pair. -/
import Candidate.C092.transport.StrongPairNative

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

theorem native_pair_at {N Y q₁ q₂ bΦ mesh ε Z C₁ C₂ : ℝ} {W : ℝ→ℂ}
    {η₁ η₂ η₀₁ η₀₂ : Character} {Q₁ Q₂ : Ideal O}
    {d₁ d₂ : ℕ} {S₁ S₂ : Finset (ℕ×ℕ)}
    (hsrc₁ : LabelledAt (α:=Fin 2×Slot) rayM Hr hHr N N q₁ W
      2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε Z η₁ η₀₁ Q₁ d₁ S₁ C₁)
    (hsrc₂ : LabelledAt (α:=Fin 2×Slot) rayM Hr hHr Y Y q₂ W
      2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε Z η₂ η₀₂ Q₂ d₂ S₂ C₂)
    (hC₁ : 0≤C₁) (hC₂ : 0≤C₂)
    (T F : Finset Slot) (hFT : F⊆T) (θ₁ θ₂ : Slot→RayQuotient.Characters rayM Hr)
    (w σ₁ σ₂ v₁ v₂ : Slot→ℝ) (t₁ t₂ height : ℝ)
    (hw : ∀ i,0≤w i) (hwm : ∀ i,w i≤ mesh)
    (hσ₁lo : ∀ i,(33/50:ℝ)≤σ₁ i) (hσ₁hi : ∀ i,σ₁ i≤(33/50:ℝ))
    (hσ₂lo : ∀ i,(33/50:ℝ)≤σ₂ i) (hσ₂hi : ∀ i,σ₂ i≤(33/50:ℝ))
    (hh : 0≤height) (hv₁ : ∀ i,|v₁ i|≤height) (hv₂ : ∀ i,|v₂ i|≤height)
    (hΦs : Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hZ : 1<Z) (hXN : length Z X₁≤N) (hXY : length Z X₂≤Y)
    (hq₁ : 2*(∑ i∈F,w i)≤q₁) (hq₂ : 2*(∑ i∈T\F,w i)≤q₂)
    (s : Finset FreeRow) (mark : Slot→FreeRow→ℂ)
    (hk₁ : ∀ u∈s,initialKeep η₁ (internalQ Q₁ η₀₁) u.val)
    (hk₂ : ∀ u∈s,initialKeep η₂ (internalQ Q₂ η₀₂) u.val)
    (hy : ∀ u∈s,rowNorm u≤Z)
    (hmark₁ : ∀ u∈s,∀ i∈F,‖mark i u‖=
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 Z w i)
        (originalCoefficients rayM Hr hHr η₀₁ θ₁ W Z w σ₁ v₁ i) t₁ (Z^(w i))‖)
    (hmark₂ : ∀ u∈s,∀ i∈T\F,‖mark i u‖=
      ‖normalizedSlot η₂ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 Z w i)
        (originalCoefficients rayM Hr hHr η₀₂ θ₂ W Z w σ₂ v₂ i) t₂ (Z^(w i))‖) :
    finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
    (C₁+C₂+1)*QuadraticInitialBound.diagonalControl radialMajorant*(p.control (S₁∪S₂))^2*
      (1+|t₁|+|t₂|+height)^(max d₁ d₂)*Z^(1+ε) := by
  have hL := native_arm rayM Hr hHr hsrc₁ F θ₁ w σ₁ v₁ t₁ height hw hwm hσ₁lo hσ₁hi
    hh hv₁ hΦs p 0 X₁ hX₁ hZ hXN hq₁ s mark hk₁ hy hmark₁
  have hR := native_arm rayM Hr hHr hsrc₂ (T\F) θ₂ w σ₂ v₂ t₂ height hw hwm hσ₂lo hσ₂hi
    hh hv₂ hΦs p 1 X₂ hX₂ hZ hXY hq₂ s mark hk₂ hy hmark₂
  let G := (C₁+C₂+1)*QuadraticInitialBound.diagonalControl radialMajorant*
    (1+|t₁|+|t₂|+height)^(max d₁ d₂)*Z^(1+ε)
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
        (1+|t₁|+|t₂|+height)^(max d₁ d₂)*Z^(1+ε) := by gcongr
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
        (1+|t₁|+|t₂|+height)^(max d₁ d₂)*Z^(1+ε) := by gcongr
      _ = _ := by ring
  have h := (finite_split_cauchy_on T F hFT s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark).trans
    (common_cauchy_factor hG hL' hR')
  convert h using 1 <;> dsimp [G,A,B,Profiles.control] <;> ring

#print axioms native_pair_at
end
end QRH.Cycle092.StrongPair
