/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The strengthened source contains the literal common-anchor finite source. -/
import Candidate.C092.transport.StrongPairOriginal

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

/-- No L-function, original polynomial, normalization, coefficient or row
is changed in extracting the original common-character finite energy. -/
theorem common_at {N Y l bΦ mesh ε Z C : ℝ} {W : ℝ→ℂ}
    {η η₀ : Character} {Q : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε Z
      η η η₀ η₀ Q Q degree controls C)
    (θ : Slot→RayQuotient.Characters rayM Hr) (w σ v : Slot→ℝ)
    (t height : ℝ) (hw : ∀ i,0 ≤ w i) (hwm : ∀ i,w i ≤ mesh)
    (hσlo : ∀ i,(33/50:ℝ) ≤ σ i) (hσhi : ∀ i,σ i ≤ (33/50:ℝ))
    (hh : 0 ≤ height) (hv : ∀ i,|v i| ≤ height) (hsum : (∑ i,w i) ≤ l)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hXN : length Z X₁ ≤ N) (hXY : length Z X₂ ≤ Y) (s : Finset FreeRow)
    (hk : ∀ u∈s,initialKeep η (internalQ Q η₀) u.val) (hy : ∀ u∈s,rowNorm u ≤ Z) :
    (∑ u∈s,‖original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t X₁*
      original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 1) t X₂‖^2*
      ∏ i,‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 Z w i)
        (originalCoefficients rayM Hr hHr η₀ θ W Z w σ v i) t (Z^(w i))‖^2) ≤
    C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
      (1+|t|+|t|+height)^degree*Z^(1+ε) := by
  have h := hsrc Finset.univ θ θ w σ σ v v t t height hw hwm hσlo hσhi hσlo hσhi hh hv hv
    hsum p X₁ X₂ hX₁ hX₂ hXN hXY s (originalMark rayM Hr hHr η η₀ θ W Z w σ v t)
    hk hk hy (fun _ _ _ _=>rfl) (fun _ _ _ _=>rfl)
  change finiteEnergy s η η (p.profile 0) (p.profile 1) t t X₁ X₂ _ ≤ _ at h
  rw [finiteEnergy_common] at h
  exact h

/-- Both full ordinary tuples exchange on any selected original subproduct. -/
theorem finiteEnergyOn_swap (T : Finset Slot) (s : Finset FreeRow)
    (η₁ η₂ : Character) (W₁ W₂ : ℝ→ℂ) (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot→FreeRow→ℂ) :
    finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark =
    finiteEnergyOn T s η₂ η₁ W₂ W₁ t₂ t₁ X₂ X₁ mark := by
  apply Finset.sum_congr rfl
  intro u hu
  ring

/-- The combined live pitch budget is imposed only after the source degree
has been fixed. It pays the literal polynomial from native_original_pair_source. -/
theorem bounded_original_payment {Z τ ε tOld t₁ t₂ height : ℝ} (degree : ℕ)
    (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (hh : 0 ≤ height)
    (hsmall : |tOld|+|t₁|+|t₂|+height ≤ Z^τ) :
    (1+|t₁|+|t₂|+(|tOld|+|t₁|+|t₂|+height))^degree*Z^(1+ε) ≤
      (4:ℝ)^degree*Z^(1+ε+τ*(degree:ℝ)) := by
  exact bounded_height_payment degree hZ hτ
    (by linarith [abs_nonneg tOld,abs_nonneg t₂])
    (by linarith [abs_nonneg tOld,abs_nonneg t₁]) (by positivity) hsmall

/-- A freely small positive frequency exponent exists after any finite
source degree; no Mellin tail order or zero-band bin count is identified with it. -/
theorem choose_tau_after_degree (degree : ℕ) {loss : ℝ} (hloss : 0 < loss) :
    ∃ τ : ℝ,0 < τ ∧ τ*(degree:ℝ) < loss := by
  let τ : ℝ := loss/(2*((degree:ℝ)+1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have he : τ*(2*((degree:ℝ)+1))=loss := by
    dsimp [τ]
    field_simp
  exact ⟨τ,hτ,by nlinarith [Nat.cast_nonneg (α:=ℝ) degree]⟩

#print axioms common_at
#print axioms bounded_height_payment
#print axioms finiteEnergyOn_swap
#print axioms bounded_original_payment
#print axioms choose_tau_after_degree
end
end QRH.Cycle092.StrongPair
