/- Copyright (c) 2026 Sil. Apache-2.0.
All-positive-scale cancellation for equal-product rectangles. The trivial
volume bound covers subunit scales, so shortening never loses a hypothesis.
The character, its natural zeros, and both profiles are kept identical.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.HeckeTwist

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.Feedback.FourthPower.PrincipalRectangle
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentHeckeTwist CenteredMomentHeckeCancellation CenteredMomentLattice
local notation "O" => ActualEisensteinCubic.O

/-- A first-order saving and a volume bound give every fractional saving,
including when L is below one. No interpolation assumption is needed. -/
theorem fractional_of_two_bounds (r A B T L α : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T) (hL : 0 < L)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hvol : r ≤ B*T) (hsave : r ≤ A*(T/L)) :
    r ≤ (A+B)*T*L^(-α) := by
  by_cases hL1 : 1 ≤ L
  · have hr : L⁻¹ ≤ L^(-α) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    calc
      r ≤ A*(T/L) := hsave
      _ = A*T*L⁻¹ := by ring
      _ ≤ A*T*L^(-α) := mul_le_mul_of_nonneg_left hr (mul_nonneg hA hT)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : A ≤ A+B) hT) (by positivity)
  · have hh : L^α ≤ 1 := Real.rpow_le_one hL.le (le_of_not_ge hL1) hα
    have hp : 0 < L^α := Real.rpow_pos_of_pos hL _
    have hr : 1 ≤ L^(-α) := by
      rw [Real.rpow_neg hL.le]
      exact (one_le_inv₀ hp).mpr hh
    calc
      r ≤ B*T := hvol
      _ ≤ (A+B)*T := mul_le_mul_of_nonneg_right (by linarith) hT
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (add_nonneg hA hB) hT) hr

theorem normalized_fractional_rectangle
    (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ M₁ M₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ M₂)
    (t X₁ X₂ Y₁ Y₂ T L α : ℝ) (hL : 0 < L) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁*X₂=T) (hprodY : Y₁*Y₂=T) :
    let E := volumeControl Q χ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
      volumeControl Q χ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
    let K := 4*E*(128*(b₁*M₁+b₂*M₂))+2*(128*b₁*M₁)*(128*b₂*M₂)
    ‖(Real.sqrt T : ℂ)⁻¹ *
      (twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂ -
        twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂)‖ ≤
      K*Real.sqrt T*L^(-α) := by
  let E := volumeControl Q χ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
    volumeControl Q χ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
  let A := 4*E*(128*(b₁*M₁+b₂*M₂))
  let B := 2*(128*b₁*M₁)*(128*b₂*M₂)
  let D := twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂ -
    twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂
  have hT : 0 < T := hprodX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hA : 0 ≤ A := by
    have he : 0 ≤ E := add_nonneg (volumeControl_nonneg _ _ _) (volumeControl_nonneg _ _ _)
    dsimp only [A]
    positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have habs (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (hUV : U*V=T) :
      ‖twistedIdealSum χ W₁ t U*twistedIdealSum χ W₂ t V‖ ≤
        (128*b₁*M₁)*(128*b₂*M₂)*T := by
    rw [norm_mul]
    have hh := mul_le_mul
      (twistedIdealSum_absolute χ W₁ a₁ b₁ M₁ ha₁ hb₁ hM₁ hs₁ hW₁ hbound₁ t U hU)
      (twistedIdealSum_absolute χ W₂ a₂ b₂ M₂ ha₂ hb₂ hM₂ hs₂ hW₂ hbound₂ t V hV)
      (norm_nonneg _) (by positivity)
    apply hh.trans_eq
    rw [← hUV]
    ring
  have hvol : ‖D‖ ≤ B*T := by
    have h := (norm_sub_le _ _).trans (add_le_add
      (habs X₁ X₂ (hL.trans_le hX₁) (hL.trans_le hX₂) hprodX)
      (habs Y₁ Y₂ (hL.trans_le hY₁) (hL.trans_le hY₂) hprodY))
    exact h.trans_eq (by dsimp only [B]; ring)
  have hsave : ‖D‖ ≤ A*(T/L) := actual_twisted_rectangle_saving
    η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ W₂ a₁ b₁ a₂ b₂ M₁ M₂
    ha₁ ha₂ hb₁ hb₂ hM₁ hM₂ hs₁ hs₂ hW₁ hW₂ hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY
  have hraw := fractional_of_two_bounds ‖D‖ A B T L α hA hB hT.le hL hα hα1 hvol hsave
  change ‖(Real.sqrt T : ℂ)⁻¹*D‖ ≤ (A+B)*Real.sqrt T*L^(-α)
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg T)]
  apply (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr (Real.sqrt_nonneg T))).trans_eq
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have he : Real.sqrt T*Real.sqrt T=T := Real.mul_self_sqrt hT.le
  have hc : (Real.sqrt T)⁻¹*T=Real.sqrt T := by
    calc
      _ = (Real.sqrt T)⁻¹*(Real.sqrt T*Real.sqrt T) := congrArg (fun x => (Real.sqrt T)⁻¹*x) he.symm
      _ = _ := inv_mul_cancel_left₀ hs.ne' _
  calc
    _ = (A+B)*((Real.sqrt T)⁻¹*T)*L^(-α) := by ring
    _ = _ := by rw [hc]

end
end Candidate.Feedback.FourthPower.PrincipalRectangle
