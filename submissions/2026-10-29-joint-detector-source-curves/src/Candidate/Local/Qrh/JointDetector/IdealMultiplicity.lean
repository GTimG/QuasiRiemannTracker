/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.IdealAmplification
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator

/-!
# Ordinary ideal merge multiplicity

A nonzero ideal product determines its second factor from its first. Hence
finite product fibers cost at most the ordinary ideal divisor function. The
existing small-power divisor bound makes this uniform on a norm range.
-/

namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentHeckeExpansion CenteredMomentSourceRow
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

/-- Projection to the first factor injects a nonzero ideal-product fiber into
all divisors of the product. Units and repeated prime factors are retained. -/
theorem idealProduct_fiber_card_le_divisors
    (sources monomials : Finset (Ideal O)) (T : Ideal O) (hT : T ≠ ⊥) :
    ((sources ×ˢ monomials).filter fun p => p.1 * p.2 = T).card ≤
      (idealDivisors T).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    have hmul := (Finset.mem_filter.mp hp).2
    exact (mem_idealDivisors hT).2 ⟨p.2, hmul.symm⟩
  · intro p hp q hq hfirst
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hnonzero : p.1 ≠ 0 := left_ne_zero_of_mul (hp' ▸ hT)
    have hmul : p.1 * p.2 = q.1 * q.2 := hp'.trans hq'.symm
    rw [← hfirst] at hmul
    exact Prod.ext hfirst (mul_left_cancel₀ hnonzero hmul)

/-- One fixed divisor constant, depending only on the requested positive loss. -/
def idealDivisorConstant (ε : ℝ) (hε : 0 < ε) : ℝ :=
  Classical.choose (IdealDivisorBound.ideal_divisor_small_power ε hε)

theorem idealDivisorConstant_pos (ε : ℝ) (hε : 0 < ε) :
    0 < idealDivisorConstant ε hε :=
  (Classical.choose_spec (IdealDivisorBound.ideal_divisor_small_power ε hε)).1

theorem idealDivisorConstant_bound (ε : ℝ) (hε : 0 < ε)
    (T : Ideal O) (hT : T ≠ ⊥) :
    ((idealDivisors T).card : ℝ) ≤
      idealDivisorConstant ε hε * (Ideal.absNorm T : ℝ) ^ ε :=
  (Classical.choose_spec (IdealDivisorBound.ideal_divisor_small_power ε hε)).2 T hT

/-- The finite merge fiber has a uniform small-power cost on the full norm
range. No coprimality or squarefree hypothesis is used. -/
theorem idealProduct_fiber_small_power
    (sources monomials : Finset (Ideal O)) (T : Ideal O) (hT : T ≠ ⊥)
    (ε : ℝ) (hε : 0 < ε) (X : ℝ) (hnorm : (Ideal.absNorm T : ℝ) ≤ X) :
    (((sources ×ˢ monomials).filter fun p => p.1 * p.2 = T).card : ℝ) ≤
      idealDivisorConstant ε hε * X ^ ε := by
  calc
    _ ≤ ((idealDivisors T).card : ℝ) := by
      exact_mod_cast idealProduct_fiber_card_le_divisors sources monomials T hT
    _ ≤ idealDivisorConstant ε hε * (Ideal.absNorm T : ℝ) ^ ε :=
      idealDivisorConstant_bound ε hε T hT
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hε.le)
      (idealDivisorConstant_pos ε hε).le

/-- Actual ordinary-source inverse amplification with its ideal-divisor cost
paid by a uniform small power. The only amplifier premises are its common
coefficient mass and its response on the selected rows. -/
theorem selectedNorm_inverse_amplification_small_power
    (rows : Finset O) (sources monomials merged : Finset (Ideal O))
    (hclosed : ∀ I ∈ sources, ∀ J ∈ monomials, I * J ∈ merged)
    (c : monomials → ℂ) (A C X ε : ℝ)
    (hA : 0 < A) (hC : 0 ≤ C) (hX : 0 ≤ X) (hε : 0 < ε)
    (hresponse : ∀ z : rows,
      A ≤ ‖∑ J : monomials, c J * idealRowHom z.val J.val‖ ^ 2)
    (hcoeff : ∑ J : monomials, ‖c J‖ ^ 2 ≤ C)
    (hnonzero : ∀ T ∈ merged, T ≠ ⊥)
    (hnorm : ∀ T ∈ merged, (Ideal.absNorm T : ℝ) ≤ X) :
    selectedNorm rows sources ≤
      C * idealDivisorConstant ε hε * X ^ ε * selectedNorm rows merged / A := by
  have hfiber (T : Ideal O) (hT : T ∈ merged) :
      (((sources ×ˢ monomials).filter fun p => p.1 * p.2 = T).card : ℝ) ≤
        idealDivisorConstant ε hε * X ^ ε :=
    idealProduct_fiber_small_power sources monomials T (hnonzero T hT)
      ε hε X (hnorm T hT)
  have hD : 0 ≤ idealDivisorConstant ε hε * X ^ ε :=
    mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg hX ε)
  have h := selectedNorm_inverse_amplification rows sources monomials merged
    hclosed c A C (idealDivisorConstant ε hε * X ^ ε) hA hC hD hresponse hcoeff hfiber
  simpa only [mul_assoc] using h

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.idealProduct_fiber_card_le_divisors
#print axioms Qrh.JointDetector.selectedNorm_inverse_amplification_small_power
