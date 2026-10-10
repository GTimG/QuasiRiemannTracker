import OAI.NumberTheory.DirichletL.Detector.Local
import OAI.NumberTheory.DirichletL.Detector.Euler
import OAI.NumberTheory.DirichletL.Detector.HighRowsClosed
import Mathlib.Tactic

/-! Exact finite coefficient expansions of the original local numerator factors.

The local variable is `T = Q^(-w)`.  All coefficients below are independent of `T`.
We use finite lists of terms, so no cancellation is lost by replacing a polynomial by
its values on a vertical line.  These lemmas refer directly to the original continued
correction and compensated replacement.
-/

noncomputable section
open scoped BigOperators
namespace Cycle25.Weighted.Numerator
open OAI.SevenEighths ProbeLocal ProbeEuler

def affine (a b T : ℂ) : ℂ := a + b * T
def quadratic (a b c T : ℂ) : ℂ := a + b * T + c * T ^ 2
def cubic (a b c d T : ℂ) : ℂ := a + b * T + c * T ^ 2 + d * T ^ 3

/-- The two coefficients of the marked defect after the original unramified
cancellation. -/
def markedDefectConstant (R V qInv D : ℂ) : ℂ :=
  (R * (1 - qInv) / (1 - V) - D * R) / (1 - R)
def markedDefectLinear (R V chi K : ℂ) : ℂ :=
  (chi * R - K * V / (1 - V)) / (1 - R)

theorem marked_defect_affine (R V qInv D chi K T : ℂ)
    (hR : 1 - R ≠ 0) (hV : 1 - V ≠ 0) :
    markedFactor R V qInv (K * T) (-D + chi * T * R) 1 + D =
      affine (markedDefectConstant R V qInv D) (markedDefectLinear R V chi K) T := by
  unfold markedFactor affine markedDefectConstant markedDefectLinear
  simp only [pow_one]
  field_simp
  ring

def correctionDefectConstant (V D E₀ : ℂ) : ℂ :=
  (D * V + (1 - V) * E₀) / (1 - D)
def correctionDefectLinear (V D chi E₀ E₁ : ℂ) : ℂ :=
  (D * chi * (1 - V) - V * chi + (1 - V) * (E₁ - chi * E₀)) / (1 - D)
def correctionDefectQuadratic (V D chi E₁ : ℂ) : ℂ :=
  (-(1 - V) * chi * E₁) / (1 - D)

theorem correction_defect_quadratic (V D chi E₀ E₁ T : ℂ) (hD : 1 - D ≠ 0) :
    continuedCorrection V (chi * T) D (affine E₀ E₁ T - D) - 1 =
      quadratic (correctionDefectConstant V D E₀)
        (correctionDefectLinear V D chi E₀ E₁)
        (correctionDefectQuadratic V D chi E₁) T := by
  unfold continuedCorrection affine quadratic correctionDefectConstant
    correctionDefectLinear correctionDefectQuadratic
  field_simp
  ring

/-- Coefficients of the error bracket after the exact normalized cancellation. -/
def errorBracketConstant (V D B nu E₀ : ℂ) : ℂ :=
  nu * (V / (1 - V) - D) + (B + nu) * E₀
def errorBracketLinear (V D B nu E₀ E₁ : ℂ) : ℂ :=
  -(V / (1 - V) - D) + (B + nu) * E₁ - E₀
def errorBracketQuadratic (E₁ : ℂ) : ℂ := -E₁

theorem compensated_error_cubic (V D chi B nu E₀ E₁ T : ℂ)
    (hV : 1 - V ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = nu) (hchi : nu * chi = 1) :
    compensatedReplacement V (chi * T) D (affine E₀ E₁ T - D) B T +
      continuedCorrection V (chi * T) D (affine E₀ E₁ T - D) * nu =
    let c := (1 - V) / (1 - D)
    let a := errorBracketConstant V D B nu E₀
    let b := errorBracketLinear V D B nu E₀ E₁
    let d := errorBracketQuadratic E₁
    cubic (c * a) (c * (b - chi * a)) (c * (d - chi * b))
      (-c * chi * d) T := by
  have hvW : nu * (chi * T) = T := by rw [← mul_assoc, hchi, one_mul]
  rw [continued_normalized_cancellation _ _ _ _ _ _ _ hV hD hBD hvW]
  dsimp only
  unfold affine cubic errorBracketConstant errorBracketLinear errorBracketQuadratic
  ring

/-- The ramified replacement is quadratic, including its strict term. -/
theorem ramified_error_quadratic (V B A C T : ℂ) :
    compensatedReplacement V 0 0 (affine A C T) B T =
      quadratic (B * (1 - V) * A)
        (B * (1 - V) * C - 1 - (1 - V) * A)
        (-(1 - V) * C) T := by
  simp only [compensatedReplacement, affine, quadratic, mul_zero, sub_zero,
    mul_one, div_one]
  ring

theorem norm_affine_le (a b T : ℂ) :
    ‖affine a b T‖ ≤ ‖a‖ + ‖b‖ * ‖T‖ := by
  simpa only [affine, norm_mul] using norm_add_le a (b * T)

theorem norm_quadratic_le (a b c T : ℂ) :
    ‖quadratic a b c T‖ ≤ ‖a‖ + ‖b‖ * ‖T‖ + ‖c‖ * ‖T‖ ^ 2 := by
  calc
    _ ≤ ‖a + b * T‖ + ‖c * T ^ 2‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, norm_pow]
      exact add_le_add (norm_affine_le a b T) le_rfl

theorem norm_cubic_le (a b c d T : ℂ) :
    ‖cubic a b c d T‖ ≤
      ‖a‖ + ‖b‖ * ‖T‖ + ‖c‖ * ‖T‖ ^ 2 + ‖d‖ * ‖T‖ ^ 3 := by
  calc
    _ ≤ ‖a + b * T + c * T ^ 2‖ + ‖d * T ^ 3‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, norm_pow]
      exact add_le_add (norm_quadratic_le a b c T) le_rfl

section ActualMarkedRow
open OAI.ActualEisensteinCubic OAI.CompletedGauss
open OAI.ConcretePrimeRowBridge OAI.SevenEighths.ProbePrimePower
local notation "O" => OAI.ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p})

/-- Every original marked term has exactly the declared degree in `Q^(-w)`. -/
theorem rowMarkedTerm_monomial (eta a X W V rho : ℂ) (j e l k m : ℕ) :
    rowMarkedTerm p hp hg eta a X W V rho j e l k m =
      rowMarkedTerm p hp hg eta a X 1 V rho j e l k m * W ^ k := by
  unfold rowMarkedTerm
  split_ifs
  · simp
  · unfold rowWeightedScalar weightedScalar
    simp only [one_pow, mul_one]
    ring

/-- The closed marked factor is genuinely affine in the Mellin local variable,
including ramified rows.  This derives the degree bound from the original Gauss
sum definition, rather than imposing it as a hypothesis. -/
theorem rowClosedMarked_affine (eta a X W V rho : ℂ) (j : ℕ) :
    rowClosedMarked p hp hg eta a X W V rho j =
      rowClosedMarked p hp hg eta a X 0 V rho j +
        (rowClosedMarked p hp hg eta a X 1 V rho j -
          rowClosedMarked p hp hg eta a X 0 V rho j) * W := by
  unfold rowClosedMarked rowBaseFinite
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  norm_num only [rowMarkedTerm, Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff,
    if_false, rowWeightedScalar, weightedScalar, pow_zero, pow_one,
    zero_pow, one_pow, mul_one, one_mul, mul_zero, zero_mul, zero_add, add_zero]
  ring

end ActualMarkedRow
end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
