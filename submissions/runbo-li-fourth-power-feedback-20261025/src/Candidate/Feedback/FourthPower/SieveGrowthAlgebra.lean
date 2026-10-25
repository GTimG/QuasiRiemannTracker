/- Copyright (c) 2026 Sil. Apache-2.0.
Explicit numerical propagation of a completed-sieve growth bound.
The input inequalities are intermediate induction hypotheses; no instance,
axiom, or claim of an optimal sieve bound is introduced here.
-/
import Candidate.Feedback.FourthPower.SieveBandBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CubicDyadicDecay

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.SieveGrowthAlgebra
noncomputable section
open scoped BigOperators
open OAI OAI.SevenEighths
open SieveBandBound

def mainCoefficient (N M α : ℝ) : ℝ := (2*N/M)^α*N^(α-1)
def secondaryCoefficient (N M : ℝ) : ℝ := 2*(2*N/M)^(1/6 : ℝ)*N^(1/6 : ℝ)
def numerator (N M α y : ℝ) : ℝ :=
  mainCoefficient N M α*y^α+secondaryCoefficient N M*y^(1/6 : ℝ)

theorem density_growth (ε : ℝ) (hε : 0 < ε) (C A P L α : ℝ)
    (hC : 0 ≤ C) (hP : 0 < P) (hL : 0 < L)
    (hlambda : SieveRanges.lambda L (2*P) ≤ A*(L*(2*P))^ε*(L^α+L^(1/6 : ℝ)*(2*P))) :
    density ε hε C P L ≤
      C*A*IdealCoprimeSieveOperator.supportConstant ε hε*(L*(2*P))^(2*ε)*
        (L^α/P+2*L^(1/6 : ℝ)) := by
  have hs := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlambda
      (show 0 ≤ C*L^ε by positivity))
      (show 0 ≤ IdealCoprimeSieveOperator.supportConstant ε hε*(2*P)^ε by positivity)) hP.le
  change density ε hε C P L ≤ _ at hb
  apply hb.trans_eq
  rw [show 2*ε=ε+ε by ring,Real.rpow_add (by positivity : 0 < L*(2*P)),
    Real.mul_rpow hL.le (by positivity : 0 ≤ 2*P)]
  field_simp
  <;> ring

theorem scaled_monomials (N M P y α : ℝ) (hN : 0 < N) (hM : 0 < M)
    (hP : 0 < P) (hy : 0 < y) :
    ((2*N/M)*P*y)^α/P+2*((2*N/M)*P*y)^(1/6 : ℝ) =
      (2*N/M)^α*P^(α-1)*y^α + 2*(2*N/M)^(1/6 : ℝ)*P^(1/6 : ℝ)*y^(1/6 : ℝ) := by
  rw [Real.mul_rpow (by positivity : 0 ≤ (2*N/M)*P) hy.le,
    Real.mul_rpow (by positivity : 0 ≤ 2*N/M) hP.le,
    Real.mul_rpow (by positivity : 0 ≤ (2*N/M)*P) hy.le,
    Real.mul_rpow (by positivity : 0 ≤ 2*N/M) hP.le,
    Real.rpow_sub hP,Real.rpow_one]
  ring

theorem monomials_le (N M P y α : ℝ) (hN : 0 < N) (hM : 0 < M)
    (hP : 0 < P) (hPN : P ≤ N) (hy : 0 < y) (hα : 1 ≤ α) :
    ((2*N/M)*P*y)^α/P+2*((2*N/M)*P*y)^(1/6 : ℝ) ≤ numerator N M α y := by
  rw [scaled_monomials N M P y α hN hM hP hy]
  unfold numerator mainCoefficient secondaryCoefficient
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hP.le hPN (sub_nonneg.mpr hα)) (by positivity))
      (by positivity)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hP.le hPN (by norm_num : (0 : ℝ) ≤ 1/6))
        (by positivity)) (by positivity)

theorem density_scaled (ε : ℝ) (hε : 0 < ε) (C A N M X P Q α : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hN : 0 < N) (hM : 0 < M) (hX : 0 < X)
    (hP : 1 ≤ P) (hPN : P ≤ N) (hQ : 1 ≤ Q) (hα : 1 ≤ α)
    (hlambda : SieveRanges.lambda (N*X/Q) (2*P) ≤
      A*((N*X/Q)*(2*P))^ε*((N*X/Q)^α+(N*X/Q)^(1/6 : ℝ)*(2*P))) :
    density ε hε C P (N*X/Q) ≤
      C*A*IdealCoprimeSieveOperator.supportConstant ε hε*(2*N^2*X)^(2*ε)*
        numerator N M α (M*X/(2*P*Q)) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hL : 0 < N*X/Q := by positivity
  have hs := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
  have hb := density_growth ε hε C A P (N*X/Q) α hC hP0 hL hlambda
  have hlen : (N*X/Q)*(2*P) ≤ 2*N^2*X := by
    have hh := mul_le_mul (div_le_self (by positivity : 0 ≤ N*X) hQ)
      (mul_le_mul_of_nonneg_left hPN (by norm_num : (0 : ℝ) ≤ 2)) (by positivity)
      (by positivity : 0 ≤ N*X)
    exact hh.trans_eq (by ring)
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ (N*X/Q)*(2*P)) hlen
    (by positivity : 0 ≤ 2*ε)
  have he : N*X/Q = (2*N/M)*P*(M*X/(2*P*Q)) := by field_simp
  have hm : (N*X/Q)^α/P+2*(N*X/Q)^(1/6 : ℝ) ≤ numerator N M α (M*X/(2*P*Q)) := by
    rw [he]
    exact monomials_le N M P _ α hN hM hP0 hPN (by positivity) hα
  apply hb.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hr (by positivity)) hm (by positivity) (by positivity)

theorem sqrt_density_scaled (ε : ℝ) (hε : 0 < ε) (C A N M X P Q α : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hN : 0 < N) (hM : 0 < M) (hX : 0 < X)
    (hP : 1 ≤ P) (hPN : P ≤ N) (hQ : 1 ≤ Q) (hQN : Q ≤ N) (hα : 1 ≤ α)
    (hlambda₁ : SieveRanges.lambda (N*X/Q) (2*P) ≤
      A*((N*X/Q)*(2*P))^ε*((N*X/Q)^α+(N*X/Q)^(1/6 : ℝ)*(2*P)))
    (hlambda₂ : SieveRanges.lambda (N*X/P) (2*Q) ≤
      A*((N*X/P)*(2*Q))^ε*((N*X/P)^α+(N*X/P)^(1/6 : ℝ)*(2*Q))) :
    Real.sqrt (density ε hε C P (N*X/Q)*density ε hε C Q (N*X/P)) ≤
      C*A*IdealCoprimeSieveOperator.supportConstant ε hε*(2*N^2*X)^(2*ε)*
        numerator N M α (M*X/(2*P*Q)) := by
  have hp := density_nonneg ε hε C P (N*X/Q) hC (zero_lt_one.trans_le hP) (by positivity)
  have hq := density_nonneg ε hε C Q (N*X/P) hC (zero_lt_one.trans_le hQ) (by positivity)
  have hs := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
  have hg : 0 ≤ C*A*IdealCoprimeSieveOperator.supportConstant ε hε*(2*N^2*X)^(2*ε)*
      numerator N M α (M*X/(2*P*Q)) := by
    unfold numerator mainCoefficient secondaryCoefficient
    positivity
  have h₁ := density_scaled ε hε C A N M X P Q α hC hA hN hM hX hP hPN hQ hα hlambda₁
  have h₂ := density_scaled ε hε C A N M X Q P α hC hA hN hM hX hQ hQN hP hα hlambda₂
  rw [show 2*Q*P=2*P*Q by ring] at h₂
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hg).mp
  rw [Real.sq_sqrt (mul_nonneg hp hq),pow_two]
  exact mul_le_mul h₁ h₂ hq hg

def dyadicGrowth (ε α t U V : ℝ) (j : ℕ) : ℝ :=
  ((2 : ℝ)^j)^(3*ε) * (U*(t*(2 : ℝ)^j)^α+V*(t*(2 : ℝ)^j)^(1/6 : ℝ)) /
    (1+t*(2 : ℝ)^j)^3

theorem shifted_numerator (ε α t U V X : ℝ) (ht : 0 < t) (hX : 0 < X) :
    X^(3*ε)*(U*(t*X)^α+V*(t*X)^(1/6 : ℝ)) =
      (U*t^α)*X^(α+3*ε)+(V*t^(1/6 : ℝ))*X^(1/6+3*ε) := by
  rw [Real.mul_rpow ht.le hX.le,Real.mul_rpow ht.le hX.le,
    Real.rpow_add hX,Real.rpow_add hX]
  ring

/-- The entire infinite frequency sum, including all logarithmic losses
from the bad-prime labels. This reuses the original baseline's elementary
dyadic decay theorem, with its hypotheses checked at the sextic exponents. -/
theorem dyadic_growth_sum (ε α : ℝ) (hε : 0 < ε) (hεs : ε < 1/6)
    (hα : 1 ≤ α) (hα₂ : α ≤ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ t U V : ℝ, 0 < t → 0 ≤ U → 0 ≤ V →
      Summable (dyadicGrowth ε α t U V) ∧
        (∑' j, dyadicGrowth ε α t U V j) ≤ K*t^(-(3*ε))*(U+V) := by
  have ha : 0 < α+3*ε := by linarith
  have ha3 : α+3*ε < 3 := by linarith
  have hb : 0 < (1/6 : ℝ)+3*ε := by linarith
  have hb3 : (1/6 : ℝ)+3*ε < 3 := by linarith
  let A := CubicDyadicDecay.decayConstant (α+3*ε)
  let B := CubicDyadicDecay.decayConstant ((1/6 : ℝ)+3*ε)
  have hA : 0 < A := CubicDyadicDecay.decayConstant_pos _ ha ha3
  have hB : 0 < B := CubicDyadicDecay.decayConstant_pos _ hb hb3
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro t U V ht hU hV
  let F : ℝ → ℝ := fun X => X^(3*ε)*(U*(t*X)^α+V*(t*X)^(1/6 : ℝ))
  have hs := CubicDyadicDecay.two_power_majorant F 1 (U*t^α) (V*t^(1/6 : ℝ))
    t (α+3*ε) ((1/6 : ℝ)+3*ε) (by norm_num) (by positivity) (by positivity)
    ht ha ha3 hb hb3
    (fun X hX => by dsimp only [F]; positivity)
    (fun X hX => by
      dsimp only [F]
      rw [shifted_numerator ε α t U V X ht (zero_lt_one.trans_le hX),one_mul])
  refine ⟨hs.1,hs.2.trans ?_⟩
  have he₁ : t^α*t^(-(α+3*ε)) = t^(-(3*ε)) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have he₂ : t^(1/6 : ℝ)*t^(-((1/6 : ℝ)+3*ε)) = t^(-(3*ε)) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  change 1*((U*t^α)*A*t^(-(α+3*ε))+(V*t^(1/6 : ℝ))*B*t^(-((1/6 : ℝ)+3*ε))) ≤ _
  calc
    _ = t^(-(3*ε))*(U*A+V*B) := by
      calc
        _ = U*A*(t^α*t^(-(α+3*ε)))+V*B*(t^(1/6 : ℝ)*t^(-((1/6 : ℝ)+3*ε))) := by ring
        _ = _ := by rw [he₁,he₂]; ring
    _ ≤ t^(-(3*ε))*((A+B)*(U+V)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hU hB.le,mul_nonneg hV hA.le]
    _ = _ := by ring

theorem coefficients_exact (N M α : ℝ) (hN : 0 < N) (hM : 0 < M) :
    M*mainCoefficient N M α = (2 : ℝ)^α*M^(1-α)*N^(2*α-1) ∧
    M*secondaryCoefficient N M = 2*(2 : ℝ)^(1/6 : ℝ)*M^(5/6 : ℝ)*N^(1/3 : ℝ) := by
  have hp (a b : ℝ) : M*((2*N/M)^a*N^b) = (2 : ℝ)^a*M^(1-a)*N^(a+b) := by
    rw [Real.div_rpow (by positivity : 0 ≤ 2*N) hM.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hN.le,
      Real.rpow_sub hM,Real.rpow_one,Real.rpow_add hN]
    ring
  constructor
  · simpa only [mainCoefficient,show α+(α-1)=2*α-1 by ring] using hp α (α-1)
  · unfold secondaryCoefficient
    calc
      _ = 2*(M*((2*N/M)^(1/6 : ℝ)*N^(1/6 : ℝ))) := by ring
      _ = _ := by rw [hp]; norm_num; ring

end
end Candidate.Feedback.FourthPower.SieveGrowthAlgebra
