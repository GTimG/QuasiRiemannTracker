/- Copyright (c) 2026 Sil. Apache-2.0.
The two length caps used after natural reflection. This is a consequence of
the actual central sieve; it does not assert that reflection has been attached.
-/
import Candidate.SilPrior.FourthPower.SieveCentralReference

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.SieveReferenceScales
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss
open CanonicalQuadraticSieve
open SieveReference SieveElementReference SieveCentralReference
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem powers_product (Z R v a b : ℝ) (hZ : 0 < Z) :
    (Z^R)^a*(Z^v)^b = Z^(R*a+v*b) := by
  rw [← Real.rpow_mul hZ.le,← Real.rpow_mul hZ.le,← Real.rpow_add hZ]

theorem two_scale_majorant (Z R v y N T : ℝ) (hZ : 1 ≤ Z) (hR : 0 ≤ R)
    (hN : 0 ≤ N) (hT : 0 ≤ T) (hv : v ≤ (4/5)*R) (hy : y ≤ R/2)
    (hmax : N ≤ Z^v) (href : N ≤ Z^y*T) :
    referenceMajorant (Z^R) N ≤ Z^R*(3+T^(1/3 : ℝ)) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hp (a : ℝ) : 0 ≤ (Z^R)^a := Real.rpow_nonneg (Real.rpow_nonneg hZ0.le R) a
  have h₂ : (Z^R)^(1/6 : ℝ)*N ≤ Z^R := by
    calc
      _ ≤ (Z^R)^(1/6 : ℝ)*(Z^v)^1 := by
        rw [Real.rpow_one]
        exact mul_le_mul_of_nonneg_left hmax (hp _)
      _ = Z^(R*(1/6)+v*1) := powers_product Z R v (1/6) 1 hZ0
      _ ≤ Z^R := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h₄ : (Z^R)^(1/3 : ℝ)*N^(5/6 : ℝ) ≤ Z^R := by
    calc
      _ ≤ (Z^R)^(1/3 : ℝ)*(Z^v)^(5/6 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN hmax (by norm_num)) (hp _)
      _ = Z^(R*(1/3)+v*(5/6)) := powers_product Z R v (1/3) (5/6) hZ0
      _ ≤ Z^R := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h₃ : (Z^R)^(5/6 : ℝ)*N^(1/3 : ℝ) ≤ Z^R*T^(1/3 : ℝ) := by
    calc
      _ ≤ (Z^R)^(5/6 : ℝ)*(Z^y*T)^(1/3 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN href (by norm_num)) (hp _)
      _ = Z^(R*(5/6)+y*(1/3))*T^(1/3 : ℝ) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hZ0.le y) hT,← mul_assoc,powers_product Z R y (5/6) (1/3) hZ0]
      _ ≤ Z^R*T^(1/3 : ℝ) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (Real.rpow_nonneg hT _)
  unfold referenceMajorant
  nlinarith

/-- Constants are selected before all row ranges, column ranges and vectors.
The extraction ratio T is retained explicitly in the critical term. -/
theorem two_scale_reference (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z R v y N T A : ℝ,
      1 ≤ Z → 0 ≤ R → 1 ≤ N → 0 ≤ T → 0 ≤ A →
      R+v ≤ L → v ≤ (4/5)*R → y ≤ R/2 → N ≤ Z^v → N ≤ Z^y*T →
      ∀ (rows : Finset O) (columns : Finset Id),
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      (∀ I ∈ columns, Supported I ∧ (Ideal.absNorm I : ℝ) ≤ N) →
      ∀ a : Id → ℂ, (∀ I ∈ columns, ‖a I‖^2 ≤ A/(Ideal.absNorm I : ℝ)) →
        elementEnergy rows columns a ≤ C*Z^(R+ε)*(3+T^(1/3 : ℝ))*A := by
  obtain ⟨C,hC,hb⟩ := central_reference (ε/L) (div_pos hε hL)
  refine ⟨C,hC,?_⟩
  intro Z R v y N T A hZ hR hN hT hA hcap hv hy hmax href rows columns hr hc a ha
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hm := Real.rpow_pos_of_pos hZ0 R
  have hp : ((Z^R)*N)^(ε/L) ≤ Z^ε := by
    calc
      _ ≤ ((Z^R)*(Z^v))^(ε/L) := Real.rpow_le_rpow (mul_nonneg hm.le hN0.le)
        (mul_le_mul_of_nonneg_left hmax hm.le) (div_pos hε hL).le
      _ = Z^((R+v)*(ε/L)) := by rw [← Real.rpow_add hZ0,← Real.rpow_mul hZ0.le]
      _ ≤ Z^ε := Real.rpow_le_rpow_of_exponent_le hZ (by
        have hh := mul_le_mul_of_nonneg_right hcap (div_pos hε hL).le
        have he : L*(ε/L) = ε := mul_div_cancel₀ ε (ne_of_gt hL)
        exact hh.trans_eq he)
  have hmajorant := two_scale_majorant Z R v y N T hZ hR hN0.le hT hv hy hmax href
  have hraw := hb (Z^R) N A (Real.one_le_rpow hZ hR) hN hA rows columns hr hc a ha
  have hnonneg := referenceMajorant_nonneg (Z^R) N hm.le hN0.le
  calc
    _ ≤ C*((Z^R)*N)^(ε/L)*referenceMajorant (Z^R) N*A := hraw
    _ ≤ C*Z^ε*(Z^R*(3+T^(1/3 : ℝ)))*A := mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hmajorant hnonneg (by positivity)) hA
    _ = C*Z^(R+ε)*(3+T^(1/3 : ℝ))*A := by
      rw [Real.rpow_add hZ0]
      ring

theorem square_root_cost (T : ℝ) (hT : 0 ≤ T) :
    3+T^(1/3 : ℝ) ≤ (2+T^(1/6 : ℝ))^2 := by
  have hp : (T^(1/6 : ℝ))^2 = T^(1/3 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hT]
    norm_num
  have hn := Real.rpow_nonneg hT (1/6 : ℝ)
  nlinarith

theorem norm_of_energy_bound {n : Type*} [Fintype n] (f : n → ℂ)
    (C Z R ε T A : ℝ) (hC : 0 ≤ C) (hZ : 0 < Z) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (h : (∑ x, ‖f x‖^2) ≤ C*Z^(R+ε)*(3+T^(1/3 : ℝ))*A) :
    ‖WithLp.toLp 2 f‖ ≤ Real.sqrt C*Z^((R+ε)/2)*(2+T^(1/6 : ℝ))*Real.sqrt A := by
  have hp : (Z^((R+ε)/2))^2 = Z^(R+ε) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hZ.le]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.norm_sq_eq,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hC,Real.sq_sqrt hA,hp]
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (square_root_cost T hT) (by positivity)) hA)

end
end Candidate.SilPrior.FourthPower.SieveReferenceScales
