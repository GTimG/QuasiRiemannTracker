/- Copyright (c) 2026 Sil. Apache-2.0.
Sextic exponent improvement. The scalar iteration follows the pattern of
the baseline's HeathBrownIteration, with the sextic step and fixed point.
-/
import Candidate.SilPrior.FourthPower.SieveExponent

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.SieveImprovement
noncomputable section
open OAI OAI.SevenEighths
open SieveRanges SieveExponent SievePoissonRecurrence

def step (α : ℝ) : ℝ := (12*α-7)/(6*α-1)
def enlargement (α : ℝ) : ℝ := (12*α-8)/(6*α-1)

theorem step_sub (α : ℝ) (hα : (7/6 : ℝ) ≤ α) :
    step α-7/6 = 5*(α-7/6)/(6*α-1) := by
  have hd : 6*α-1 ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  unfold step
  rw [sub_mul,div_mul_cancel₀ _ hd]
  ring

theorem step_gt {α : ℝ} (hα : (7/6 : ℝ) < α) : (7/6 : ℝ) < step α := by
  have h := step_sub α hα.le
  have hd : 0 < 6*α-1 := by linarith
  have he : 0 < α-7/6 := sub_pos.mpr hα
  have hp : 0 < 5*(α-7/6)/(6*α-1) := by positivity
  linarith

theorem step_error_le {α : ℝ} (hα : (7/6 : ℝ) ≤ α) :
    step α-7/6 ≤ (5/6 : ℝ)*(α-7/6) := by
  rw [step_sub α hα]
  apply (div_le_iff₀ (by linarith : 0 < 6*α-1)).mpr
  nlinarith [sq_nonneg (α-7/6)]

theorem step_lt {α : ℝ} (hα : (7/6 : ℝ) < α) : step α < α := by
  have h := step_error_le hα.le
  linarith

theorem enlargement_bounds (α : ℝ) (hα : (7/6 : ℝ) ≤ α) :
    1 ≤ enlargement α ∧ enlargement α ≤ step α := by
  have hd : 0 < 6*α-1 := by linarith
  constructor
  · unfold enlargement
    apply (one_le_div hd).mpr
    linarith
  · unfold enlargement step
    exact div_le_div_of_nonneg_right (by linarith) hd.le

theorem enlargement_cross (α : ℝ) (hα : (7/6 : ℝ) ≤ α) :
    enlargement α*(5/6 : ℝ)+1/3 = step α := by
  have hd : 6*α-1 ≠ 0 := by linarith
  unfold enlargement step
  apply (eq_div_iff hd).mpr
  calc
    _ = ((12*α-8)/(6*α-1)*(6*α-1))*(5/6 : ℝ)+(6*α-1)/3 := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hd]; ring

theorem enlargement_secondary (α : ℝ) (hα : (7/6 : ℝ) ≤ α) :
    enlargement α*(1-α)+(2*α-1) = step α := by
  have hd : 6*α-1 ≠ 0 := by linarith
  unfold enlargement step
  apply (eq_div_iff hd).mpr
  calc
    _ = ((12*α-8)/(6*α-1)*(6*α-1))*(1-α)+(2*α-1)*(6*α-1) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hd]; ring

theorem enlarged_shape (α M N : ℝ) (hα : (7/6 : ℝ) ≤ α) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    let T := max M (N^(enlargement α))
    T+shape α T N ≤ 3*exponentShape (step α) M N := by
  let T := max M (N^(enlargement α))
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have ht : T ≤ M+N^(step α) := by
    apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · exact (Real.rpow_le_rpow_of_exponent_le hN (enlargement_bounds α hα).2).trans
        (le_add_of_nonneg_left hM0.le)
  have hc : T^(5/6 : ℝ)*N^(1/3 : ℝ) ≤ M^(5/6 : ℝ)*N^(1/3 : ℝ)+N^(step α) := by
    by_cases hm : M ≤ N^(enlargement α)
    · dsimp only [T]
      rw [max_eq_right hm,← Real.rpow_mul hN0.le,← Real.rpow_add hN0,enlargement_cross α hα]
      exact le_add_of_nonneg_left (by positivity)
    · dsimp only [T]
      rw [max_eq_left (le_of_not_ge hm)]
      exact le_add_of_nonneg_right (by positivity)
  have hs : T^(1-α)*N^(2*α-1) ≤ N^(step α) := by
    have hp := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 (enlargement α))
      (le_max_right M (N^(enlargement α))) (show 1-α ≤ 0 by linarith)
    calc
      _ ≤ (N^(enlargement α))^(1-α)*N^(2*α-1) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by rw [← Real.rpow_mul hN0.le,← Real.rpow_add hN0,enlargement_secondary α hα]
  change T+shape α T N ≤ _
  unfold shape exponentShape
  have hx : 0 ≤ M^(5/6 : ℝ)*N^(1/3 : ℝ) := by positivity
  linarith

theorem estimate_le (ε α A T N : ℝ) (hε : 0 < ε) (hA : 0 ≤ A) (hT : 1 ≤ T) (hN : 1 ≤ N) :
    estimate ε α A T N ≤ (A+1)*N^(12*ε)*(T+shape α T N) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hp : 1 ≤ N^(12*ε) := Real.one_le_rpow hN (by positivity)
  have hq : T^(-(3*ε)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by linarith)
  have hs : 0 ≤ shape α T N := by unfold shape; positivity
  have ht : T ≤ (A+1)*N^(12*ε)*T :=
    le_mul_of_one_le_left hT0.le (one_le_mul_of_one_le_of_one_le (by linarith) hp)
  have hh : A*N^(12*ε)*T^(-(3*ε)) ≤ (A+1)*N^(12*ε) := by
    calc
      _ ≤ A*N^(12*ε)*1 := mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ _ := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)
  have hb := add_le_add ht (mul_le_mul_of_nonneg_right hh hs)
  exact hb.trans_eq (by ring)

theorem improve (α : ℝ) (h : HasExponent α) (hα : (7/6 : ℝ) < α) (hα₂ : α ≤ 2) :
    HasExponent (step α) := by
  intro δ hδ
  let ε := min (δ/13) (1/12 : ℝ)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεs : ε < 1/6 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεd : 13*ε ≤ δ := by
    have hh : ε ≤ δ/13 := min_le_left _ _
    linarith
  obtain ⟨A,hA,hGrowth⟩ := completed_of_exponent α h hα.le ε hε
  obtain ⟨C,hC,hrec⟩ := lambda_recurrence ε α hε hεs (by linarith) hα₂
  refine ⟨3*C*(A+1),by positivity,?_⟩
  intro M N hM hN
  let T := max M (N^(enlargement α))
  have hT : 1 ≤ T := hM.trans (le_max_left _ _)
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hp : N^(13*ε) ≤ (M*N)^δ :=
    (Real.rpow_le_rpow_of_exponent_le hN hεd).trans
      (Real.rpow_le_rpow hN0.le (by nlinarith) hδ.le)
  have hs : 0 ≤ exponentShape (step α) M N := by unfold exponentShape; positivity
  have he : N^ε*N^(12*ε)=N^(13*ε) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  calc
    theta M N ≤ theta T N := theta_mono (le_max_left _ _) le_rfl
    _ ≤ SieveRanges.lambda T N := theta_le_lambda T N
    _ ≤ C*N^ε*estimate ε α A T N := hrec A hA.le hGrowth T N hT hN
    _ ≤ C*N^ε*((A+1)*N^(12*ε)*(T+shape α T N)) :=
      mul_le_mul_of_nonneg_left (estimate_le ε α A T N hε hA.le hT hN) (by positivity)
    _ = C*(A+1)*N^(13*ε)*(T+shape α T N) := by
      calc
        _ = C*(A+1)*(N^ε*N^(12*ε))*(T+shape α T N) := by ring
        _ = _ := by rw [he]
    _ ≤ C*(A+1)*N^(13*ε)*(3*exponentShape (step α) M N) :=
      mul_le_mul_of_nonneg_left (enlarged_shape α M N hα.le hM hN) (by positivity)
    _ ≤ C*(A+1)*(M*N)^δ*(3*exponentShape (step α) M N) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ = _ := by ring

def exponent : ℕ → ℝ
  | 0 => 2
  | n+1 => step (exponent n)

theorem exponent_bounds (n : ℕ) : (7/6 : ℝ) < exponent n ∧ exponent n ≤ 2 := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih => exact ⟨step_gt ih.1,(step_lt ih.1).le.trans ih.2⟩

theorem exponent_error_le (n : ℕ) : exponent n-7/6 ≤ (5/6 : ℝ)^(n+1) := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    calc
      _ ≤ (5/6 : ℝ)*(exponent n-7/6) := step_error_le (exponent_bounds n).1.le
      _ ≤ (5/6 : ℝ)*(5/6 : ℝ)^(n+1) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem exponent_proved (n : ℕ) : HasExponent (exponent n) := by
  induction n with
  | zero => exact exponent_initial
  | succ n ih => exact improve _ ih (exponent_bounds n).1 (exponent_bounds n).2

theorem arbitrary_close (δ : ℝ) (hδ : 0 < δ) :
    ∃ α : ℝ, (7/6 : ℝ) < α ∧ α ≤ 2 ∧ α < 7/6+δ ∧ HasExponent α := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (5/6 : ℝ) < 1)
  have hp : (5/6 : ℝ)^(n+1) ≤ (5/6 : ℝ)^n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (by norm_num)
  have he := exponent_error_le n
  refine ⟨exponent n,(exponent_bounds n).1,(exponent_bounds n).2,?_,exponent_proved n⟩
  linarith

end
end Candidate.SilPrior.FourthPower.SieveImprovement
