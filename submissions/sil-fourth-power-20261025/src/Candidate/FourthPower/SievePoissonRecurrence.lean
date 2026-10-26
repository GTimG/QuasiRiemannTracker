/- Copyright (c) 2026 Sil. Apache-2.0.
Return the full Poisson estimate to the literal coprime operator norm.
The completed growth inequality is the displayed exponent-induction input.
-/
import Candidate.FourthPower.SievePoissonSeries

set_option autoImplicit false
namespace Candidate.FourthPower.SievePoissonRecurrence
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss
open CanonicalQuadraticSieve EisensteinSchwartzPoisson
open SexticSieve SievePairPoisson SievePoissonBound SieveDualGeometry
open SieveSmoothed SievePoissonSeries SieveGrowthAlgebra
local notation "Id" => Ideal ActualEisensteinCubic.O
local notation "O" => ActualEisensteinCubic.O

theorem dualFamily_reverse {n : Type*} [Fintype n] (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (a b : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (x : O) :
    dualFamily cols hc a b W M x = ∑ i, ∑ k, if IsCoprime (cols i) (cols k) then
      dualTerm (cols i) (cols k) (hc i) (hc k) (b i) (a k) W M x else 0 := by
  unfold dualFamily
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : IsCoprime (cols i) (cols k)
  · simp only [h,h.symm,ite_true]
  · have h' : ¬IsCoprime (cols k) (cols i) := fun hh => h hh.symm
    simp only [h,h',ite_false]

def profile (ε α C A : ℝ) (W : 𝓢(ℝ, ℂ)) (M N : ℝ) : ℝ :=
  M*(‖paperRadialFourier W 0‖+C*A*N^(12*ε)*M^(-(3*ε))*
    (mainCoefficient N M α+secondaryCoefficient N M))

theorem profile_nonneg (ε α C A : ℝ) (W : 𝓢(ℝ, ℂ)) (M N : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hM : 0 < M) (hN : 0 < N) :
    0 ≤ profile ε α C A W M N := by
  unfold profile mainCoefficient secondaryCoefficient
  positivity

theorem matrix_growth (ε α : ℝ) (hε : 0 < ε) (hεs : ε < 1/6)
    (hα : 1 ≤ α) (hα₂ : α ≤ 2) (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 ≤ A →
      (∀ L B : ℝ, 0 < L → 1 ≤ B → SieveRanges.lambda L B ≤
        A*(L*B)^ε*(L^α+L^(1/6 : ℝ)*B)) →
      ∀ {n : Type*} [Fintype n] (N : ℝ), 1 ≤ N → ∀ (cols : n → Id)
        (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
        (hi : Function.Injective cols) (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N)
        (M : ℝ), 0 < M →
        ‖FiniteSieveOperator.operator (gramMatrix cols W M)‖ ≤ profile ε α C A W M N := by
  obtain ⟨C,hC,hb⟩ := all_series_bound ε α hε hεs hα hα₂ W
  refine ⟨C,hC,?_⟩
  intro A hA hGrowth n _ N hN cols hc hf hi hn M hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  apply operator_norm_le_of_pairing _ _ (profile_nonneg ε α C A W M N hC.le hA hM hN0)
  intro a b
  let E := Real.sqrt ((∑ i, ‖a i‖^2)*(∑ k, ‖b k‖^2))
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have hE2 : E^2 = (∑ i, ‖a i‖^2)*(∑ k, ‖b k‖^2) := Real.sq_sqrt (by positivity)
  obtain ⟨hs,hb'⟩ := hb A hA hGrowth N hN cols hc hf hi hn M hM b a
  rw [show (∑ i, ‖b i‖^2)*(∑ k, ‖a k‖^2) = (∑ i, ‖a i‖^2)*(∑ k, ‖b k‖^2) by ring] at hb'
  have hpoint (j : ℕ) : ‖∑ x : CubicSieve.frequencyDyad j, dualFamily cols hc a b W M x.val‖ ≤
      wholeBand cols hc W M b a j := by
    simp_rw [dualFamily_reverse]
    exact norm_sum_le _ _
  have ht := (tsum_of_norm_bounded hs.hasSum hpoint).trans hb'
  have hz : ‖dualFamily cols hc a b W M 0‖ ≤ ‖paperRadialFourier W 0‖*E := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) hE)).mp
    rw [mul_pow,hE2]
    exact (dualFamily_zero_bound cols hc hf hi a b W M).trans_eq (by ring)
  have hpair : ‖pairing (gramMatrix cols W M) a b‖ ≤ profile ε α C A W M N*E := by
    rw [poisson_frequency_shells cols hc hf a b W M hM,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
    calc
      _ ≤ M*(‖dualFamily cols hc a b W M 0‖+
          ‖∑' j : ℕ, ∑ x : CubicSieve.frequencyDyad j, dualFamily cols hc a b W M x.val‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hM.le
      _ ≤ M*(‖paperRadialFourier W 0‖*E+
          C*A*N^(12*ε)*M^(-(3*ε))*(mainCoefficient N M α+secondaryCoefficient N M)*E) :=
        mul_le_mul_of_nonneg_left (add_le_add hz ht) hM.le
      _ = _ := by unfold profile; ring
  have hh := pow_le_pow_left₀ (norm_nonneg _) hpair 2
  rw [mul_pow,hE2] at hh
  exact hh.trans_eq (by ring)

theorem coprime_growth (ε α : ℝ) (hε : 0 < ε) (hεs : ε < 1/6)
    (hα : 1 ≤ α) (hα₂ : α ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 ≤ A →
      (∀ L B : ℝ, 0 < L → 1 ≤ B → SieveRanges.lambda L B ≤
        A*(L*B)^ε*(L^α+L^(1/6 : ℝ)*B)) →
      ∀ M N : ℝ, 0 < M → 1 ≤ N →
        coprimeNorm M N ≤ profile ε α C A SecondPassArithmetic.rowMajorant M N := by
  obtain ⟨C,hC,hb⟩ := matrix_growth ε α hε hεs hα hα₂ SecondPassArithmetic.rowMajorant
  refine ⟨C,hC,?_⟩
  intro A hA hGrowth M N hM hN
  exact hb A hA hGrowth N hN (fun I : SieveRanges.freeRange N => I.val)
    (fun I => (SieveRanges.mem_freeRange.mp I.property).1)
    (fun I => (SieveRanges.mem_freeRange.mp I.property).2.1)
    Subtype.val_injective (fun I => (SieveRanges.mem_freeRange.mp I.property).2.2) M hM

def shape (α M N : ℝ) : ℝ :=
  M^(1-α)*N^(2*α-1)+M^(5/6 : ℝ)*N^(1/3 : ℝ)

def estimate (ε α A M N : ℝ) : ℝ := M+A*N^(12*ε)*M^(-(3*ε))*shape α M N

theorem coefficients_four (α M N : ℝ) (hα₂ : α ≤ 2) (hM : 0 < M) (hN : 0 < N) :
    M*(mainCoefficient N M α+secondaryCoefficient N M) ≤ 4*shape α M N := by
  have he := coefficients_exact N M α hN hM
  have ha : (2 : ℝ)^α ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα₂
    norm_num at h ⊢
    exact h
  have hb : (2 : ℝ)^(1/6 : ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1/6 : ℝ) ≤ 1)
    simpa only [Real.rpow_one] using h
  rw [mul_add,he.1,he.2]
  unfold shape
  have h₁ := mul_le_mul_of_nonneg_right ha (show 0 ≤ M^(1-α)*N^(2*α-1) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2))
    (show 0 ≤ M^(5/6 : ℝ)*N^(1/3 : ℝ) by positivity)
  nlinarith

theorem coprime_simple (ε α : ℝ) (hε : 0 < ε) (hεs : ε < 1/6)
    (hα : 1 ≤ α) (hα₂ : α ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 ≤ A →
      (∀ L B : ℝ, 0 < L → 1 ≤ B → SieveRanges.lambda L B ≤
        A*(L*B)^ε*(L^α+L^(1/6 : ℝ)*B)) →
      ∀ M N : ℝ, 0 < M → 1 ≤ N → coprimeNorm M N ≤ C*estimate ε α A M N := by
  obtain ⟨C,hC,hb⟩ := coprime_growth ε α hε hεs hα hα₂
  let F := ‖paperRadialFourier SecondPassArithmetic.rowMajorant 0‖
  have hF : 0 ≤ F := norm_nonneg _
  let K := F+4*C+1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro A hA hGrowth M N hM hN
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hs : 0 ≤ shape α M N := by unfold shape; positivity
  have hB : 0 ≤ A*N^(12*ε)*M^(-(3*ε)) := by positivity
  apply (hb A hA hGrowth M N hM hN).trans
  calc
    _ = F*M+C*(A*N^(12*ε)*M^(-(3*ε)))*
        (M*(mainCoefficient N M α+secondaryCoefficient N M)) := by unfold profile; ring
    _ ≤ F*M+C*(A*N^(12*ε)*M^(-(3*ε)))*(4*shape α M N) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (coefficients_four α M N hα₂ hM hN0)
        (mul_nonneg hC.le hB))
    _ ≤ K*estimate ε α A M N := by
      have h₁ := mul_le_mul_of_nonneg_right (show F ≤ K by dsimp only [K]; linarith) hM.le
      have h₂ := mul_le_mul_of_nonneg_right (show 4*C ≤ K by dsimp only [K]; linarith)
        (mul_nonneg hB hs)
      unfold estimate
      nlinarith

theorem estimate_descendant (ε α A M N e d : ℝ) (hε : 0 < ε) (hα : 1 ≤ α)
    (hA : 0 ≤ A) (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d) :
    estimate ε α A (M/e) (N/d) ≤ estimate ε α A M N := by
  have he0 : 0 < e := zero_lt_one.trans_le he
  have hd0 : 0 < d := he0.trans_le hed
  have hloss := CubicDyadicDecay.monomial_descendant_le M N e d (-(3*ε)) (12*ε)
    hM hN he hed (by positivity) (by linarith)
  have hmain := CubicDyadicDecay.monomial_descendant_le M N e d (1-α) (2*α-1)
    hM hN he hed (by linarith) (by linarith)
  have hsecondary := CubicDyadicDecay.monomial_descendant_le M N e d (5/6) (1/3)
    hM hN he hed (by norm_num) (by norm_num)
  have hshape : shape α (M/e) (N/d) ≤ shape α M N := add_le_add hmain hsecondary
  have hshape0 : 0 ≤ shape α (M/e) (N/d) := by unfold shape; positivity
  unfold estimate
  apply add_le_add (div_le_self hM.le he)
  have hh := mul_le_mul
    (mul_le_mul_of_nonneg_left hloss hA) hshape hshape0
    (show 0 ≤ A*(M^(-(3*ε))*N^(12*ε)) by positivity)
  convert hh using 1 <;> ring

/-- The full recurrence for the completed norm. The coprime descent is
valid even when its row length is below one, since the preceding Poisson
estimate was proved for every positive row length. -/
theorem lambda_recurrence (ε α : ℝ) (hε : 0 < ε) (hεs : ε < 1/6)
    (hα : 1 ≤ α) (hα₂ : α ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 ≤ A →
      (∀ L B : ℝ, 0 < L → 1 ≤ B → SieveRanges.lambda L B ≤
        A*(L*B)^ε*(L^α+L^(1/6 : ℝ)*B)) →
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
        SieveRanges.lambda M N ≤ C*N^ε*estimate ε α A M N := by
  obtain ⟨C,hC,hb⟩ := coprime_simple ε α hε hεs hα hα₂
  obtain ⟨D,hD,hd⟩ := SieveGcdNorm.lambda_gcd_descent ε hε
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro A hA hGrowth M N hM hN
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  obtain ⟨e,d,he,hed,hdN,hatt⟩ := SieveGcdNorm.envelope_attained M N hN
  have he0 : 0 < e := zero_lt_one.trans_le he
  have hd0 : 0 < d := he0.trans_le hed
  have hND : 1 ≤ N/d := (one_le_div hd0).mpr hdN
  have hb' := hb A hA hGrowth (M/e) (N/d) (by positivity) hND
  calc
    _ ≤ D*N^ε*SieveGcdNorm.envelope M N := hd M N hM hN
    _ = D*N^ε*coprimeNorm (M/e) (N/d) := by rw [hatt]
    _ ≤ D*N^ε*(C*estimate ε α A (M/e) (N/d)) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ ≤ D*N^ε*(C*estimate ε α A M N) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (estimate_descendant ε α A M N e d hε hα hA hM0 hN0 he hed) hC.le) (by positivity)
    _ = _ := by ring

end
end Candidate.FourthPower.SievePoissonRecurrence
