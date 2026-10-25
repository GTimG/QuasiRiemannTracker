/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from OpenAI baseline QuadraticSieve.InitialBound. Its general
smoothing and Gram bookkeeping are reused with the actually proved sextic
off-diagonal estimate; no squarefree column assumption is imported. -/
import Candidate.Feedback.FourthPower.SieveInitial

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.SieveInitialEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open EisensteinSchwartzPoisson QuadraticInitialBound SexticSieve SieveInitial
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem pair_summable (I J : Id) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => (star (idealRowHom z I) * idealRowHom z J) *
      W (‖eisEmbedding z‖^2/M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hW
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (idealRowHom_norm z I) (idealRowHom_norm z J)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem gram_diagonal (I : Id) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, (star (idealRowHom z I) * idealRowHom z I) * W (‖eisEmbedding z‖^2/M)‖ ≤
      diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  have hs := (pair_summable I I W M hMp).norm
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ?_ hW).trans
    (radial_weight_lattice_bound W M hM))
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (idealRowHom_norm z I) (idealRowHom_norm z I)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

private theorem norm_sq_finite_sum {β : Type*} (C : Finset β) (a r : β → ℂ) :
    (↑(‖∑ n ∈ C, a n * r n‖ ^ 2) : ℂ) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) * (star (r n) * r m) := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, starRingEnd_apply]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem mean_summable (C : Finset Id) (a : Id → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => W (‖eisEmbedding z‖^2/M) *
      (↑(‖∑ n ∈ C, a n * idealRowHom z n‖^2) : ℂ)) := by
  have hs := summable_sum (s := C) (fun n hn => summable_sum (s := C) (fun m hm =>
    (pair_summable n m W M hM).mul_left (star (a n) * a m)))
  apply hs.congr
  intro z
  rw [norm_sq_finite_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem mean_expand (C : Finset Id) (a : Id → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, W (‖eisEmbedding z‖^2/M) * (↑(‖∑ n ∈ C, a n * idealRowHom z n‖^2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) *
        ∑' z : O, (star (idealRowHom z n) * idealRowHom z m) * W (‖eisEmbedding z‖^2/M) := by
  let f : Id → Id → O → ℂ := fun n m z => (star (a n) * a m) *
    ((star (idealRowHom z n) * idealRowHom z m) *
      W (‖eisEmbedding z‖ ^ 2 / M))
  have hf (n m : Id) : Summable (f n m) :=
    (pair_summable n m W M hM).mul_left _
  have heq (z : O) : W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * idealRowHom z n‖ ^ 2) : ℂ) =
        ∑ n ∈ C, ∑ m ∈ C, f n m z := by
    rw [norm_sq_finite_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [f]
    ring
  rw [tsum_congr heq, Summable.tsum_finsetSum (fun n hn => summable_sum (fun m hm => hf n m))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Summable.tsum_finsetSum (fun m hm => hf n m)]
  apply Finset.sum_congr rfl
  intro m hm
  exact tsum_mul_left

theorem initial_mean_bound (C : Finset Id)
    (hc : ∀ I ∈ C, Supported I ∧ PowerFree 6 I)
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ I ∈ C, (Ideal.absNorm I : ℝ) ≤ N)
    (a : Id → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, W (‖eisEmbedding z‖^2/M) * (↑(‖∑ n ∈ C, a n * idealRowHom z n‖^2) : ℂ)‖ ≤
      (diagonalControl W*M + pvControl W*N*C.card) * ∑ n ∈ C, ‖a n‖^2 := by
  have hMp : 0 < M := by linarith
  let D := diagonalControl W * M
  let B := pvControl W * N
  have hB : 0 ≤ B := mul_nonneg (pvControl_nonneg W) hN
  let K : Id → Id → ℂ := fun n m => ∑' z : O,
    (star (idealRowHom z n) * idealRowHom z m) *
      W (‖eisEmbedding z‖ ^ 2 / M)
  have hK (n : Id) (hn : n ∈ C) (m : Id) (hm : m ∈ C) :
      ‖K n m‖ ≤ (if n = m then D else 0) + B := by
    by_cases hnm : n = m
    · subst m
      simp only [ite_true]
      exact (gram_diagonal n W M hM).trans (le_add_of_nonneg_right hB)
    · simp only [hnm, ite_false, zero_add]
      have hb := gram_offdiagonal m n (hc m hm).1 (hc n hn).1
        (hc m hm).2 (hc n hn).2 (Ne.symm hnm) N hN (hNorm m hm) (hNorm n hn) W M hMp
      simpa only [K, mul_comm (star (idealRowHom _ n)) (idealRowHom _ m)] using hb
  have heq (n : Id) (hn : n ∈ C) :
      (∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
        D * ‖a n‖ ^ 2 + B * ‖a n‖ * ∑ m ∈ C, ‖a m‖ := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq,  hn, ite_true]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hcalc : (∑ n ∈ C, ∑ m ∈ C,
      ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
      D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := by
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [mean_expand C a W M hMp]
  calc
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖(star (a n) * a m) * K n m‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hK n hn m hm) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := hcalc
    _ ≤ D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * ((C.card : ℝ) * ∑ n ∈ C, ‖a n‖ ^ 2) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hB
      simpa only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, mul_comm] using
        Finset.sum_mul_sq_le_sq_mul_sq C (fun n => ‖a n‖) (fun _ => (1 : ℝ))
    _ = _ := by dsimp [D, B]; ring

theorem initial_finite_bound (C : Finset Id)
    (hc : ∀ I ∈ C, Supported I ∧ PowerFree 6 I)
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ I ∈ C, (Ideal.absNorm I : ℝ) ≤ N)
    (a : Id → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖^2 ≤ M) :
    (∑ z ∈ R, ‖∑ n ∈ C, a n * idealRowHom z n‖^2) ≤
      (diagonalControl sieveCutoff*M + pvControl sieveCutoff*N*C.card) * ∑ n ∈ C, ‖a n‖^2 := by
  have hMp : 0 < M := by linarith
  let E : O → ℝ := fun z => ‖∑ n ∈ C, a n * idealRowHom z n‖ ^ 2
  let F : O → ℝ := fun z => sieveBump (‖eisEmbedding z‖ ^ 2 / M) * E z
  let H : O → ℂ := fun z => sieveCutoff (‖eisEmbedding z‖ ^ 2 / M) * (E z : ℂ)
  have hF (z : O) : 0 ≤ F z := mul_nonneg sieveBump.nonneg (sq_nonneg _)
  have hH (z : O) : H z = (F z : ℂ) := by
    simp only [H, F, sieveCutoff_apply, Complex.ofReal_mul]
  have hHs : Summable H := mean_summable C a sieveCutoff M hMp
  have hFs : Summable F := hHs.norm.congr (fun z => by
    rw [hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF z)])
  have hsum : ‖∑' z : O, H z‖ = ∑' z : O, F z := by
    rw [tsum_congr hH, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg hF)]
  calc
    _ = ∑ z ∈ R, F z := by
      apply Finset.sum_congr rfl
      intro z hz
      have ht0 : 0 ≤ ‖eisEmbedding z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
      have ht1 : ‖eisEmbedding z‖ ^ 2 / M ≤ 1 := (div_le_one hMp).mpr (hR z hz)
      simp only [F, sieveBump_eq_one ht0 ht1, one_mul, E]
    _ ≤ ∑' z : O, F z := hFs.sum_le_tsum R (fun z _ => hF z)
    _ = ‖∑' z : O, H z‖ := hsum.symm
    _ ≤ _ := initial_mean_bound C hc N hN hNorm
      a sieveCutoff M hM

theorem initial_element_bound (C : Finset Id)
    (hc : ∀ I ∈ C, Supported I ∧ PowerFree 6 I)
    (N : ℝ) (hN : 1 ≤ N) (hNorm : ∀ I ∈ C, (Ideal.absNorm I : ℝ) ≤ N)
    (a : Id → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖^2 ≤ M) :
    (∑ z ∈ R, ‖∑ I ∈ C, a I * idealRowHom z I‖^2) ≤
      initialSieveConstant * (M+N^2) * coefficientMass C a := by
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hb := initial_finite_bound C hc N hN0 hNorm a M hM R hR
  have hsub : C ⊆ idealsUpTo ⌊N⌋₊ := by
    intro I hI
    apply mem_idealsUpTo.mpr
    refine ⟨Nat.one_le_iff_ne_zero.mpr ?_, Nat.le_floor (hNorm I hI)⟩
    exact Ideal.absNorm_eq_zero_iff.not.mpr (hc I hI).1.1
  have hcardNat : C.card ≤ 64 * (⌊N⌋₊+1) :=
    (Finset.card_le_card hsub).trans (CompactScaleBridge.idealsUpTo_card_le _)
  have hcard : (C.card : ℝ) ≤ 128*N := by
    have hh : (C.card : ℝ) ≤ 64*((⌊N⌋₊ : ℝ)+1) := by exact_mod_cast hcardNat
    have hfloor := Nat.floor_le hN0
    linarith
  apply hb.trans (mul_le_mul_of_nonneg_right _ (coefficientMass_nonneg C a))
  have hdiag := diagonalControl_nonneg sieveCutoff
  have hpv := pvControl_nonneg sieveCutoff
  have hmul := mul_le_mul_of_nonneg_left hcard (mul_nonneg hpv hN0)
  unfold initialSieveConstant
  nlinarith [mul_nonneg hdiag (sq_nonneg N), mul_nonneg hpv (zero_le_one.trans hM)]

/-- The initial bound is unconditional for all supported rows. Only the
columns must be sixth-power-free; this is the input for exponent iteration. -/
theorem initial_ideal_bound (rows columns : Finset Id)
    (hr : ∀ R ∈ rows, Supported R)
    (hc : ∀ I ∈ columns, Supported I ∧ PowerFree 6 I)
    (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hR : ∀ R ∈ rows, (Ideal.absNorm R : ℝ) ≤ M)
    (hC : ∀ I ∈ columns, (Ideal.absNorm I : ℝ) ≤ N) (a : Id → ℂ) :
    energy rows columns a ≤ initialSieveConstant * (M+N^2) * coefficientMass columns a := by
  have hinj : Set.InjOn primaryGenerator (rows : Set Id) := by
    intro I hI J hJ he
    calc
      I = Ideal.span {primaryGenerator I} :=
        (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I (hr I hI))).1.symm
      _ = Ideal.span {primaryGenerator J} := by rw [he]
      _ = J := (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J (hr J hJ))).1
  have hrows : ∀ z ∈ rows.image primaryGenerator, ‖eisEmbedding z‖^2 ≤ M := by
    intro z hz
    obtain ⟨R,hRs,rfl⟩ := Finset.mem_image.mp hz
    rw [primaryGenerator_norm_sq R (supported_primaryGenerator_ne_zero R (hr R hRs))]
    exact hR R hRs
  have he := initial_element_bound columns hc N hN hC a M hM (rows.image primaryGenerator) hrows
  rw [Finset.sum_image (fun I hI J hJ hij => hinj hI hJ hij)] at he
  exact he

end
end Candidate.Feedback.FourthPower.SieveInitialEnergy
