/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.InBallTotal
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.LabelInt
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.TailTotal

/-!
# Inverse.Poisson.InBallSum — the in-ball rows of all labels at once

The in-ball part of `f_decomp`, summed over the labels with the weights `D f · c`, is a sum over
the finite label set `(f, g, E, k)` (`E ⊆ g`, `g` live, `k` and its physical row in the child
ball). `inball_total` (with the per-label bound `label_inner_bound`, the uniform kernel decay
`Cb (1+|t|)^(-(2d+2))` and the label-sum bound `lam_sum_le`) bounds it by an explicit product.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap ENNReal
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.SecondPassArithmetic (rayMonoid conjugateRayMonoid)
open OAI.RayFourExpansion (RayCharacter rayCharacter gCoeff crossCoeff)
open FourierBridge (logPhase)
open IdealMobiusDivisorSum (idealDivisors)

local notation "O" => ActualEisensteinCubic.O

theorem one_le_eis_sq {x : O} (hx : x ≠ 0) : 1 ≤ ‖eisEmbedding x‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  have : Ideal.absNorm (Ideal.span {x}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hx
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

theorem ball_norm (R : ℝ) (y : O) (hy : y ∈ nonzeroChildFrequencyBall 1 R) :
    0 < ‖eisEmbedding y‖ ^ 2 ∧ ‖eisEmbedding y‖ ^ 2 ≤ R := by
  have := (mem_nonzeroChildFrequencyBall 1 one_ne_zero R y).mp hy
  simpa only [one_mul] using this

theorem ball_neg (R : ℝ) (y : O) (hy : y ∈ nonzeroChildFrequencyBall 1 R) :
    -y ∈ nonzeroChildFrequencyBall 1 R := by
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero] at hy ⊢
  simpa only [mul_neg, map_neg, norm_neg] using hy

theorem ball_ne_zero (R : ℝ) (y : O) (hy : y ∈ nonzeroChildFrequencyBall 1 R) : y ≠ 0 := by
  intro h
  have := (ball_norm R y hy).1
  rw [h, map_zero, norm_zero] at this
  norm_num at this

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
theorem k_mem_of_row (f : O) (hf : f ≠ 0) (g E : Finset ι) (hE : E ⊆ g) (R : ℝ) (k : O)
    (hk : physRow p f g E k ∈ nonzeroChildFrequencyBall 1 R) :
    k ∈ nonzeroChildFrequencyBall 1 R := by
  have hc := physRow_coeff_ne_zero p hp f hf g E hE
  have h1 := one_le_eis_sq hc
  obtain ⟨hk1, hk2⟩ := ball_norm R _ hk
  unfold physRow at hk1 hk2
  rw [eis_norm_sq_mul] at hk1 hk2
  rw [mem_nonzeroChildFrequencyBall 1 one_ne_zero]
  simp only [one_mul]
  have hk0 : 0 ≤ ‖eisEmbedding k‖ ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · rcases hk0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hk1; exact absurd hk1 (lt_irrefl 0)
  · nlinarith

include hp in
theorem kIn_ball_eq (f : O) (hf : f ≠ 0) (g E : Finset ι) (hE : E ⊆ g) (R : ℝ) :
    kIn p hp f hf g E hE (nonzeroChildFrequencyBall 1 R) =
      (nonzeroChildFrequencyBall 1 R).filter
        (fun k => physRow p f g E k ∈ nonzeroChildFrequencyBall 1 R) := by
  ext k
  rw [mem_kIn, Finset.mem_filter]
  exact ⟨fun h => ⟨k_mem_of_row p hp f hf g E hE R k h, h⟩, fun h => h.2⟩

include hp in
theorem inball_attach_eq (f : O) (hf : f ≠ 0) (g : Finset ι) (R : ℝ) (F : Finset ι → O → ℝ)
    (c : Finset ι → ℝ) :
    ∑ E ∈ g.powerset.attach, c E.1 *
        ∑ k ∈ kIn p hp f hf g E.1 (Finset.mem_powerset.mp E.2) (nonzeroChildFrequencyBall 1 R),
          F E.1 k =
      ∑ E ∈ g.powerset, c E * ∑ k ∈ (nonzeroChildFrequencyBall 1 R).filter
        (fun k => physRow p f g E k ∈ nonzeroChildFrequencyBall 1 R), F E k := by
  rw [← Finset.sum_attach g.powerset (fun E => c E * ∑ k ∈ (nonzeroChildFrequencyBall 1 R).filter
        (fun k => physRow p f g E k ∈ nonzeroChildFrequencyBall 1 R), F E k)]
  apply Finset.sum_congr rfl
  intro E _
  rw [kIn_ball_eq p hp f hf g E.1 (Finset.mem_powerset.mp E.2) R]

include hp in
theorem inner_dead (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m f : O) (H : Finset ι → ℂ)
    (Wk : 𝓢(ℝ, ℂ)) (Y : ℝ) (g E : Finset ι) (k : O)
    (hdead : ∀ A ∈ (pool \ g).powerset, H (g ∪ A) = 0) :
    inner p hp hcop hg pool Ψ m f H Wk Y g E k = 0 := by
  unfold inner
  apply Finset.sum_eq_zero; intro A hA
  apply Finset.sum_eq_zero; intro B _
  split_ifs
  · rw [← norm_le_zero_iff]
    refine (innerPair_norm_le p hp hcop hg Ψ m f H Wk Y g E k A B).trans (le_of_eq ?_)
    have h1 := bigGBound_le p hp hcop hg hinj hc hpr Ψ hΨ m f H g A B
    have h0 := bigGBound_nonneg p hp hcop hg Ψ m f H g A B
    rw [hdead A hA, norm_zero, zero_mul, mul_zero] at h1
    rw [le_antisymm h1 h0, zero_div, zero_mul]
  · rfl

theorem primeMark_card_le (J : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ha : ∀ i j, ‖a i j‖ ≤ 1) (U : Finset ι) :
    ‖primeMarkInj J lists a U‖ ≤ (U.card : ℝ) ^ J.card :=
  markInj_norm_le lists a J (fun i _ P _ => ha i P) U

include hp in
theorem card_le_logb (U : Finset ι) : (U.card : ℝ) ≤ Real.logb 2 (primeProductNorm p U) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (FirstPassCubeLabels.primeProductNorm_pos p hp U),
    Real.rpow_natCast]
  exact two_pow_card_le_primeProductNorm p hp U

/-- The in-ball label set. -/
def labelSet (labels : Finset (Ideal O)) (pool : Finset ι) (ball : Finset O) (L : ℝ) :
    Finset (Ideal O × Finset ι × Finset ι × O) :=
  (labels ×ˢ pool.powerset ×ˢ pool.powerset ×ˢ ball).filter
    (fun l => l.2.2.1 ⊆ l.2.1 ∧ primeProductNorm p l.2.1 ≤ L ∧ labelRow p l ∈ ball)

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem sum_labelSet (labels : Finset (Ideal O)) (pool : Finset ι) (ball : Finset O) (L : ℝ)
    (F : Ideal O × Finset ι × Finset ι × O → ℝ) :
    ∑ l ∈ labelSet p labels pool ball L, F l =
      ∑ f ∈ labels, ∑ g ∈ pool.powerset, ∑ E ∈ pool.powerset, ∑ k ∈ ball,
        if E ⊆ g ∧ primeProductNorm p g ≤ L ∧
            physRow p (CompletedGauss.primaryGenerator f) g E k ∈ ball
          then F (f, g, E, k) else 0 := by
  unfold labelSet
  rw [Finset.sum_filter]
  simp only [Finset.sum_product]
  rfl

include hp in
theorem label_row_sum_eq (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (s₀ X bo : ℝ) (hX : 0 < X)
    (hW : ∀ x, W x ≠ 0 → x ≤ bo) (Wk : 𝓢(ℝ, ℂ)) (Y : ℝ) (f : Ideal O) (R Df : ℝ) :
    ∑ g ∈ pool.powerset, ∑ E ∈ pool.powerset, ∑ k ∈ nonzeroChildFrequencyBall 1 R,
        (if E ⊆ g ∧ primeProductNorm p g ≤ bo * X ∧
            physRow p (CompletedGauss.primaryGenerator f) g E k ∈ nonzeroChildFrequencyBall 1 R then
          Df * (Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2) *
            ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
              (entryH p slots lists a W s₀ X) Wk Y g E k‖ else 0) =
      Df * ∑ g ∈ pool.powerset, ∑ E ∈ g.powerset,
        Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
          ∑ k ∈ (nonzeroChildFrequencyBall 1 R).filter
            (fun k => physRow p (CompletedGauss.primaryGenerator f) g E k ∈
              nonzeroChildFrequencyBall 1 R),
            ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
              (entryH p slots lists a W s₀ X) Wk Y g E k‖ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg'
  by_cases hl : primeProductNorm p g ≤ bo * X
  · have hfil : pool.powerset.filter (fun E => E ⊆ g) = g.powerset := by
      ext E
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨h.trans (Finset.mem_powerset.mp hg'), h⟩⟩
    calc _ = ∑ E ∈ pool.powerset, if E ⊆ g then ∑ k ∈ nonzeroChildFrequencyBall 1 R,
          (if physRow p (CompletedGauss.primaryGenerator f) g E k ∈ nonzeroChildFrequencyBall 1 R then
            Df * (Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2) *
              ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
                (entryH p slots lists a W s₀ X) Wk Y g E k‖ else 0) else 0 := by
          apply Finset.sum_congr rfl; intro E _
          by_cases hEg : E ⊆ g
          · simp only [hEg, hl, true_and, ↓reduceIte]
          · simp only [hEg, false_and, ↓reduceIte, Finset.sum_const_zero]
      _ = ∑ E ∈ g.powerset, ∑ k ∈ nonzeroChildFrequencyBall 1 R,
          (if physRow p (CompletedGauss.primaryGenerator f) g E k ∈ nonzeroChildFrequencyBall 1 R then
            Df * (Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2) *
              ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
                (entryH p slots lists a W s₀ X) Wk Y g E k‖ else 0) := by
          rw [← Finset.sum_filter, hfil]
      _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro E _
          rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _
          split_ifs <;> ring
  · have hdead : ∀ E k, inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
        (entryH p slots lists a W s₀ X) Wk Y g E k = 0 := fun E k =>
      inner_dead p hp hcop hg hinj hc hpr pool Ψ hΨ m _ _ Wk Y g E k (by
        intro A hA
        by_contra hne
        have h1 := entryH_live p slots lists a W s₀ X bo hX hW _ hne
        have hgA : Disjoint g A := Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hA)
          Finset.disjoint_sdiff
        rw [FirstPassCubeLabels.primeProductNorm_union p g A hgA] at h1
        have h2 := one_le_primeProductNorm p hp A
        have h3 := FirstPassCubeLabels.primeProductNorm_pos p hp g
        apply hl; nlinarith)
    simp only [hdead, norm_zero, mul_zero, ite_self, Finset.sum_const_zero]

set_option maxHeartbeats 1600000 in
include hp in
/-- The in-ball rows of all labels. -/
theorem inball_le (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (ha : ∀ i j, ‖a i j‖ ≤ 1)
    (Kslots : ℕ) (hK : slots.card ≤ Kslots)
    (labels : Finset (Ideal O)) (hlab : ∀ f ∈ labels, CompletedGauss.primaryGenerator f ≠ 0)
    (D : Ideal O → ℝ) (Dmax : ℝ) (hD : ∀ f ∈ labels, 0 ≤ D f ∧ D f ≤ Dmax) (hDmax : 0 ≤ Dmax)
    (W Φ : ℝ → ℂ) (bo bl : ℝ) (hbl : bo ≤ bl) (hW : ∀ x, W x ≠ 0 → x ≤ bl) (b' : 𝓢(ℝ, ℂ))
    (hb' : ∀ r x h : ℝ, 1 ≤ r → r ≤ 2 → 0 < x →
      W (r * x) * logPhase h (Real.log (r * x)) =
        ∫ t : ℝ, logPhase (t + h) (Real.log r) * childLogTest Φ (t + h) x * b' t)
    (hΦ : ∀ x, 2 * bo < x → Φ x = 0)
    (Wk : 𝓢(ℝ, ℂ)) (d : ℕ) (Cb : ℝ) (hCb : 0 ≤ Cb) (bf : ℝ → 𝓢(ℝ, ℂ))
    (hbf : ∀ R : ℝ, 0 < R → KernelSep Wk W R (bf R) ∧
      ∀ t : ℝ, (1 + ‖t‖) ^ (2 * d + 2) * ‖bf R t‖ ≤ Cb)
    (Z X Y cZ Hc B s₀ : ℝ) (hX : 0 < X) (hY : 0 < Y) (hc0 : 0 ≤ cZ) (hboX : 1 ≤ bl * X)
    (hB : 0 ≤ B)
    (hchild : ChildBoundInj p hg pool Ψ m slots lists a ![Φ] d Z X (2 * bo * X) Hc B)
    (fib : ℝ) (hfib0 : 0 ≤ fib)
    (hfib : ∀ y : O, y ≠ 0 → ‖eisEmbedding y‖ ^ 2 ≤ Z ^ Hc →
      ((idealDivisors (Ideal.span {y})).card : ℝ) ^ 3 ≤ fib) :
    ∑ f ∈ labels, D f * cZ * ∑ g ∈ pool.powerset, ∑ E ∈ g.powerset,
        Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
          ∑ k ∈ (nonzeroChildFrequencyBall 1 (Z ^ Hc)).filter
            (fun k => physRow p (CompletedGauss.primaryGenerator f) g E k ∈
              nonzeroChildFrequencyBall 1 (Z ^ Hc)),
            ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
              (entryH p slots lists a W s₀ X) Wk Y g E k‖ ≤
      Cb * (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * X),
          kOne slots ((1 + Real.logb 2 (2 * (bl * X) ^ 2)) ^ Kslots) b' / primeProductNorm p t') *
        (∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖) *
        (2 * (Dmax * cZ * Y * fib * ((Nat.floor (Real.logb 2 (bl * X)) + 1 : ℕ) : ℝ) *
          (B * (1 + ‖s₀‖) ^ (2 * d) * ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d)))) *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(2 : ℝ)) := by
  obtain ⟨S, hS⟩ : ∃ S, S = labelSet p labels pool (nonzeroChildFrequencyBall 1 (Z ^ Hc)) (bl * X) :=
    ⟨_, rfl⟩
  have hboX0 : 0 < bl * X := by linarith
  -- membership in the label set
  have hmemS : ∀ l ∈ S, l.1 ∈ labels ∧ l.2.2.2 ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc) ∧
      l.2.2.1 ⊆ l.2.1 ∧ primeProductNorm p l.2.1 ≤ bl * X ∧
      labelRow p l ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc) := by
    intro l hl
    rw [hS] at hl
    unfold labelSet at hl
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_product] at hl
    exact ⟨hl.1.1, hl.1.2.2.2, hl.2.1, hl.2.2.1, hl.2.2.2⟩
  -- the label sum
  have hconv : ∑ f ∈ labels, D f * cZ * ∑ g ∈ pool.powerset, ∑ E ∈ g.powerset,
        Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
          ∑ k ∈ (nonzeroChildFrequencyBall 1 (Z ^ Hc)).filter
            (fun k => physRow p (CompletedGauss.primaryGenerator f) g E k ∈
              nonzeroChildFrequencyBall 1 (Z ^ Hc)),
            ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator f)
              (entryH p slots lists a W s₀ X) Wk Y g E k‖ =
      ∑ l ∈ S, D l.1 * cZ *
        (Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) l.2.2.1)‖ ^ 2) *
        ‖inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator l.1)
          (entryH p slots lists a W s₀ X) Wk Y l.2.1 l.2.2.1 l.2.2.2‖ := by
    rw [hS, sum_labelSet]
    apply Finset.sum_congr rfl; intro f _
    exact (label_row_sum_eq p hp hcop hg hinj hc hpr pool Ψ hΨ m slots lists a W s₀ X bl hX hW
      Wk Y f (Z ^ Hc) (D f * cZ)).symm
  rw [hconv]
  -- the data of `inball_total`
  set iof : Ideal O × Finset ι × Finset ι × O → ℕ :=
    fun l => Nat.log 2 (Ideal.absNorm (colIdeal p l.2.1)) with hiof
  have hn0 : ∀ g : Finset ι, Ideal.absNorm (colIdeal p g) ≠ 0 := by
    intro g
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact colIdeal_ne_bot p hp g
  have hi1 : ∀ l : Ideal O × Finset ι × Finset ι × O,
      (2 : ℝ) ^ iof l ≤ primeProductNorm p l.2.1 := by
    intro l
    rw [primeProductNorm_eq_absNorm]
    exact_mod_cast Nat.pow_log_le_self 2 (hn0 l.2.1)
  have hi2 : ∀ l : Ideal O × Finset ι × Finset ι × O,
      primeProductNorm p l.2.1 ≤ 2 * 2 ^ iof l := by
    intro l
    rw [primeProductNorm_eq_absNorm]
    have h := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
      (Ideal.absNorm (colIdeal p l.2.1))).le
    rw [pow_succ, mul_comm] at h
    exact_mod_cast h
  have hR : ∀ l ∈ S, 0 < poissonR p Y X l.2.1 l.2.2.1 l.2.2.2 := by
    intro l hl
    obtain ⟨_, hk, _, _, _⟩ := hmemS l hl
    have hk2 := (ball_norm _ _ hk).1
    have hg0 := FirstPassCubeLabels.primeProductNorm_pos p hp l.2.1
    have he := one_le_gen_norm_sq p hp l.2.2.1
    unfold poissonR
    exact div_pos (mul_pos (mul_pos hY hk2) (pow_pos hg0 2))
      (mul_pos (by linarith) (pow_pos hX 2))
  set Lp := (1 + Real.logb 2 (2 * (bl * X) ^ 2)) ^ Kslots with hLp
  have hlog0 : 0 ≤ Real.logb 2 (2 * (bl * X) ^ 2) :=
    Real.logb_nonneg (by norm_num) (by nlinarith)
  have hLp0 : 0 ≤ Lp := pow_nonneg (by linarith) _
  set I := Nat.floor (Real.logb 2 (bl * X)) with hI
  have hInt : (Module.finrank ℝ ℝ : ℝ) < 2 := by rw [Module.finrank_self]; norm_num
  set Kc := Cb * (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * X),
          kOne slots Lp b' / primeProductNorm p t') *
        (∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖) *
        (2 * (Dmax * cZ * Y * fib * ((I + 1 : ℕ) : ℝ) *
          (B * (1 + ‖s₀‖) ^ (2 * d) * ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d)))) with hKc
  have hpt : ∀ t : ℝ, Cb / (1 + ‖t‖) ^ (2 * d + 2) *
      ((∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * X),
          kOne slots Lp b' / primeProductNorm p t') *
        (∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖) *
        (2 * (Dmax * cZ * Y * fib * ((I + 1 : ℕ) : ℝ) *
          (B * ((1 + ‖s₀‖) ^ (2 * d) * (1 + ‖t‖) ^ (2 * d)) *
            ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d))))) =
      Kc * (1 + ‖t‖) ^ (-(2 : ℝ)) := by
    intro t
    have hq : 0 < 1 + ‖t‖ := by positivity
    rw [hKc, Real.rpow_neg hq.le, Real.rpow_two, pow_add]
    generalize (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) = P1
    generalize (∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * X),
          kOne slots Lp b' / primeProductNorm p t') = P2
    generalize (∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖) = P3
    generalize (∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d)) = Mb
    generalize 1 + ‖t‖ = q at hq ⊢
    have h1 : q ^ (2 * d) * (q ^ (2 * d))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hq.ne')
    calc Cb / (q ^ (2 * d) * q ^ 2) * (P1 * P2 * P3 * (2 * (Dmax * cZ * Y * fib *
          ((I + 1 : ℕ) : ℝ) * (B * ((1 + ‖s₀‖) ^ (2 * d) * q ^ (2 * d)) * Mb))))
        = Cb * P1 * P2 * P3 * (2 * (Dmax * cZ * Y * fib * ((I + 1 : ℕ) : ℝ) *
          (B * (1 + ‖s₀‖) ^ (2 * d) * Mb))) * (q ^ 2)⁻¹ * (q ^ (2 * d) * (q ^ (2 * d))⁻¹) := by
          ring
      _ = _ := by rw [h1, mul_one]
  calc _ ≤ ∫ t : ℝ, Cb / (1 + ‖t‖) ^ (2 * d + 2) *
      ((∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * X),
          kOne slots Lp b' / primeProductNorm p t') *
        (∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖) *
        (2 * (Dmax * cZ * Y * fib * ((I + 1 : ℕ) : ℝ) *
          (B * ((1 + ‖s₀‖) ^ (2 * d) * (1 + ‖t‖) ^ (2 * d)) *
            ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d))))) := by
        refine inball_total S
          (fun l => D l.1 * cZ *
            (Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) l.2.2.1)‖ ^ 2))
          ?_ (fun l => inner p hp hcop hg pool Ψ m (CompletedGauss.primaryGenerator l.1)
            (entryH p slots lists a W s₀ X) Wk Y l.2.1 l.2.2.1 l.2.2.2)
          (fun l => star (canonCoeff p hp hcop hg Ψ m (CompletedGauss.primaryGenerator l.1)
              (fun _ => 1) l.2.1) *
            canonCoeff p hp hcop hg Ψ m (CompletedGauss.primaryGenerator l.1) (fun _ => 1) l.2.1)
          ?_ (fun l => ⇑(bf (poissonR p Y X l.2.1 l.2.2.1 l.2.2.2)))
          (fun l t => labelLam p hg pool Ψ m slots lists a Φ b' l.2.1 X (iof l) s₀
            (labelRow p l) t)
          (fun l t => labelLam_nonneg p hg pool Ψ m slots lists a Φ b' l.2.1 X (iof l) s₀
            (labelRow p l) t)
          (fun t => Cb / (1 + ‖t‖) ^ (2 * d + 2)) ?_ ?_ _ ?_ ?_ ?_
        · intro l hl
          beta_reduce
          obtain ⟨hf, _, _, _, _⟩ := hmemS l hl
          exact mul_nonneg (mul_nonneg (hD _ hf).1 hc0) (div_nonneg hY.le (sq_nonneg _))
        · intro l _
          beta_reduce
          have h := canonCoeff_one_norm_le p hp hcop hg hc Ψ hΨ m
            (CompletedGauss.primaryGenerator l.1) l.2.1
          rw [norm_mul, norm_star]
          exact mul_le_one₀ h (norm_nonneg _) h
        · intro l hl t
          beta_reduce
          have h := (hbf _ (hR l hl)).2 t
          rw [le_div_iff₀ (by positivity), mul_comm]
          exact h
        · intro l hl
          obtain ⟨hf, _, hE, _, _⟩ := hmemS l hl
          exact label_inner_bound p hp hcop hg hinj hc hpr pool Ψ hΨ m slots lists a W Φ b' hb'
            Wk Y X s₀ hX (CompletedGauss.primaryGenerator l.1) l.2.1 l.2.2.1 hE l.2.2.2 (iof l)
            (hi1 l) (hi2 l) _ ((bf _).integrable (μ := volume)) (hbf _ (hR l hl)).1
        · intro t
          refine lam_sum_le p hp hg hinj pool Ψ hΨ m slots lists a Φ b' d Z X bo Hc B hX hB hΦ
            hchild S (fun l => l.2.1) iof (labelRow p) _ I (Dmax * cZ * Y) fib
            (mul_nonneg (mul_nonneg hDmax hc0) hY.le) hfib0 ?_ ?_ ?_ (fun l _ => hi2 l) ?_ ?_ ?_ ?_
            Lp hLp0 ?_ s₀ t
          · intro l hl
            obtain ⟨hf, _, _, _, _⟩ := hmemS l hl
            exact mul_nonneg (mul_nonneg (hD _ hf).1 hc0) (div_nonneg hY.le (sq_nonneg _))
          · intro l hl
            obtain ⟨hf, _, _, _, _⟩ := hmemS l hl
            exact mul_le_mul (mul_le_mul_of_nonneg_right (hD _ hf).2 hc0)
              (div_le_self hY.le (one_le_gen_norm_sq p hp _)) (div_nonneg hY.le (sq_nonneg _))
              (mul_nonneg hDmax hc0)
          · intro l hl
            obtain ⟨_, _, _, hlive, _⟩ := hmemS l hl
            apply Nat.le_floor
            rw [Real.le_logb_iff_rpow_le (by norm_num) hboX0, Real.rpow_natCast]
            exact (hi1 l).trans hlive
          · intro l hl
            obtain ⟨_, _, _, _, hrow⟩ := hmemS l hl
            exact ball_neg _ _ hrow
          · intro l hl
            obtain ⟨_, _, _, _, hrow⟩ := hmemS l hl
            exact hrow
          · intro y hy
            have hy0 := ball_ne_zero _ _ hy
            have heq : S.filter (fun l => -labelRow p l = y) =
                S.filter (fun l => labelRow p l = -y) :=
              Finset.filter_congr fun l _ => neg_eq_iff_eq_neg
            rw [heq]
            refine (fibre_card_le p hinj S (fun l hl => ⟨hlab _ (hmemS l hl).1, (hmemS l hl).2.2.1⟩)
              (-y) (neg_ne_zero.mpr hy0)).trans ?_
            rw [Ideal.span_singleton_neg]
            exact hfib y hy0 (ball_norm _ _ hy).2
          · intro y hy
            have hy0 := ball_ne_zero _ _ hy
            refine (fibre_card_le p hinj S (fun l hl => ⟨hlab _ (hmemS l hl).1, (hmemS l hl).2.2.1⟩)
              y hy0).trans ?_
            exact hfib y hy0 (ball_norm _ _ hy).2
          · intro l hl t' ht' hNt J hJ
            obtain ⟨_, _, _, hlive, _⟩ := hmemS l hl
            refine (primeMark_card_le J lists a ha _).trans ?_
            have hgt : Disjoint l.2.1 t' := Finset.disjoint_of_subset_right
              (Finset.mem_powerset.mp ht') Finset.disjoint_sdiff
            have hcard := card_le_logb p hp (l.2.1 ∪ t')
            rw [FirstPassCubeLabels.primeProductNorm_union p _ _ hgt] at hcard
            have hg0 := FirstPassCubeLabels.primeProductNorm_pos p hp l.2.1
            have ht0 := FirstPassCubeLabels.primeProductNorm_pos p hp t'
            have hN : primeProductNorm p l.2.1 * primeProductNorm p t' ≤ 2 * (bl * X) ^ 2 := by
              calc primeProductNorm p l.2.1 * primeProductNorm p t' ≤ (bl * X) * (2 * bl * X) :=
                    mul_le_mul hlive (hNt.trans (by nlinarith)) ht0.le hboX0.le
                _ = 2 * (bl * X) ^ 2 := by ring
            have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (mul_pos hg0 ht0) hN
            have hJc : J.card ≤ Kslots := (Finset.card_le_card (Finset.mem_powerset.mp hJ)).trans hK
            calc ((l.2.1 ∪ t').card : ℝ) ^ J.card
                ≤ (1 + Real.logb 2 (2 * (bl * X) ^ 2)) ^ J.card :=
                  pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
              _ ≤ Lp := pow_le_pow_right₀ (by linarith) hJc
        · exact ((integrable_one_add_norm (μ := (volume : Measure ℝ)) hInt).const_mul Kc).congr
            (ae_of_all _ fun t => (hpt t).symm)
        · intro t; beta_reduce; exact div_nonneg hCb (by positivity)
    _ = Kc * ∫ t : ℝ, (1 + ‖t‖) ^ (-(2 : ℝ)) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ hpt)
    _ = _ := by rw [hKc]

end
end Qrh.MarkedAnchor.Inverse.Poisson
