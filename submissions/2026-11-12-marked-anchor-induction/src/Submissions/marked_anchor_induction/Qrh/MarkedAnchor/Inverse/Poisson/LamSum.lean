/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.CellChild

/-!
# Inverse.Poisson.LamSum — summing the label densities by fibres

`∑_l w_l Λ_l(t) ≤ Ccc · Hsum · K₁ · Gc · wmax · fib · (I+1) · 2 B (1+|s₀|)^(2d) (1+|t|)^(2d) Mb'`.
Labels `l` carry the dyadic block `i_l`, the row `y_l` (and `-y_l`); the child vector of a cell
depends only on `(χ, η, t', c, i)`, never on the label (the residual coefficient vector is
independent of `f, g, d`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.SecondPassArithmetic (rayMonoid conjugateRayMonoid)
open OAI.RayFourExpansion (RayCharacter rayCharacter gCoeff crossCoeff)

local notation "O" => ActualEisensteinCubic.O

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
/-- One side of a cell summed over the labels. -/
theorem side_label_sum {L : Type*} (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (d : ℕ) (Z X bo Hc B : ℝ)
    (hX : 0 < X) (hB : 0 ≤ B) (hΦ : ∀ x, 2 * bo < x → Φ x = 0)
    (hchild : ChildBoundInj p hg pool Ψ m slots lists a ![Φ] d Z X (2 * bo * X) Hc B)
    (t : Finset ι) (ht : t ∈ pool.powerset) (ψ₀ : O →* ℂ) (c : RayCharacter × Finset σ)
    (hc : c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset)
    (hψ : IsChildRay Ψ (rayMonoid c.1 * ψ₀)) (hψn : ∀ u, ‖(rayMonoid c.1 * ψ₀) u‖ ≤ 1)
    (h : ℝ) (S : Finset L) (iof : L → ℕ) (zof : L → O) (w : L → ℝ) (I : ℕ) (wmax fib : ℝ)
    (hwmax : 0 ≤ wmax) (hfib0 : 0 ≤ fib) (hw0 : ∀ l ∈ S, 0 ≤ w l) (hw : ∀ l ∈ S, w l ≤ wmax)
    (hI : ∀ l ∈ S, iof l ≤ I) (hz : ∀ l ∈ S, zof l ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc))
    (hfib : ∀ y ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc),
      ((S.filter (fun l => zof l = y)).card : ℝ) ≤ fib) :
    ∑ l ∈ S, w l * cellG p hg pool t ψ₀ m slots lists a Φ b' X h c (iof l) (zof l) ≤
      wmax * fib * ((I + 1 : ℕ) : ℝ) *
        (B * (1 + ‖h‖) ^ (2 * d) * ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d)) := by
  have hbf := blocked_fibre S iof zof w
    (fun i y => cellG p hg pool t ψ₀ m slots lists a Φ b' X h c i y)
    (nonzeroChildFrequencyBall 1 (Z ^ Hc)) I wmax fib hwmax hw0 hw
    (fun i y => cellG_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ c i y) hI hz hfib
  refine hbf.trans ?_
  have hsum : ∑ i ∈ Finset.range (I + 1), ∑ y ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc),
      cellG p hg pool t ψ₀ m slots lists a Φ b' X h c i y ≤
      ∑ _i ∈ Finset.range (I + 1),
        B * (1 + ‖h‖) ^ (2 * d) * ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d) :=
    Finset.sum_le_sum fun i _ => cellG_sum_le p hp hg hinj pool Ψ m slots lists a Φ b' d Z X bo
      Hc B hX hB hΦ hchild t ht ψ₀ c hc hψ hψn i h
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  calc wmax * fib * ∑ i ∈ Finset.range (I + 1), ∑ y ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc),
        cellG p hg pool t ψ₀ m slots lists a Φ b' X h c i y
      ≤ wmax * fib * (((I + 1 : ℕ) : ℝ) *
        (B * (1 + ‖h‖) ^ (2 * d) * ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d))) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hwmax hfib0)
    _ = _ := by ring

theorem sum_comm4 {L A B C : Type*} (S : Finset L) (sA : Finset A) (sB : Finset B) (sC : Finset C)
    (f : L → A → B → C → ℝ) :
    ∑ l ∈ S, ∑ x ∈ sA, ∑ y ∈ sB, ∑ z ∈ sC, f l x y z =
      ∑ x ∈ sA, ∑ y ∈ sB, ∑ z ∈ sC, ∑ l ∈ S, f l x y z := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.sum_comm]

include hp in
theorem lam_sum_le {L : Type*} (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b' : 𝓢(ℝ, ℂ)) (d : ℕ) (Z X bo Hc B : ℝ)
    (hX : 0 < X) (hB : 0 ≤ B) (hΦ : ∀ x, 2 * bo < x → Φ x = 0)
    (hchild : ChildBoundInj p hg pool Ψ m slots lists a ![Φ] d Z X (2 * bo * X) Hc B)
    (S : Finset L) (gof : L → Finset ι) (iof : L → ℕ) (yof : L → O) (w : L → ℝ) (I : ℕ)
    (wmax fib : ℝ) (hwmax : 0 ≤ wmax) (hfib0 : 0 ≤ fib)
    (hw0 : ∀ l ∈ S, 0 ≤ w l) (hw : ∀ l ∈ S, w l ≤ wmax) (hI : ∀ l ∈ S, iof l ≤ I)
    (hgi : ∀ l ∈ S, primeProductNorm p (gof l) ≤ 2 * 2 ^ iof l)
    (hzA : ∀ l ∈ S, -yof l ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc))
    (hzB : ∀ l ∈ S, yof l ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc))
    (hfibA : ∀ y ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc),
      ((S.filter (fun l => -yof l = y)).card : ℝ) ≤ fib)
    (hfibB : ∀ y ∈ nonzeroChildFrequencyBall 1 (Z ^ Hc),
      ((S.filter (fun l => yof l = y)).card : ℝ) ≤ fib)
    (Lp : ℝ) (hLp0 : 0 ≤ Lp)
    (hLp : ∀ l ∈ S, ∀ t' ∈ (pool \ gof l).powerset, primeProductNorm p t' ≤ 2 * bo * X →
      ∀ J ∈ slots.powerset, ‖primeMarkInj J lists a (gof l ∪ t')‖ ≤ Lp)
    (s₀ t : ℝ) :
    ∑ l ∈ S, w l * labelLam p hg pool Ψ m slots lists a Φ b' (gof l) X (iof l) s₀ (yof l) t ≤
      (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ t' ∈ pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * X),
          kOne slots Lp b' / primeProductNorm p t') *
        (∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖) *
        (2 * (wmax * fib * ((I + 1 : ℕ) : ℝ) *
          (B * ((1 + ‖s₀‖) ^ (2 * d) * (1 + ‖t‖) ^ (2 * d)) *
            ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d)))) := by
  set T := pool.powerset.filter (fun t' => primeProductNorm p t' ≤ 2 * bo * X) with hT
  set Mb := ∫ τ : ℝ, ‖b' τ‖ * (1 + ‖τ‖) ^ (2 * d) with hMb
  have hMb0 : 0 ≤ Mb := integral_nonneg fun τ => by positivity
  set K := wmax * fib * ((I + 1 : ℕ) : ℝ) *
    (B * ((1 + ‖s₀‖) ^ (2 * d) * (1 + ‖t‖) ^ (2 * d)) * Mb) with hK
  have hK0 : 0 ≤ K := by positivity
  -- one side per cell
  have hside : ∀ χ η : RayCharacter, ∀ t' ∈ T, ∀ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset,
      ∑ l ∈ S, w l *
        (cellG p hg pool t' (conjugateRayMonoid χ * Ψ) m slots lists a Φ b' X (s₀ + t) c (iof l) (-yof l) +
          cellG p hg pool t' (rayMonoid η * Ψ) m slots lists a Φ b' X (s₀ - t) c (iof l) (yof l)) ≤
      2 * K := by
    intro χ η t' ht' c hc
    have htp : t' ∈ pool.powerset := (Finset.mem_filter.mp ht').1
    have hA := side_label_sum p hp hg hinj pool Ψ m slots lists a Φ b' d Z X bo Hc B hX hB hΦ hchild
      t' htp (conjugateRayMonoid χ * Ψ) c hc (isChildRay_conj c.1 χ Ψ)
      (fun u => twist_conj_le c.1 χ Ψ hΨ u) (s₀ + t) S iof (fun l => -yof l) w I wmax fib hwmax
      hfib0 hw0 hw hI hzA hfibA
    have hB' := side_label_sum p hp hg hinj pool Ψ m slots lists a Φ b' d Z X bo Hc B hX hB hΦ hchild
      t' htp (rayMonoid η * Ψ) c hc (isChildRay_plain c.1 η Ψ)
      (fun u => twist_plain_le c.1 η Ψ hΨ u) (s₀ - t) S iof yof w I wmax fib hwmax
      hfib0 hw0 hw hI hzB hfibB
    have hpA := one_add_pow_add_le s₀ t (2 * d)
    have hpB : (1 + ‖s₀ - t‖) ^ (2 * d) ≤ (1 + ‖s₀‖) ^ (2 * d) * (1 + ‖t‖) ^ (2 * d) := by
      have := one_add_pow_add_le s₀ (-t) (2 * d)
      rwa [← sub_eq_add_neg, norm_neg] at this
    have hc0 : 0 ≤ wmax * fib * ((I + 1 : ℕ) : ℝ) := by positivity
    have hsplit : ∑ l ∈ S, w l *
        (cellG p hg pool t' (conjugateRayMonoid χ * Ψ) m slots lists a Φ b' X (s₀ + t) c (iof l) (-yof l) +
          cellG p hg pool t' (rayMonoid η * Ψ) m slots lists a Φ b' X (s₀ - t) c (iof l) (yof l)) =
        ∑ l ∈ S, w l * cellG p hg pool t' (conjugateRayMonoid χ * Ψ) m slots lists a Φ b' X (s₀ + t) c
            (iof l) (-yof l) +
        ∑ l ∈ S, w l * cellG p hg pool t' (rayMonoid η * Ψ) m slots lists a Φ b' X (s₀ - t) c
            (iof l) (yof l) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro l _; ring
    rw [hsplit, two_mul]
    apply add_le_add
    · refine hA.trans ?_
      rw [hK]
      apply mul_le_mul_of_nonneg_left _ hc0
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpA hB) hMb0
    · refine hB'.trans ?_
      rw [hK]
      apply mul_le_mul_of_nonneg_left _ hc0
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpB hB) hMb0
  calc ∑ l ∈ S, w l * labelLam p hg pool Ψ m slots lists a Φ b' (gof l) X (iof l) s₀ (yof l) t
      ≤ ∑ l ∈ S, w l * (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖ *
          ∑ t' ∈ T, lamTerm p hg pool Ψ m slots lists a Φ b' X (iof l) s₀ (yof l) t Lp χ η t') :=
        Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left
          (lam_label_le p hp hg pool Ψ m slots lists a Φ b' (gof l) X (iof l) s₀ (yof l) t bo Lp hX
            hΦ hLp0 (hgi l hl) (hLp l hl)) (hw0 l hl)
    _ = ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ t' ∈ T, ∑ l ∈ S,
          ‖crossCoeff χ η‖ * (w l * lamTerm p hg pool Ψ m slots lists a Φ b' X (iof l) s₀ (yof l) t
            Lp χ η t') := by
        rw [← sum_comm4]
        apply Finset.sum_congr rfl; intro l _
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro χ _
        apply Finset.sum_congr rfl; intro η _
        apply Finset.sum_congr rfl; intro t' _
        ring
    _ ≤ ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ t' ∈ T,
          ‖crossCoeff χ η‖ * (kOne slots Lp b' / primeProductNorm p t' *
            ∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖ * (2 * K)) := by
        apply Finset.sum_le_sum; intro χ _
        apply Finset.sum_le_sum; intro η _
        apply Finset.sum_le_sum; intro t' ht'
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have hk1 : 0 ≤ kOne slots Lp b' / primeProductNorm p t' := by
          have := FirstPassCubeLabels.primeProductNorm_pos p hp t'
          unfold kOne
          have : 0 ≤ ∑ θ : RayCharacter, ‖gCoeff θ‖ := Finset.sum_nonneg fun θ _ => norm_nonneg _
          have : 0 ≤ ∫ τ : ℝ, ‖b' τ‖ := integral_nonneg fun τ => norm_nonneg _
          positivity
        calc ∑ l ∈ S, w l * lamTerm p hg pool Ψ m slots lists a Φ b' X (iof l) s₀ (yof l) t Lp χ η t'
            = kOne slots Lp b' / primeProductNorm p t' *
              ∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖ *
                ∑ l ∈ S, w l *
                  (cellG p hg pool t' (conjugateRayMonoid χ * Ψ) m slots lists a Φ b' X (s₀ + t) c
                      (iof l) (-yof l) +
                    cellG p hg pool t' (rayMonoid η * Ψ) m slots lists a Φ b' X (s₀ - t) c
                      (iof l) (yof l)) := by
              unfold lamTerm
              simp only [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro c _
              apply Finset.sum_congr rfl; intro l _
              ring
          _ ≤ kOne slots Lp b' / primeProductNorm p t' *
              ∑ c ∈ (Finset.univ : Finset RayCharacter) ×ˢ slots.powerset, ‖gCoeff c.1‖ * (2 * K) := by
              apply mul_le_mul_of_nonneg_left _ hk1
              exact Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left
                (hside χ η t' ht' c hc) (norm_nonneg _)
    _ = _ := by
        simp only [← Finset.sum_mul, ← Finset.mul_sum]
        rw [hK]
        ring

end
end Qrh.MarkedAnchor.Inverse.Poisson
