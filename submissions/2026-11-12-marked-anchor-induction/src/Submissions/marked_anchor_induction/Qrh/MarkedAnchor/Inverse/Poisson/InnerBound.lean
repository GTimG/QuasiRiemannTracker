/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.PairSep
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.RowSep

/-!
# Inverse.Poisson.InnerBound — the residual pair sum as one separated integral

`inner g E k = Q_g ∫ b(t) · sepBil(t) dt` for the kernel coefficient `b` at `R = poissonR`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open ConcreteTraceCRT (eisEmbedding)
open MixedCrossSeparation (columnG quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius)
open OAI.FirstPassCubeLabels (primeProductNorm)
open FourierBridge (logPhase)

local notation "O" => ActualEisensteinCubic.O

theorem logPhase_cont_plus (c x : ℝ) : Continuous (fun t : ℝ => logPhase (c + t) x) := by
  unfold logPhase; fun_prop

theorem logPhase_cont_minus (c x : ℝ) : Continuous (fun t : ℝ => logPhase (c - t) x) := by
  unfold logPhase; fun_prop

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem sepPair_phase (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (W : ℝ → ℂ) (g : Finset ι) (X s₀ : ℝ) (y : O) (A B : Finset ι) (t : ℝ) :
    quadraticCrossPhase p hg A B * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) *
      star (sepCol p hp hcop hg Ψ m slots lists a W g X y (s₀ + t) A) *
      sepCol p hp hcop hg Ψ m slots lists a W g X y (s₀ - t) B =
    (quadraticCrossPhase p hg A B * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) *
      star (colCore p hp hcop hg Ψ m slots lists a g y A * W (colX p g A X) *
        (((Real.sqrt (primeProductNorm p A))⁻¹ : ℝ) : ℂ)) *
      (colCore p hp hcop hg Ψ m slots lists a g y B * W (colX p g B X) *
        (((Real.sqrt (primeProductNorm p B))⁻¹ : ℝ) : ℂ))) *
    (star (logPhase (s₀ + t) (Real.log (colX p g A X))) *
      logPhase (s₀ - t) (Real.log (colX p g B X))) := by
  unfold sepCol
  simp only [star_mul]
  ring

theorem integrable_sepPair (b : ℝ → ℂ) (hb : Integrable b) (C : ℂ) (s₀ La Lb : ℝ) :
    Integrable (fun t : ℝ => b t * (C * (star (logPhase (s₀ + t) La) * logPhase (s₀ - t) Lb))) := by
  refine hb.mul_bdd (c := ‖C‖) ?_ (ae_of_all _ ?_)
  · exact (continuous_const.mul (((logPhase_cont_plus s₀ La).star).mul
      (logPhase_cont_minus s₀ Lb))).aestronglyMeasurable
  · intro t
    rw [norm_mul, norm_mul, norm_star, logPhase_norm, logPhase_norm, mul_one, mul_one]

variable (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem inner_eq_integral (pool : Finset ι) (Ψ : O →* ℂ) (m f : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (Wk : 𝓢(ℝ, ℂ)) (Y X s₀ : ℝ)
    (hX : 0 < X) (g E : Finset ι) (k : O) (b : ℝ → ℂ) (hbint : Integrable b)
    (hb : KernelSep Wk W (poissonR p Y X g E k) b) :
    inner p hp hcop hg pool Ψ m f (entryH p slots lists a W s₀ X) Wk Y g E k =
      (star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
        canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
      ∫ t : ℝ, b t * sepBil p hp hcop hg pool Ψ m slots lists a W g X s₀ (physRow p f g E k) t := by
  unfold inner sepBil
  have hint : ∀ A B : Finset ι, Integrable (fun t : ℝ => b t *
      (quadraticCrossPhase p hg A B * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) *
        star (sepCol p hp hcop hg Ψ m slots lists a W g X (physRow p f g E k) (s₀ + t) A) *
        sepCol p hp hcop hg Ψ m slots lists a W g X (physRow p f g E k) (s₀ - t) B)) := by
    intro A B
    simp only [sepPair_phase]
    exact integrable_sepPair b hbint _ s₀ _ _
  have hite : ∀ t : ℝ, b t * (∑ A ∈ (pool \ g).powerset, ∑ B ∈ (pool \ g).powerset,
      if Disjoint A B then quadraticCrossPhase p hg A B *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) *
        star (sepCol p hp hcop hg Ψ m slots lists a W g X (physRow p f g E k) (s₀ + t) A) *
        sepCol p hp hcop hg Ψ m slots lists a W g X (physRow p f g E k) (s₀ - t) B else 0) =
      ∑ A ∈ (pool \ g).powerset, ∑ B ∈ (pool \ g).powerset,
        if Disjoint A B then b t * (quadraticCrossPhase p hg A B *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) *
          star (sepCol p hp hcop hg Ψ m slots lists a W g X (physRow p f g E k) (s₀ + t) A) *
          sepCol p hp hcop hg Ψ m slots lists a W g X (physRow p f g E k) (s₀ - t) B) else 0 := by
    intro t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro A _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro B _
    split_ifs <;> simp
  simp_rw [hite]
  rw [integral_finset_sum _ (fun A _ => integrable_finset_sum _ (fun B _ => by
    by_cases hd : Disjoint A B <;> simp only [hd, if_true, if_false] <;>
      first | exact hint A B | exact integrable_zero _ _ _))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [integral_finset_sum _ (fun B _ => by
    by_cases hd : Disjoint A B <;> simp only [hd, if_true, if_false] <;>
      first | exact hint A B | exact integrable_zero _ _ _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hd : Disjoint A B
  · simp only [if_pos hd]
    have hgA : Disjoint g A := Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hA)
      Finset.disjoint_sdiff
    have hgB : Disjoint g B := Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hB)
      Finset.disjoint_sdiff
    exact innerPair_sep p hp hcop hg Ψ m f slots lists a W Wk Y X s₀ hX g E k b hb A B hgA hgB hd
  · simp [hd]

end
end Qrh.MarkedAnchor.Inverse.Poisson
