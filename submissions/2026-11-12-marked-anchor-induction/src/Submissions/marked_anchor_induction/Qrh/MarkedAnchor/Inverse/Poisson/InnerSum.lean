/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.Grouping

/-!
# Inverse.Poisson.InnerSum — the residual pair sum inside the dual frequency sum

`∑_g ∑_{a,b ⊆ pool\g disjoint} groupedTerm g a b = ∑_g ∑_{E ⊆ g} (μ(E) Y/N e) ∑'_k inner g E k`,
`inner g E k = ∑_{a,b disjoint} Ŵ(Y‖k‖²/(N e · N a N b))/√(N a N b) · bigG g a b E k`.
For fixed `(g, E, k)` the inner sum is the bilinear form in the residual columns that the
separation, the cross phase, the projector and the side expansion act on.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnG quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The physical row `y = f² (e g') g' k`. -/
def physRow (f : O) (g E : Finset ι) (k : O) : O :=
  f ^ 2 * (primeSubsetGenerator (fun i => Ideal.span {p i}) E * cofactor p g E) *
    cofactor p g E * k

/-- The coefficient of the physical row `y` in the grouped term. -/
def bigG (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (g a b E : Finset ι) (k : O) : ℂ :=
  star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
    canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g *
    quadraticCrossPhase p hg a b *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a (-1) *
    star (physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A)) (physRow p f g E k) a) *
    physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A)) (physRow p f g E k) b

/-- The kernel denominator `N e · N a N b`. -/
def kernelDen (E a b : Finset ι) : ℝ :=
  ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
    ‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ ^ 2

def innerPair (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (g E : Finset ι) (k : O) (a b : Finset ι) : ℂ :=
  paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 / kernelDen p E a b) /
      (‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ : ℂ) *
    bigG p hp hcop hg Ψ m f H g a b E k

def inner (pool : Finset ι) (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (g E : Finset ι) (k : O) : ℂ :=
  ∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset,
    if Disjoint a b then innerPair p hp hcop hg Ψ m f H W Y g E k a b else 0

theorem physCoeff_norm_le (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (y : O) (A : Finset ι) :
    ‖physCoeff p hp hcop hg Ψ m H y A‖ ≤
      ‖supportMobius (fun i => Ideal.span {p i}) A * columnG p hp hcop hg A *
        Ψ (∏ i ∈ A, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) A m * H A‖ := by
  unfold physCoeff
  have h1 := finiteSquarefreeRow_norm_le_one (fun i => Ideal.span {p i}) hg A y
  simp only [norm_mul, norm_star]
  have := norm_nonneg (supportMobius (fun i => Ideal.span {p i}) A)
  have := norm_nonneg (columnG p hp hcop hg A)
  have := norm_nonneg (Ψ (∏ i ∈ A, p i))
  have := norm_nonneg (rowCoprimeMask (fun i => Ideal.span {p i}) A m)
  have := norm_nonneg (H A)
  calc _ ≤ ‖supportMobius (fun i => Ideal.span {p i}) A‖ * ‖columnG p hp hcop hg A‖ *
        ‖Ψ (∏ i ∈ A, p i)‖ * ‖rowCoprimeMask (fun i => Ideal.span {p i}) A m‖ * 1 * ‖H A‖ := by
          gcongr
    _ = _ := by ring

/-- A `k`-independent bound for `bigG`. -/
def bigGBound (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (g a b : Finset ι) : ℝ :=
  ‖star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
    canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g * quadraticCrossPhase p hg a b *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a (-1)‖ *
  ‖supportMobius (fun i => Ideal.span {p i}) a * columnG p hp hcop hg a *
    Ψ (∏ i ∈ a, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) a m * H (g ∪ a)‖ *
  ‖supportMobius (fun i => Ideal.span {p i}) b * columnG p hp hcop hg b *
    Ψ (∏ i ∈ b, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) b m * H (g ∪ b)‖

theorem bigG_norm_le (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (g a b E : Finset ι) (k : O) :
    ‖bigG p hp hcop hg Ψ m f H g a b E k‖ ≤ bigGBound p hp hcop hg Ψ m f H g a b := by
  unfold bigG bigGBound
  rw [norm_mul, norm_mul, norm_star]
  have ha := physCoeff_norm_le p hp hcop hg Ψ m (fun A => H (g ∪ A)) (physRow p f g E k) a
  have hb := physCoeff_norm_le p hp hcop hg Ψ m (fun A => H (g ∪ A)) (physRow p f g E k) b
  have h0 := norm_nonneg (star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
    canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g * quadraticCrossPhase p hg a b *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a (-1))
  gcongr

include hp in
theorem kernelDen_pos (E a b : Finset ι) : 0 < kernelDen p E a b := by
  unfold kernelDen
  have h1 : primeSubsetGenerator (fun i => Ideal.span {p i}) E ≠ 0 :=
    primeSubsetGenerator_ne_zero _ E
  have h2 : (∏ i ∈ activeSupport a b, p i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i))
  have e1 := ConcreteTraceCRT.eisEmbedding_ne_zero h1
  have e2 := ConcreteTraceCRT.eisEmbedding_ne_zero h2
  positivity

theorem innerPair_summable (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (hY : 0 < Y) (g E a b : Finset ι) :
    Summable (fun k : O => innerPair p hp hcop hg Ψ m f H W Y g E k a b) := by
  have hK : 0 < Y / kernelDen p E a b := div_pos hY (kernelDen_pos p hp E a b)
  have hs := (EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W _ hK).mul_right
    (bigGBound p hp hcop hg Ψ m f H g a b /
      ‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖)
  apply Summable.of_norm_bounded hs
  intro k
  unfold innerPair
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  have hB := bigG_norm_le p hp hcop hg Ψ m f H g a b E k
  have harg : Y * ‖eisEmbedding k‖ ^ 2 / kernelDen p E a b =
      Y / kernelDen p E a b * ‖eisEmbedding k‖ ^ 2 := by ring
  rw [harg]
  have hn := norm_nonneg (paperRadialFourier W (Y / kernelDen p E a b * ‖eisEmbedding k‖ ^ 2))
  have hd := norm_nonneg (eisEmbedding (∏ i ∈ activeSupport a b, p i))
  calc ‖paperRadialFourier W (Y / kernelDen p E a b * ‖eisEmbedding k‖ ^ 2)‖ /
        ‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ * ‖bigG p hp hcop hg Ψ m f H g a b E k‖
      ≤ ‖paperRadialFourier W (Y / kernelDen p E a b * ‖eisEmbedding k‖ ^ 2)‖ /
        ‖eisEmbedding (∏ i ∈ activeSupport a b, p i)‖ * bigGBound p hp hcop hg Ψ m f H g a b :=
        mul_le_mul_of_nonneg_left hB (div_nonneg hn hd)
    _ = _ := by ring

theorem inner_summable (pool : Finset ι) (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (g E : Finset ι) :
    Summable (fun k : O => inner p hp hcop hg pool Ψ m f H W Y g E k) := by
  unfold inner
  apply summable_sum; intro a _
  apply summable_sum; intro b _
  by_cases hd : Disjoint a b
  · simp only [hd, if_true]; exact innerPair_summable p hp hcop hg Ψ m f H W Y hY g E a b
  · simp only [hd, if_false]; exact summable_zero

/-- The grouped sum as an `(E, k)` sum of residual pair sums. -/
theorem grouped_eq_inner (pool : Finset ι) (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (g : Finset ι) :
    (∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset,
      if Disjoint a b then groupedTerm p hp hcop hg Ψ m f H W Y g a b else 0) =
    ∑ E ∈ g.powerset,
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * Y /
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) *
      ∑' k : O, inner p hp hcop hg pool Ψ m f H W Y g E k := by
  have hterm : ∀ a b : Finset ι, groupedTerm p hp hcop hg Ψ m f H W Y g a b =
      ∑ E ∈ g.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * Y /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) *
        ∑' k : O, innerPair p hp hcop hg Ψ m f H W Y g E k a b := by
    intro a b
    unfold groupedTerm innerPair bigG kernelDen physRow
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E _
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    apply tsum_congr
    intro k
    ring
  have hite : ∀ a b : Finset ι, (if Disjoint a b then groupedTerm p hp hcop hg Ψ m f H W Y g a b
      else 0) = ∑ E ∈ g.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * Y /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) *
        ∑' k : O, (if Disjoint a b then innerPair p hp hcop hg Ψ m f H W Y g E k a b else 0) := by
    intro a b
    by_cases hd : Disjoint a b
    · simp only [hd, if_true]; exact hterm a b
    · simp [hd]
  simp_rw [hite]
  calc (∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset, ∑ E ∈ g.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * Y /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) *
        ∑' k : O, (if Disjoint a b then innerPair p hp hcop hg Ψ m f H W Y g E k a b else 0))
      = ∑ a ∈ (pool \ g).powerset, ∑ E ∈ g.powerset, ∑ b ∈ (pool \ g).powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * Y /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) *
        ∑' k : O, (if Disjoint a b then innerPair p hp hcop hg Ψ m f H W Y g E k a b else 0) := by
        apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm
    _ = ∑ E ∈ g.powerset, ∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * Y /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) *
        ∑' k : O, (if Disjoint a b then innerPair p hp hcop hg Ψ m f H W Y g E k a b else 0) :=
        Finset.sum_comm
    _ = _ := by
        apply Finset.sum_congr rfl
        intro E _
        simp only [← Finset.mul_sum]
        congr 1
        unfold inner
        have hs : ∀ a b : Finset ι, Summable (fun k : O =>
            if Disjoint a b then innerPair p hp hcop hg Ψ m f H W Y g E k a b else 0) := by
          intro a b
          by_cases hd : Disjoint a b
          · simp only [hd, if_true]; exact innerPair_summable p hp hcop hg Ψ m f H W Y hY g E a b
          · simp only [hd, if_false]; exact summable_zero
        rw [Summable.tsum_finsetSum (fun a _ => summable_sum (fun b _ => hs a b))]
        apply Finset.sum_congr rfl
        intro a _
        rw [Summable.tsum_finsetSum (fun b _ => hs a b)]

end
end Qrh.MarkedAnchor.Inverse.Poisson
