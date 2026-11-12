/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.InnerSum
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.ChildRow
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.Bilinear

/-!
# Inverse.Poisson.PairSep — the kernel separation inside the residual pair sum

For fixed `(g, E, k)` with Poisson parameter `R = Y‖k‖² (N g)²/(N e X²)` and a separating
coefficient `b` for `Ŵ` (`radial_kernel_separation_pointwise`), the residual pair sum is

`inner g E k = Q_g ∫ b(t) · ∑_{a,b disjoint} QCP(a,b) χ_a(-1) conj α_t(a) β_t(b) dt`,

`α_t(A) = core(A) W(x_A) e(s₀+t, log x_A)/√N A`, `β_t(B) = core(B) W(x_B) e(s₀-t, log x_B)/√N B`,
`x_A = N g N A / X`, `core(A) = μ(A) G(A) Ψ(A) mask_A(m) conj χ_A(y) mark(g ∪ A)`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnG quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius)
open OAI.FirstPassCubeLabels (primeProductNorm)
open FourierBridge (logPhase)

local notation "O" => ActualEisensteinCubic.O

theorem logPhase_neg_arg (t u : ℝ) : logPhase t (-u) = star (logPhase t u) := by
  unfold logPhase
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem star_ofReal' (r : ℝ) : star ((r : ℂ)) = (r : ℂ) := Complex.conj_ofReal r

theorem logPhase_neg_freq (t u : ℝ) : logPhase t (-u) = logPhase (-t) u := by
  unfold logPhase
  congr 1
  push_cast
  ring

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The column core at the row `y`. -/
def colCore (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (g : Finset ι) (y : O) (A : Finset ι) : ℂ :=
  supportMobius (fun i => Ideal.span {p i}) A * columnG p hp hcop hg A * Ψ (∏ i ∈ A, p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) A m *
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A y) * primeMarkInj slots lists a (g ∪ A)

/-- The normalized column variable `x_A = N g · N A / X`. -/
def colX (g A : Finset ι) (X : ℝ) : ℝ := primeProductNorm p g * primeProductNorm p A / X

/-- The separated column vector at height `h`. -/
def sepCol (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (g : Finset ι) (X : ℝ) (y : O) (h : ℝ) (A : Finset ι) : ℂ :=
  colCore p hp hcop hg Ψ m slots lists a g y A *
    (W (colX p g A X) * logPhase h (Real.log (colX p g A X))) *
    (((Real.sqrt (primeProductNorm p A))⁻¹ : ℝ) : ℂ)

/-- The canonical row profile of `Entry`. -/
def entryH (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (s₀ X : ℝ)
    (U : Finset ι) : ℂ :=
  primeMarkInj slots lists a U * childLogTest W s₀ (primeProductNorm p U / X)

theorem physCoeff_eq_core (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (W : ℝ → ℂ) (s₀ X : ℝ) (g A : Finset ι) (hgA : Disjoint g A) (y : O) :
    physCoeff p hp hcop hg Ψ m (fun U => entryH p slots lists a W s₀ X (g ∪ U)) y A =
      colCore p hp hcop hg Ψ m slots lists a g y A *
        (W (colX p g A X) * logPhase s₀ (Real.log (colX p g A X))) := by
  simp only [physCoeff, colCore, colX, entryH, childLogTest]
  rw [FirstPassCubeLabels.primeProductNorm_union p g A hgA]
  ring

theorem activeSupport_disjoint (A B : Finset ι) (hd : Disjoint A B) :
    activeSupport A B = A ∪ B := by
  unfold activeSupport
  rw [Finset.sdiff_eq_self_of_disjoint hd, Finset.sdiff_eq_self_of_disjoint hd.symm]

include hp in
theorem norm_eis_active (A B : Finset ι) (hd : Disjoint A B) :
    ‖eisEmbedding (∏ i ∈ activeSupport A B, p i)‖ =
      Real.sqrt (primeProductNorm p A) * Real.sqrt (primeProductNorm p B) := by
  rw [activeSupport_disjoint A B hd, ← Real.sqrt_mul (FirstPassCubeLabels.primeProductNorm_pos p hp A).le,
    ← FirstPassCubeLabels.primeProductNorm_union p A B hd, FirstPassCubeLabels.primeProductNorm,
    Real.sqrt_sq (norm_nonneg _)]

/-- The separation hypothesis for the radial kernel at one Poisson parameter `R`. -/
def KernelSep (Wk : 𝓢(ℝ, ℂ)) (W : ℝ → ℂ) (R : ℝ) (b : ℝ → ℂ) : Prop :=
  ∀ y : Fin 2 → ℝ,
    (∏ j : Fin 2, (![fun z => star (W (Real.exp z)), fun z => W (Real.exp z)] : Fin 2 → ℝ → ℂ)
        j (y j)) * paperRadialFourier Wk (R * Real.exp (∑ j : Fin 2, (fun _ => (-1 : ℝ)) j * y j)) =
      ∫ t : ℝ, (∏ j : Fin 2,
        (![fun z => star (W (Real.exp z)), fun z => W (Real.exp z)] : Fin 2 → ℝ → ℂ) j (y j) *
          logPhase t ((fun _ => (-1 : ℝ)) j * y j)) * b t

theorem pair_kernel_identity (Wk : 𝓢(ℝ, ℂ)) (W : ℝ → ℂ) (R : ℝ) (b : ℝ → ℂ)
    (hb : KernelSep Wk W R b) (xa xb s₀ : ℝ) (hxa : 0 < xa) (hxb : 0 < xb) :
    star (W xa * logPhase s₀ (Real.log xa)) * (W xb * logPhase s₀ (Real.log xb)) *
        paperRadialFourier Wk (R / (xa * xb)) =
      ∫ t : ℝ, b t * (star (W xa * logPhase (s₀ + t) (Real.log xa)) *
        (W xb * logPhase (s₀ - t) (Real.log xb))) := by
  have h := hb ![Real.log xa, Real.log xb]
  simp only [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Real.exp_log hxa, Real.exp_log hxb] at h
  have harg : R * Real.exp (-1 * Real.log xa + -1 * Real.log xb) = R / (xa * xb) := by
    rw [show -1 * Real.log xa + -1 * Real.log xb = -(Real.log xa + Real.log xb) by ring,
      Real.exp_neg, ← Real.log_mul hxa.ne' hxb.ne', Real.exp_log (mul_pos hxa hxb)]
    ring
  rw [harg] at h
  calc star (W xa * logPhase s₀ (Real.log xa)) * (W xb * logPhase s₀ (Real.log xb)) *
        paperRadialFourier Wk (R / (xa * xb))
      = (star (logPhase s₀ (Real.log xa)) * logPhase s₀ (Real.log xb)) *
        (star (W xa) * W xb * paperRadialFourier Wk (R / (xa * xb))) := by
        rw [star_mul]; ring
    _ = (star (logPhase s₀ (Real.log xa)) * logPhase s₀ (Real.log xb)) *
        ∫ t : ℝ, star (W xa) * logPhase t (-1 * Real.log xa) *
          (W xb * logPhase t (-1 * Real.log xb)) * b t := by rw [h]
    _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        simp only [neg_one_mul]
        rw [logPhase_neg_arg, show logPhase t (-Real.log xb) = logPhase (-t) (Real.log xb) from
          logPhase_neg_freq t _, star_mul, show s₀ - t = s₀ + -t by ring,
          logPhase_add_freq, logPhase_add_freq, star_mul]
        ring

/-- The Poisson parameter `R = Y‖k‖² (N g)²/(N e X²)`. -/
def poissonR (Y X : ℝ) (g E : Finset ι) (k : O) : ℝ :=
  Y * ‖eisEmbedding k‖ ^ 2 * primeProductNorm p g ^ 2 /
    (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 * X ^ 2)

/-- The separated residual bilinear form at the kernel height `t`. -/
def sepBil (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (W : ℝ → ℂ) (g : Finset ι) (X s₀ : ℝ) (y : O) (t : ℝ) : ℂ :=
  ∑ A ∈ (pool \ g).powerset, ∑ B ∈ (pool \ g).powerset,
    if Disjoint A B then quadraticCrossPhase p hg A B *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) *
      star (sepCol p hp hcop hg Ψ m slots lists a W g X y (s₀ + t) A) *
      sepCol p hp hcop hg Ψ m slots lists a W g X y (s₀ - t) B else 0

set_option maxHeartbeats 800000 in
theorem innerPair_sep (Ψ : O →* ℂ) (m f : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (W : ℝ → ℂ) (Wk : 𝓢(ℝ, ℂ)) (Y X s₀ : ℝ) (hX : 0 < X)
    (g E : Finset ι) (k : O) (b : ℝ → ℂ)
    (hb : KernelSep Wk W (poissonR p Y X g E k) b)
    (A B : Finset ι) (hgA : Disjoint g A) (hgB : Disjoint g B) (hAB : Disjoint A B) :
    innerPair p hp hcop hg Ψ m f (entryH p slots lists a W s₀ X) Wk Y g E k A B =
      (star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
        canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
      ∫ t : ℝ, b t * (quadraticCrossPhase p hg A B *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) *
        star (sepCol p hp hcop hg Ψ m slots lists a W g X (physRow p f g E k) (s₀ + t) A) *
        sepCol p hp hcop hg Ψ m slots lists a W g X (physRow p f g E k) (s₀ - t) B) := by
  have hNg := FirstPassCubeLabels.primeProductNorm_pos p hp g
  have hNA := FirstPassCubeLabels.primeProductNorm_pos p hp A
  have hNB := FirstPassCubeLabels.primeProductNorm_pos p hp B
  have hxa : 0 < colX p g A X := by unfold colX; positivity
  have hxb : 0 < colX p g B X := by unfold colX; positivity
  have he : 0 < ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ :=
    norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero _ E))
  have hkey := pair_kernel_identity Wk W (poissonR p Y X g E k) b hb
    (colX p g A X) (colX p g B X) s₀ hxa hxb
  have harg : Y * ‖eisEmbedding k‖ ^ 2 / kernelDen p E A B =
      poissonR p Y X g E k / (colX p g A X * colX p g B X) := by
    unfold kernelDen poissonR colX
    rw [norm_eis_active p hp A B hAB, mul_pow, Real.sq_sqrt hNA.le, Real.sq_sqrt hNB.le]
    field_simp
  have hn : (‖eisEmbedding (∏ i ∈ activeSupport A B, p i)‖ : ℂ) =
      ((Real.sqrt (primeProductNorm p A) : ℝ) : ℂ) * ((Real.sqrt (primeProductNorm p B) : ℝ) : ℂ) := by
    rw [norm_eis_active p hp A B hAB]; push_cast; ring
  unfold innerPair bigG
  rw [physCoeff_eq_core p hp hcop hg Ψ m slots lists a W s₀ X g A hgA,
    physCoeff_eq_core p hp hcop hg Ψ m slots lists a W s₀ X g B hgB, harg, hn]
  unfold sepCol
  have hsA : (Real.sqrt (primeProductNorm p A)) ≠ 0 := (Real.sqrt_pos.mpr hNA).ne'
  have hsB : (Real.sqrt (primeProductNorm p B)) ≠ 0 := (Real.sqrt_pos.mpr hNB).ne'
  calc paperRadialFourier Wk (poissonR p Y X g E k / (colX p g A X * colX p g B X)) /
        (((Real.sqrt (primeProductNorm p A) : ℝ) : ℂ) *
          ((Real.sqrt (primeProductNorm p B) : ℝ) : ℂ)) *
      (star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
        canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g * quadraticCrossPhase p hg A B *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) *
        star (colCore p hp hcop hg Ψ m slots lists a g (physRow p f g E k) A *
          (W (colX p g A X) * logPhase s₀ (Real.log (colX p g A X)))) *
        (colCore p hp hcop hg Ψ m slots lists a g (physRow p f g E k) B *
          (W (colX p g B X) * logPhase s₀ (Real.log (colX p g B X)))))
      = (star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
          canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
        ((quadraticCrossPhase p hg A B * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1) *
          star (colCore p hp hcop hg Ψ m slots lists a g (physRow p f g E k) A *
            (((Real.sqrt (primeProductNorm p A))⁻¹ : ℝ) : ℂ)) *
          (colCore p hp hcop hg Ψ m slots lists a g (physRow p f g E k) B *
            (((Real.sqrt (primeProductNorm p B))⁻¹ : ℝ) : ℂ))) *
        (star (W (colX p g A X) * logPhase s₀ (Real.log (colX p g A X))) *
          (W (colX p g B X) * logPhase s₀ (Real.log (colX p g B X))) *
          paperRadialFourier Wk (poissonR p Y X g E k / (colX p g A X * colX p g B X)))) := by
        simp only [star_mul, star_ofReal']
        push_cast
        ring
    _ = _ := by
        rw [hkey, ← integral_const_mul, ← integral_const_mul]
        conv_rhs => rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        simp only [star_mul]
        ring

end
end Qrh.MarkedAnchor.Inverse.Poisson
