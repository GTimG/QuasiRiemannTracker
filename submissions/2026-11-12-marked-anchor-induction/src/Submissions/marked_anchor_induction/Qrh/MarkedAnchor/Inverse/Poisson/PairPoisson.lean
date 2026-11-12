/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.Statement
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CubicSieve.SecondPoisson

/-!
# Inverse.Poisson.PairPoisson — expansion of the squared column and the second Poisson

Expand the squared column, write its two squarefree columns as `ga, gb` with `g, a, b` pairwise
coprime, and take `d | g` from the row mask. For a smooth radial weight `w` on the Gauss rows `k`:

`∑'_k w(‖k‖²/Y) |∑_{U ⊆ pool} c_U χ_U(k)|²
   = ∑_{U₁,U₂} conj c_{U₁} c_{U₂} · (Y/√(N a N b)) ∑_{E ⊆ g} μ(E)/N e ∑'_h Ŵ(Y‖h‖²/(N e N a N b))
       · activeGaussRowFactor a b e h`

with `g = U₁ ∩ U₂`, `a = U₁ \ U₂`, `b = U₂ \ U₁` (pairwise disjoint), `e` the generator of
`d = ∏_E`. This is `finiteSquarefreeRow_smoothed_mean_square_expand` followed by
`masked_pair_second_poisson (M := g) (T := a) (S := b)` for every pair.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (activeGaussRowFactor)

local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

/-- The dual (second Poisson) form of one column pair `(U₁, U₂)`. -/
def pairDual (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (U₁ U₂ : Finset ι) : ℂ :=
  let n := ∏ i : activeSupport (U₁ \ U₂) (U₂ \ U₁), p i.val
  ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (U₁ ∩ U₂).powerset,
      let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
        (‖eisEmbedding e‖ ^ 2 : ℝ)) *
        ∑' k : O, paperRadialFourier W
          (Y * ‖eisEmbedding k‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
            activeGaussRowFactor p hp hinj hg (U₁ \ U₂) (U₂ \ U₁) e k

include hc in
/-- Second Poisson for one pair of squarefree columns. -/
theorem pair_kernel_poisson (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (U₁ U₂ : Finset ι) :
    (∑' k : O, (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U₁ k) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U₂ k) *
        W (‖eisEmbedding k‖ ^ 2 / Y)) =
      pairDual p hp hinj hg W Y U₁ U₂ := by
  have hd : Disjoint (U₂ \ U₁) (U₁ \ U₂) := disjoint_sdiff_sdiff
  have h := SecondPassArithmetic.masked_pair_second_poisson p hp hinj hg hc
    (U₁ ∩ U₂) (U₂ \ U₁) (U₁ \ U₂) hd W Y hY
  dsimp only at h
  rw [pairDual, ← h]
  apply tsum_congr
  intro k
  have hk : star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U₁ k) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U₂ k =
      rowCoprimeMask (fun i => Ideal.span {p i}) (U₁ ∩ U₂) k *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg (U₁ \ U₂) k) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg (U₂ \ U₁) k :=
    finiteSquarefreeRow_pair_kernel (fun i => Ideal.span {p i}) hg U₁ U₂ k
  rw [hk]
  ring

include hc in
/-- Expansion of the smoothed squared column and the second Poisson for every pair. -/
theorem smoothed_column_poisson (pool : Finset ι) (c : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' k : O, W (‖eisEmbedding k‖ ^ 2 / Y) *
      (↑(‖∑ U ∈ pool.powerset, c U *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U k‖ ^ 2) : ℂ)) =
      ∑ U₁ ∈ pool.powerset, ∑ U₂ ∈ pool.powerset, (star (c U₁) * c U₂) *
        pairDual p hp hinj hg W Y U₁ U₂ := by
  have hx := finiteSquarefreeRow_smoothed_mean_square_expand (fun i => Ideal.span {p i}) hg
    pool.powerset id c W Y hY
  simp only [id] at hx
  rw [hx]
  apply Finset.sum_congr rfl
  intro U₁ _
  apply Finset.sum_congr rfl
  intro U₂ _
  rw [pair_kernel_poisson p hp hinj hg hc W Y hY U₁ U₂]

end
end Qrh.MarkedAnchor.Inverse.Poisson
