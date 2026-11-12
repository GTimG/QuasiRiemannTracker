/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.InnerSum
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.Counting

/-!
# Inverse.Poisson.Diag — the dual frequency `k = 0` (the direct diagonal)

At `k = 0` only the empty residual columns survive (`χ_a(0) = 0` for `a ≠ ∅`), so
`inner g E 0 = Ŵ(0) · D₀(g)` does not depend on `E`, and
`∑_{E ⊆ g} μ(E) Y/N e = Y ∏_{i ∈ g} (1 - 1/N p_i) ∈ [0, Y]`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnG quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius)
open OAI.FirstPassCubeLabels (primeProductNorm)

local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The diagonal coefficient `D₀(g)`. -/
def diagCoeff (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (g : Finset ι) : ℂ :=
  star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
    canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g *
    star (physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A)) 0 ∅) *
    physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A)) 0 ∅

theorem physCoeff_empty (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (y y' : O) :
    physCoeff p hp hcop hg Ψ m H y ∅ = physCoeff p hp hcop hg Ψ m H y' ∅ := by
  simp [physCoeff, finiteSquarefreeRow]

theorem physCoeff_zero_nonempty (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (A : Finset ι)
    (hA : A.Nonempty) : physCoeff p hp hcop hg Ψ m H 0 A = 0 := by
  unfold physCoeff
  rw [SecondPassArithmetic.finiteSquarefreeRow_zero_of_nonempty p hg A hA]
  simp

theorem inner_zero (pool : Finset ι) (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
    (Y : ℝ) (g E : Finset ι) :
    inner p hp hcop hg pool Ψ m f H W Y g E 0 =
      paperRadialFourier W 0 * diagCoeff p hp hcop hg Ψ m f H g := by
  have hrow : physRow p f g E 0 = 0 := by unfold physRow; ring
  unfold inner
  rw [Finset.sum_eq_single ∅, Finset.sum_eq_single ∅]
  · simp only [Finset.disjoint_empty_left, if_true]
    unfold innerPair bigG diagCoeff
    rw [hrow]
    simp [activeSupport, quadraticCrossPhase, finiteSquarefreeRow]
  · intro b _ hb
    have hbn : b.Nonempty := Finset.nonempty_iff_ne_empty.mpr hb
    split_ifs
    · unfold innerPair bigG
      rw [hrow, physCoeff_zero_nonempty p hp hcop hg Ψ m _ b hbn]
      simp
    · rfl
  · intro h; exact absurd (Finset.empty_mem_powerset _) h
  · intro a _ ha
    have han : a.Nonempty := Finset.nonempty_iff_ne_empty.mpr ha
    apply Finset.sum_eq_zero
    intro b _
    split_ifs
    · unfold innerPair bigG
      rw [hrow, physCoeff_zero_nonempty p hp hcop hg Ψ m _ a han]
      simp
    · rfl
  · intro h; exact absurd (Finset.empty_mem_powerset _) h

theorem gen_norm_sq (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 =
      primeProductNorm p E := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, primeSubsetGenerator,
    ConcretePrimeRowBridge.span_idealGenerator, primeProductNorm_eq_absNorm]
  rfl

theorem primeProductNorm_prod (E : Finset ι) :
    primeProductNorm p E = ∏ i ∈ E, primeProductNorm p {i} := by
  induction E using Finset.induction_on with
  | empty => simp [FirstPassCubeLabels.primeProductNorm]
  | @insert j E hj ih =>
    rw [Finset.prod_insert hj, Finset.insert_eq,
      FirstPassCubeLabels.primeProductNorm_union p {j} E (Finset.disjoint_singleton_left.mpr hj), ih]

include hp in
/-- `∑_{E ⊆ g} μ(E)/N e = ∏_{i ∈ g} (1 - 1/N p_i)`, a number in `[0, 1]`. -/
theorem mobius_density_bound (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (g : Finset ι) :
    ‖∑ E ∈ g.powerset,
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ))‖ ≤ 1 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  set x : ι → ℝ := fun i => primeProductNorm p {i} with hx
  have hterm : ∀ E ∈ g.powerset,
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) =
      ((∏ i ∈ E, (-(x i)⁻¹) : ℝ) : ℂ) := by
    intro E _
    rw [prime_product_moebius _ hprime hinj, gen_norm_sq, primeProductNorm_prod]
    have hneg : (∏ i ∈ E, (-(x i)⁻¹) : ℝ) = (-1) ^ E.card * ∏ i ∈ E, (x i)⁻¹ := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _; ring
    rw [hneg, Finset.prod_inv_distrib]
    push_cast
    rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum]
  have hsum : ∑ E ∈ g.powerset, ∏ i ∈ E, (-(x i)⁻¹) = ∏ i ∈ g, ((-(x i)⁻¹) + 1) := by
    rw [Finset.prod_add]; simp
  rw [hsum, Complex.norm_real, Real.norm_eq_abs]
  have hfac : ∀ i ∈ g, 0 ≤ -(x i)⁻¹ + 1 ∧ -(x i)⁻¹ + 1 ≤ 1 := by
    intro i _
    have h2 := one_le_primeProductNorm_single p hp i
    have h3 : (x i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by simp only [hx]; linarith)
    have h4 : 0 ≤ (x i)⁻¹ := by simp only [hx]; positivity
    constructor <;> linarith
  rw [abs_of_nonneg (Finset.prod_nonneg fun i hi => (hfac i hi).1)]
  exact Finset.prod_le_one₀ (fun i hi => (hfac i hi).1) (fun i hi => (hfac i hi).2)

end
end Qrh.MarkedAnchor.Inverse.Poisson
