/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.Grouping

/-!
# Inverse.Poisson.SideRow — one side of the projector as residual child rows

After the projector `a = t ∪ a'` (slots are assigned first to `g`, then to `t`, then to the
residual column), one side of the physical pair is

`∑_{a' ⊆ R\t} μ(t∪a') G(t∪a') ψ₀(t∪a') mask_{t∪a'}(m) conj χ_{t∪a'}(z) mark(g∪t∪a') F(N(t∪a'))/√N(t∪a')
   = ∑_θ ∑_{J ⊆ slots} gCoeff θ · mark_J(g∪t) · [t-scalars]/√Nt ·
       mobiusRowF (R\t) (rayMonoid θ * ψ₀) m (slots\J) (F(Nt ·)) z`,

with `G = columnG = ∑_θ gCoeff θ · ray_θ` (the primitive Gauss root as a fixed ray expansion), the
frozen marks `mark_J(g ∪ t)` and the residual marks on the ORIGINAL lists.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open MixedCrossSeparation (columnG)
open FirstCauchyArithmetic (supportMobius)
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.SecondPassArithmetic (rayMonoid)
open OAI.RayFourExpansion (RayCharacter rayCharacter gCoeff)

local notation "O" => ActualEisensteinCubic.O

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The physical Möbius row with a general norm profile `F` (conjugate row character). -/
def mobiusRowF (pool : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (F : ℝ → ℂ) (z : O) : ℂ :=
  ∑ A ∈ pool.powerset,
    supportMobius (fun i => Ideal.span {p i}) A * ψ (∏ i ∈ A, p i) *
      rowCoprimeMask (fun i => Ideal.span {p i}) A m *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A z) *
      primeMarkInj slots lists a A * F (primeProductNorm p A) *
      (((Real.sqrt (primeProductNorm p A))⁻¹ : ℝ) : ℂ)

theorem rayCharacter_prod_union (χ : RayCharacter) (A B : Finset ι) (hd : Disjoint A B) :
    rayCharacter χ (∏ i ∈ A ∪ B, p i) =
      rayCharacter χ (∏ i ∈ A, p i) * rayCharacter χ (∏ i ∈ B, p i) := by
  rw [Finset.prod_union hd, RayFourExpansion.rayCharacter_mul]

theorem supportMobius_union (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (A B : Finset ι) (hd : Disjoint A B) :
    supportMobius (fun i => Ideal.span {p i}) (A ∪ B) =
      supportMobius (fun i => Ideal.span {p i}) A * supportMobius (fun i => Ideal.span {p i}) B := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  simp only [supportMobius, prime_product_moebius _ hprime hinj, Finset.card_union_of_disjoint hd,
    pow_add]

include hp in
theorem sqrt_norm_union (A B : Finset ι) (hd : Disjoint A B) :
    (((Real.sqrt (primeProductNorm p (A ∪ B)))⁻¹ : ℝ) : ℂ) =
      (((Real.sqrt (primeProductNorm p A))⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt (primeProductNorm p B))⁻¹ : ℝ) : ℂ) := by
  rw [FirstPassCubeLabels.primeProductNorm_union p A B hd,
    Real.sqrt_mul (FirstPassCubeLabels.primeProductNorm_pos p hp A).le, mul_inv]
  push_cast
  ring

theorem side_expand (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (g t R : Finset ι) (ht : t ⊆ R) (hgR : Disjoint g R)
    (ψ₀ : O →* ℂ) (m z : O) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (F : ℝ → ℂ) :
    ∑ a' ∈ (R \ t).powerset,
      supportMobius (fun i => Ideal.span {p i}) (t ∪ a') * columnG p hp hcop hg (t ∪ a') *
        ψ₀ (∏ i ∈ t ∪ a', p i) * rowCoprimeMask (fun i => Ideal.span {p i}) (t ∪ a') m *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg (t ∪ a') z) *
        primeMarkInj slots lists a (g ∪ (t ∪ a')) * F (primeProductNorm p (t ∪ a')) *
        (((Real.sqrt (primeProductNorm p (t ∪ a')))⁻¹ : ℝ) : ℂ) =
    ∑ θ : RayCharacter, ∑ J ∈ slots.powerset,
      (gCoeff θ * primeMarkInj J lists a (g ∪ t) *
        (supportMobius (fun i => Ideal.span {p i}) t * rayCharacter θ (∏ i ∈ t, p i) *
          ψ₀ (∏ i ∈ t, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) t m *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg t z) *
          (((Real.sqrt (primeProductNorm p t))⁻¹ : ℝ) : ℂ))) *
      mobiusRowF p hg (R \ t) (rayMonoid θ * ψ₀) m (slots \ J) lists a
        (fun n => F (primeProductNorm p t * n)) z := by
  have hkey : ∀ a' ∈ (R \ t).powerset,
      supportMobius (fun i => Ideal.span {p i}) (t ∪ a') * columnG p hp hcop hg (t ∪ a') *
        ψ₀ (∏ i ∈ t ∪ a', p i) * rowCoprimeMask (fun i => Ideal.span {p i}) (t ∪ a') m *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg (t ∪ a') z) *
        primeMarkInj slots lists a (g ∪ (t ∪ a')) * F (primeProductNorm p (t ∪ a')) *
        (((Real.sqrt (primeProductNorm p (t ∪ a')))⁻¹ : ℝ) : ℂ) =
      ∑ θ : RayCharacter, ∑ J ∈ slots.powerset,
        (gCoeff θ * primeMarkInj J lists a (g ∪ t) *
          (supportMobius (fun i => Ideal.span {p i}) t * rayCharacter θ (∏ i ∈ t, p i) *
            ψ₀ (∏ i ∈ t, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) t m *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg t z) *
            (((Real.sqrt (primeProductNorm p t))⁻¹ : ℝ) : ℂ))) *
        (supportMobius (fun i => Ideal.span {p i}) a' * (rayMonoid θ * ψ₀) (∏ i ∈ a', p i) *
          rowCoprimeMask (fun i => Ideal.span {p i}) a' m *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a' z) *
          primeMarkInj (slots \ J) lists a a' * F (primeProductNorm p t * primeProductNorm p a') *
          (((Real.sqrt (primeProductNorm p a'))⁻¹ : ℝ) : ℂ)) := by
    intro a' ha'
    have ha'R : a' ⊆ R \ t := Finset.mem_powerset.mp ha'
    have hd : Disjoint t a' :=
      Finset.disjoint_of_subset_right ha'R Finset.disjoint_sdiff
    have hga : Disjoint (g ∪ t) a' := by
      rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_of_subset_right (ha'R.trans Finset.sdiff_subset) hgR, hd⟩
    have hmark := markInj_priority lists a slots (g ∪ t) a'
    rw [Finset.sdiff_eq_self_of_disjoint hga.symm, Finset.union_assoc] at hmark
    rw [supportMobius_union p hinj t a' hd,
      SecondPassArithmetic.columnG_eq_ray_sum p hp hcop hg hc hpr (t ∪ a'),
      Finset.prod_union hd, map_mul,
      FirstPassCubeLabels.mask_union (fun i => Ideal.span {p i}) hg t a' hd,
      FirstPassCubeLabels.row_union (fun i => Ideal.span {p i}) hg t a' hd, star_mul, hmark,
      sqrt_norm_union p hp t a' hd, FirstPassCubeLabels.primeProductNorm_union p t a' hd,
      ← Finset.prod_union hd]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro θ _
    apply Finset.sum_congr rfl
    intro J _
    rw [rayCharacter_prod_union p θ t a' hd]
    simp only [MonoidHom.mul_apply, SecondPassArithmetic.rayMonoid_apply, map_mul]
    ring
  rw [Finset.sum_congr rfl hkey, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  unfold mobiusRowF
  rw [Finset.mul_sum]

end
end Qrh.MarkedAnchor.Inverse.Poisson
