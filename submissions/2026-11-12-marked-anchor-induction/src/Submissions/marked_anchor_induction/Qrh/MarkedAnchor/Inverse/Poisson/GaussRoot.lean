/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.Phase
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CubicSieve.FirstPassage

/-!
# Inverse.Poisson.GaussRoot — one physical row and the Gauss root

For one off-diagonal pair of canonical columns `g ∪ a`, `g ∪ b` (`g, a, b` pairwise disjoint),
a divisor `e` of the common column `∏_g p = e g'`, and a dual frequency `h`, the canonical
coefficients (`γ2 · Ψ · mask · χ(f)^4 · H`) times the second-Poisson Gauss row factor equal

`|c_g|² · quadraticCrossPhase(a,b) · χ_a(-1) · conj P_a(y) · P_b(y)`,   `y = f² (e g') g' h`,

where `P_A(y) = μ(A) G(A) Ψ(A) mask_A(m) conj χ_A(y) H(g ∪ A)` and `G = columnG` is the
primitive Gauss root (`= ∑ gCoeff·ray`, a fixed ray character expansion): by the phase identity
(`Phase`), the primitive Gauss root times `conj(α)γ2` leaves `μ(a)` times a fixed finite ray
character. The coefficient of the physical row `y` depends on `(f, g, e, h)` only through the
outer scalar `|c_g|²` and the frozen `H(g ∪ ·)`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient columnG quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open SecondPassArithmetic (secondColumnMinus secondColumnPlus)

local notation "O" => ActualEisensteinCubic.O

theorem star_rowCoprimeMask {ι : Type*} (P : ι → Ideal O) (S : Finset ι) (u : O) :
    star (rowCoprimeMask P S u) = rowCoprimeMask P S u := by
  unfold rowCoprimeMask
  split_ifs <;> simp

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The canonical column coefficient without the Gauss-row character:
`secondChildColumn … f k H U = canonCoeff … f H U * χ_U(k)`. -/
def canonCoeff (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (U : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg U * Ψ (∏ i ∈ U, p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) U m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U f ^ 4 * H U

theorem secondChildColumn_eq (Ψ : O →* ℂ) (m f k : O) (H : Finset ι → ℂ) (U : Finset ι) :
    SecondPassArithmetic.secondChildColumn p hp hcop hg Ψ m f k H U =
      canonCoeff p hp hcop hg Ψ m f H U * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U k := by
  unfold SecondPassArithmetic.secondChildColumn canonCoeff
  ring

/-- The physical column coefficient at the physical row `y`. -/
def physCoeff (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (y : O) (A : Finset ι) : ℂ :=
  supportMobius (fun i => Ideal.span {p i}) A * columnG p hp hcop hg A * Ψ (∏ i ∈ A, p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) A m *
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A y) * H A

variable (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)

include hc hpr

omit hc in
theorem canonCoeff_union (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (g A : Finset ι)
    (hd : Disjoint A g) :
    canonCoeff p hp hcop hg Ψ m f H (g ∪ A) =
      canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g *
        (columnCoefficient p hp hcop hg A * Ψ (∏ i ∈ A, p i) *
          rowCoprimeMask (fun i => Ideal.span {p i}) A m *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A f ^ 4 *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (∏ k ∈ g, p k) ^ 4 *
          H (g ∪ A)) := by
  have hγ := FirstPassCubeLabels.columnCoefficient_union_row_four p hp hcop hg hpr A g hd
  rw [Finset.union_comm A g] at hγ
  unfold canonCoeff
  beta_reduce
  rw [hγ, Finset.prod_union hd.symm, map_mul,
    FirstPassCubeLabels.mask_union (fun i => Ideal.span {p i}) hg g A hd.symm,
    FirstPassCubeLabels.row_union (fun i => Ideal.span {p i}) hg g A hd.symm]
  ring

/-- The `b`-side (conjugated column of the restore lemma). -/
theorem minus_side (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (g b : Finset ι)
    (hd : Disjoint b g) (e g' h : O) (he : ∏ k ∈ g, p k = e * g') :
    star (secondColumnMinus p hp hcop hg
      (fun A => supportMobius (fun i => Ideal.span {p i}) A *
        star (canonCoeff p hp hcop hg Ψ m f H (g ∪ A))) e h b) =
      physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A)) (f ^ 2 * (e * g') * g' * h) b *
        canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g := by
  have hγ : star (columnCoefficient p hp hcop hg b) * columnCoefficient p hp hcop hg b = 1 := by
    rw [mul_comm]; exact SecondPassArithmetic.columnCoefficient_mul_star p hp hcop hg hc b
  have hph := phase_identity (fun i => Ideal.span {p i}) hg b f e g' h
  unfold secondColumnMinus
  beta_reduce
  rw [canonCoeff_union p hp hcop hg hpr Ψ m f H g b hd, he]
  unfold physCoeff
  rw [← hph]
  simp only [star_mul, star_star, star_pow, FirstCauchyArithmetic.star_supportMobius,
    star_rowCoprimeMask]
  calc _ = (star (columnCoefficient p hp hcop hg b) * columnCoefficient p hp hcop hg b) *
        (supportMobius (fun i => Ideal.span {p i}) b * columnG p hp hcop hg b *
          Ψ (∏ i ∈ b, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) b m *
          (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg b e *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg b h) *
            finiteSquarefreeRow (fun i => Ideal.span {p i}) hg b (e * g') ^ 4 *
            finiteSquarefreeRow (fun i => Ideal.span {p i}) hg b f ^ 4) * H (g ∪ b) *
          canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) := by ring
    _ = _ := by rw [hγ, one_mul]

/-- The `a`-side (plain column of the restore lemma). -/
theorem plus_side (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (g a : Finset ι)
    (hd : Disjoint a g) (e g' h : O) (he : ∏ k ∈ g, p k = e * g') :
    secondColumnPlus p hp hcop hg
      (fun A => supportMobius (fun i => Ideal.span {p i}) A *
        star (canonCoeff p hp hcop hg Ψ m f H (g ∪ A))) e h a =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a (-1) *
        star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
        star (physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A)) (f ^ 2 * (e * g') * g' * h) a) := by
  have hγ : columnCoefficient p hp hcop hg a * star (columnCoefficient p hp hcop hg a) = 1 :=
    SecondPassArithmetic.columnCoefficient_mul_star p hp hcop hg hc a
  have hph := phase_identity_conj (fun i => Ideal.span {p i}) hg a f e g' h
  unfold secondColumnPlus
  beta_reduce
  rw [canonCoeff_union p hp hcop hg hpr Ψ m f H g a hd, he]
  unfold physCoeff
  simp only [star_mul, star_star, star_pow, FirstCauchyArithmetic.star_supportMobius,
    star_rowCoprimeMask]
  rw [← hph]
  calc _ = (columnCoefficient p hp hcop hg a * star (columnCoefficient p hp hcop hg a)) *
        (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a (-1) *
          star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
          (supportMobius (fun i => Ideal.span {p i}) a * star (columnG p hp hcop hg a) *
            star (Ψ (∏ i ∈ a, p i)) * rowCoprimeMask (fun i => Ideal.span {p i}) a m *
            (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a e) *
              finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a h *
              star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a (e * g')) ^ 4 *
              star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a f) ^ 4) *
            star (H (g ∪ a)))) := by ring
    _ = _ := by rw [hγ]; ring

/-- One physical row (second Poisson, phase identity, Gauss root): the pair coefficient at the dual frequency
`h` and divisor `e | ∏_g p` is an outer `|c_g|²` times the quadratic cross phase times
`χ_a(-1) conj P_a(y) P_b(y)` at the single physical row `y = f² (e g') g' h`. -/
theorem pair_gauss_identity
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ) (g a b : Finset ι)
    (hga : Disjoint a g) (hgb : Disjoint b g) (hab : Disjoint a b)
    (e g' h : O) (he : ∏ k ∈ g, p k = e * g') :
    star (canonCoeff p hp hcop hg Ψ m f H (g ∪ a)) * canonCoeff p hp hcop hg Ψ m f H (g ∪ b) *
        activeGaussRowFactor p hp hinj hg a b e h =
      star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
        canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g *
        quadraticCrossPhase p hg a b * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a (-1) *
        star (physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A)) (f ^ 2 * (e * g') * g' * h) a) *
        physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A)) (f ^ 2 * (e * g') * g' * h) b := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  set C : Finset ι → ℂ := fun A => supportMobius (fun i => Ideal.span {p i}) A *
    star (canonCoeff p hp hcop hg Ψ m f H (g ∪ A)) with hC
  have hμ (A : Finset ι) := FirstCauchyArithmetic.supportMobius_sq _ hprime hinj A
  have hL : star (canonCoeff p hp hcop hg Ψ m f H (g ∪ a)) *
      canonCoeff p hp hcop hg Ψ m f H (g ∪ b) =
      star (supportMobius (fun i => Ideal.span {p i}) b * C b) *
        (supportMobius (fun i => Ideal.span {p i}) a * C a) := by
    simp only [hC, star_mul, star_star, FirstCauchyArithmetic.star_supportMobius]
    calc _ = (supportMobius (fun i => Ideal.span {p i}) b *
          supportMobius (fun i => Ideal.span {p i}) b) *
          (supportMobius (fun i => Ideal.span {p i}) a *
            supportMobius (fun i => Ideal.span {p i}) a) *
          (star (canonCoeff p hp hcop hg Ψ m f H (g ∪ a)) *
            canonCoeff p hp hcop hg Ψ m f H (g ∪ b)) := by rw [hμ, hμ]; ring
      _ = _ := by ring
  rw [hL, SecondPassArithmetic.mobius_second_gauss_restore p hp hinj hcop hg hc hpr b a
    hab.symm C C e h, minus_side p hp hcop hg hc hpr Ψ m f H g b hgb e g' h he,
    plus_side p hp hcop hg hc hpr Ψ m f H g a hga e g' h he]
  ring

end
end Qrh.MarkedAnchor.Inverse.Poisson
