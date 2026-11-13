/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.FDecomp

/-!
# Inverse.Poisson.Norms — trivial coefficient bounds

`‖columnG A‖ ≤ Gs = ∑_θ |gCoeff θ|`, `‖canonCoeff g‖ ≤ 1`, `‖quadraticCrossPhase‖ ≤ 1`,
`bigGBound g a b ≤ Gs² ‖H(g∪a)‖ ‖H(g∪b)‖`, `‖D₀(g)‖ ≤ Gs² ‖H g‖²`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient columnG quadraticCrossPhase crossSymbol)
open FirstCauchyArithmetic (supportMobius)
open OAI.RayFourExpansion (RayCharacter rayCharacter gCoeff)

local notation "O" => ActualEisensteinCubic.O

/-- The Gauss-root constant. -/
def gSum : ℝ := ∑ θ : RayCharacter, ‖gCoeff θ‖

theorem gSum_nonneg : 0 ≤ gSum := Finset.sum_nonneg fun θ _ => norm_nonneg _

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem mask_norm_le' (S : Finset ι) (u : O) :
    ‖rowCoprimeMask (fun i => Ideal.span {p i}) S u‖ ≤ 1 := by
  unfold rowCoprimeMask
  split_ifs <;> simp

theorem mobius_norm' (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (A : Finset ι) : ‖supportMobius (fun i => Ideal.span {p i}) A‖ = 1 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  simp only [supportMobius, prime_product_moebius _ hprime hinj, norm_pow, norm_neg, norm_one,
    one_pow]

theorem columnG_norm_le (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (A : Finset ι) :
    ‖columnG p hp hcop hg A‖ ≤ gSum := by
  rw [SecondPassArithmetic.columnG_eq_ray_sum p hp hcop hg hc hpr A]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun θ _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (FiniteRayExpansion.norm_char_le_one θ _)

theorem quadraticCrossPhase_norm_le (A B : Finset ι) : ‖quadraticCrossPhase p hg A B‖ ≤ 1 := by
  unfold quadraticCrossPhase
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
  intro i _
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun k _ => norm_nonneg _)
  intro k _
  rw [norm_mul, norm_pow, norm_pow]
  have h1 : ‖crossSymbol p hg i k‖ ≤ 1 := FiniteRayExpansion.norm_char_le_one _ _
  have h2 : ‖crossSymbol p hg k i‖ ≤ 1 := FiniteRayExpansion.norm_char_le_one _ _
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) h1) (by positivity) (pow_le_one₀ (norm_nonneg _) h2)

theorem canonCoeff_one_norm_le (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m f : O) (g : Finset ι) :
    ‖canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g‖ ≤ 1 := by
  unfold canonCoeff
  rw [norm_mul, norm_mul, norm_mul, norm_mul,
    SecondPassArithmetic.columnCoefficient_norm_one p hp hcop hg hc g, norm_one, mul_one, one_mul,
    norm_pow]
  have h1 := hΨ (∏ i ∈ g, p i)
  have h2 := mask_norm_le' p g m
  have h3 := finiteSquarefreeRow_norm_le_one (fun i => Ideal.span {p i}) hg g f
  calc ‖Ψ (∏ i ∈ g, p i)‖ * ‖rowCoprimeMask (fun i => Ideal.span {p i}) g m‖ *
        ‖finiteSquarefreeRow (fun i => Ideal.span {p i}) hg g f‖ ^ 4
      ≤ 1 * 1 * 1 ^ 4 := by gcongr
    _ = 1 := by ring

theorem rowNegOne_norm_le (A : Finset ι) :
    ‖finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A (-1)‖ ≤ 1 :=
  finiteSquarefreeRow_norm_le_one _ hg A _

theorem physCore_norm_le (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m : O) (x : ℂ)
    (A : Finset ι) :
    ‖supportMobius (fun i => Ideal.span {p i}) A * columnG p hp hcop hg A *
      Ψ (∏ i ∈ A, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) A m * x‖ ≤ gSum * ‖x‖ := by
  rw [norm_mul, norm_mul, norm_mul, norm_mul, mobius_norm' p hinj, one_mul]
  have h1 := columnG_norm_le p hp hcop hg hc hpr A
  have h2 := hΨ (∏ i ∈ A, p i)
  have h3 := mask_norm_le' p A m
  have hG := gSum_nonneg
  calc ‖columnG p hp hcop hg A‖ * ‖Ψ (∏ i ∈ A, p i)‖ *
        ‖rowCoprimeMask (fun i => Ideal.span {p i}) A m‖ * ‖x‖
      ≤ gSum * 1 * 1 * ‖x‖ := by gcongr
    _ = gSum * ‖x‖ := by ring

theorem bigGBound_le (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m f : O)
    (H : Finset ι → ℂ) (g a b : Finset ι) :
    bigGBound p hp hcop hg Ψ m f H g a b ≤ gSum ^ 2 * (‖H (g ∪ a)‖ * ‖H (g ∪ b)‖) := by
  unfold bigGBound
  have hQ : ‖star (canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g) *
      canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g * quadraticCrossPhase p hg a b *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a (-1)‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_mul, norm_star]
    have h1 := canonCoeff_one_norm_le p hp hcop hg hc Ψ hΨ m f g
    have h2 := quadraticCrossPhase_norm_le p hg a b
    have h3 := rowNegOne_norm_le p hg a
    calc ‖canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g‖ *
          ‖canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g‖ * ‖quadraticCrossPhase p hg a b‖ *
          ‖finiteSquarefreeRow (fun i => Ideal.span {p i}) hg a (-1)‖ ≤ 1 * 1 * 1 * 1 := by
          gcongr
      _ = 1 := by ring
  have hA := physCore_norm_le p hp hcop hg hinj hc hpr Ψ hΨ m (H (g ∪ a)) a
  have hB := physCore_norm_le p hp hcop hg hinj hc hpr Ψ hΨ m (H (g ∪ b)) b
  have hG := gSum_nonneg
  calc _ ≤ 1 * (gSum * ‖H (g ∪ a)‖) * (gSum * ‖H (g ∪ b)‖) := by gcongr
    _ = _ := by ring

theorem diagCoeff_norm_le (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m f : O)
    (H : Finset ι → ℂ) (g : Finset ι) :
    ‖diagCoeff p hp hcop hg Ψ m f H g‖ ≤ gSum ^ 2 * ‖H g‖ ^ 2 := by
  unfold diagCoeff
  have hP : ‖physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A)) 0 ∅‖ ≤ gSum * ‖H g‖ := by
    have := physCoeff_norm_le p hp hcop hg Ψ m (fun A => H (g ∪ A)) 0 ∅
    refine this.trans ?_
    have h := physCore_norm_le p hp hcop hg hinj hc hpr Ψ hΨ m (H (g ∪ ∅)) ∅
    simpa using h
  have h1 := canonCoeff_one_norm_le p hp hcop hg hc Ψ hΨ m f g
  rw [norm_mul, norm_mul, norm_mul, norm_star, norm_star]
  have hG := gSum_nonneg
  calc ‖canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g‖ *
        ‖canonCoeff p hp hcop hg Ψ m f (fun _ => 1) g‖ *
        ‖physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A)) 0 ∅‖ *
        ‖physCoeff p hp hcop hg Ψ m (fun A => H (g ∪ A)) 0 ∅‖
      ≤ 1 * 1 * (gSum * ‖H g‖) * (gSum * ‖H g‖) := by gcongr
    _ = _ := by ring

end
end Qrh.MarkedAnchor.Inverse.Poisson
