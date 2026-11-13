/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Interface

/-!
# Inverse.Restore.Orient — the negative orientation by conjugation

The row symbol `finiteSquarefreeRow` is sextic, so `star χ_A(y)` is not a row symbol at a row of
the same norm. Instead the whole negative row is conjugated: it is the conjugate of the POSITIVE
row for the conjugated twist `conjHom ψ`, coefficients `star a` and profile `star Φ`; hence the
two child moments coincide.

* `conjHom ψ` — `ψ` followed by complex conjugation.
* `primeMark_star` — `star (primeMark I L (star a) A) = primeMark I L a A`.
* `mobiusChildRow_negative` — `row(ψ, a, Φ, negative) = star (row(conj ψ, star a, star Φ, positive))`.
* `mobiusChildSum_negative` — equality of the child moments.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.FirstCauchyArithmetic (supportMobius)
open Qrh.MarkedAnchor.Inverse.Poisson

local notation "O" => ActualEisensteinCubic.O

/-- `ψ` followed by complex conjugation. -/
def conjHom (ψ : O →* ℂ) : O →* ℂ := (starRingEnd ℂ).toMonoidHom.comp ψ

@[simp] theorem conjHom_apply (ψ : O →* ℂ) (x : O) : conjHom ψ x = star (ψ x) := rfl

theorem conjHom_conjHom (ψ : O →* ℂ) : conjHom (conjHom ψ) = ψ := by
  ext x; simp

theorem norm_conjHom (ψ : O →* ℂ) (x : O) : ‖conjHom ψ x‖ = ‖ψ x‖ := by
  simp

theorem primeMark_star {ι σ : Type} [DecidableEq ι] (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    star (primeMark I L (fun i j => star (a i j)) A) = primeMark I L a A := by
  unfold primeMark primeSlot
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp

theorem supportMobius_star {ι : Type} (P : ι → Ideal O) (S : Finset ι) :
    star (supportMobius P S) = supportMobius P S := by
  unfold supportMobius
  simp

theorem rowCoprimeMask_star {ι : Type} (P : ι → Ideal O) (S : Finset ι) (u : O) :
    star (rowCoprimeMask P S u) =
      rowCoprimeMask P S u := by
  unfold rowCoprimeMask
  split_ifs <;> simp

theorem ofReal_star' (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The negative row is the conjugate of the positive row of the conjugated data. -/
theorem mobiusChildRow_negative {ι σ : Type} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (Xc : ℝ) (y : O) :
    mobiusChildRow p hg pool ψ m slots lists a Φ Xc true y =
      star (mobiusChildRow p hg pool (conjHom ψ) m slots lists (fun i j => star (a i j))
        (fun x => star (Φ x)) Xc false y) := by
  unfold mobiusChildRow
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [if_true, Bool.false_eq_true, if_false, star_mul', conjHom_apply, star_star,
    supportMobius_star, rowCoprimeMask_star, primeMark_star, ofReal_star']

theorem mobiusChildSum_negative {ι σ : Type} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (Xc Z Hc : ℝ) :
    mobiusChildSum p hg pool ψ m slots lists a Φ Xc true Z Hc =
      mobiusChildSum p hg pool (conjHom ψ) m slots lists (fun i j => star (a i j))
        (fun x => star (Φ x)) Xc false Z Hc := by
  unfold mobiusChildSum
  apply Finset.sum_congr rfl
  intro y _
  rw [mobiusChildRow_negative, norm_star]

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.mobiusChildSum_negative
