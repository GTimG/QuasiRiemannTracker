/- Copyright (c) 2026 Sil. Apache-2.0.
Literal sextic sieve interface and elementary proved facts.
This file only defines `OptimalBound`; its unconditional proof is supplied
by Candidate.FourthPower.SieveOptimal.optimal_bound. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.PositiveFamily
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
namespace Candidate.FourthPower.SexticSieve
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss
open CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def PowerFree (n : ℕ) (I : Id) : Prop := ∀ P : Id, Prime P → ¬P^n ∣ I

def coefficientMass (columns : Finset Id) (a : Id → ℂ) : ℝ :=
  ∑ I ∈ columns, ‖a I‖^2

def rowValue (row column : Id) : ℂ := idealRowHom (primaryGenerator row) column

def energy (rows columns : Finset Id) (a : Id → ℂ) : ℝ :=
  ∑ R ∈ rows, ‖∑ I ∈ columns, a I * rowValue R I‖^2

def majorant (A B : ℝ) : ℝ :=
  A + B + A^(5/6 : ℝ)*B^(1/3 : ℝ) + A^(1/3 : ℝ)*B^(5/6 : ℝ)

/-- The exact sieve interface. All coefficients are common to the row family,
both ideal families are sixth-power-free, and constants precede all ranges. -/
def OptimalBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
  ∀ (A B : ℝ), 1 ≤ A → 1 ≤ B →
  ∀ rows columns : Finset Id,
  (∀ R ∈ rows, Supported R ∧ PowerFree 6 R ∧ (Ideal.absNorm R : ℝ) ≤ A) →
  (∀ I ∈ columns, Supported I ∧ PowerFree 6 I ∧ (Ideal.absNorm I : ℝ) ≤ B) →
  ∀ a : Id → ℂ, energy rows columns a ≤
    C*(A*B)^ε*majorant A B*coefficientMass columns a

theorem coefficientMass_nonneg (columns : Finset Id) (a : Id → ℂ) :
    0 ≤ coefficientMass columns a := Finset.sum_nonneg (fun I _ => sq_nonneg _)

theorem energy_nonneg (rows columns : Finset Id) (a : Id → ℂ) :
    0 ≤ energy rows columns a := Finset.sum_nonneg (fun R _ => sq_nonneg _)

theorem energy_rows_mono {rows rows' columns : Finset Id} (hrows : rows ⊆ rows')
    (a : Id → ℂ) : energy rows columns a ≤ energy rows' columns a := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hrows (fun R _ _ => sq_nonneg _)

theorem powerFree_mono {n m : ℕ} (hnm : n ≤ m) {I : Id} (hI : PowerFree n I) :
    PowerFree m I := by
  intro P hP hd
  exact hI P hP ((pow_dvd_pow P hnm).trans hd)

theorem trivial_bound (rows columns : Finset Id) (a : Id → ℂ) :
    energy rows columns a ≤ (rows.card : ℝ) * columns.card * coefficientMass columns a := by
  have hrow (R : Id) : ‖∑ I ∈ columns, a I * rowValue R I‖^2 ≤
      (columns.card : ℝ) * coefficientMass columns a := by
    have ht := norm_sum_le columns (fun I => a I * rowValue R I)
    have hs := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun I _ => norm_nonneg _))).mpr ht
    have hc := sq_sum_le_card_mul_sum_sq (s := columns) (f := fun I => ‖a I * rowValue R I‖)
    apply hs.trans (hc.trans _)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro I _
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (idealRowHom_norm _ _)
  calc
    _ ≤ ∑ _R ∈ rows, (columns.card : ℝ) * coefficientMass columns a :=
      Finset.sum_le_sum (fun R _ => hrow R)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Sixth-power extraction keeps its natural coprimality mask. -/
theorem row_sixth_power (R D I : Id) (hD : Supported D) (hI : Supported I) :
    rowValue (R*D^6) I = rowValue R I * (if IsCoprime I D then 1 else 0) := by
  have hpow : primaryGenerator (D^6) = (primaryGenerator D)^6 :=
    map_pow primaryGeneratorHom D 6
  dsimp only [rowValue]
  rw [primaryGenerator_mul, hpow, idealRowHom_argument_mul,
    idealRowHom_sixth_mask _ I hI,
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).1]

theorem coefficientMass_mask_le (columns : Finset Id) (a : Id → ℂ) (D : Id) :
    coefficientMass columns (fun I => a I * (if IsCoprime I D then 1 else 0)) ≤
      coefficientMass columns a := by
  apply Finset.sum_le_sum
  intro I _
  dsimp only
  split_ifs <;> simp [sq_nonneg]

end
end Candidate.FourthPower.SexticSieve
