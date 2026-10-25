/- Copyright (c) 2026 Sil. Apache-2.0.
The literal finite operator for the sextic sieve. Reciprocity has only a fixed
finite loss. This module does not assume or assert the optimal large sieve. -/
import Candidate.Feedback.FourthPower.SexticSieve
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CubicSieve.Operator

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.SieveOperator
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths CompletedGauss CanonicalRowCompletion SexticSieve
open CanonicalQuadraticSieve
open FiniteSieveOperator
local notation "Id" => Ideal ActualEisensteinCubic.O

def matrix (rows columns : Finset Id) : Matrix rows columns ℂ :=
  fun R I => rowValue R.val I.val

def squaredNorm (rows columns : Finset Id) : ℝ := ‖operator (matrix rows columns)‖^2

theorem energy_eq_norm (rows columns : Finset Id) (a : Id → ℂ) :
    energy rows columns a =
      ‖operator (matrix rows columns) (WithLp.toLp 2 (fun I : columns => a I.val))‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [operator_apply, matrix, energy, mul_comm]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro R _
  rw [← Finset.sum_coe_sort]

theorem mass_eq_norm (columns : Finset Id) (a : Id → ℂ) :
    coefficientMass columns a = ‖WithLp.toLp 2 (fun I : columns => a I.val)‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact (Finset.sum_coe_sort columns (fun I => ‖a I‖^2)).symm

theorem energy_bound (rows columns : Finset Id) (a : Id → ℂ) :
    energy rows columns a ≤ squaredNorm rows columns * coefficientMass columns a := by
  rw [energy_eq_norm, mass_eq_norm]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    ((operator (matrix rows columns)).le_opNorm _) 2).trans_eq (mul_pow _ _ _)

/-- Exact operator interpretation, including empty families and arbitrary
common coefficients. No analytic estimate is hidden in this equivalence. -/
theorem bound_iff (rows columns : Finset Id) (K : ℝ) (hK : 0 ≤ K) :
    squaredNorm rows columns ≤ K ↔
      ∀ a : Id → ℂ, energy rows columns a ≤ K * coefficientMass columns a := by
  constructor
  · intro h a
    exact (energy_bound rows columns a).trans
      (mul_le_mul_of_nonneg_right h (coefficientMass_nonneg _ _))
  · intro h
    have hop : ‖operator (matrix rows columns)‖ ≤ Real.sqrt K := by
      apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
      intro x
      let a : Id → ℂ := fun I => if hI : I ∈ columns then x ⟨I,hI⟩ else 0
      have ha : WithLp.toLp 2 (fun I : columns => a I.val) = x := by
        ext I
        simp [a]
      have he := h a
      rw [energy_eq_norm, mass_eq_norm, ha] at he
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      simpa only [mul_pow, Real.sq_sqrt hK] using he
    exact (pow_le_pow_left₀ (norm_nonneg _) hop 2).trans_eq (Real.sq_sqrt hK)

def ray (I : Id) : EisensteinEPrimaryPhase.Coord :=
  ActualEisensteinCoordinates.residue (primaryGenerator I)

def phase (r s : EisensteinEPrimaryPhase.Coord) : ℂ :=
  (QuadraticAllOddCRT.quadraticRaySign r s : ℂ)

theorem phase_norm_le (r s : EisensteinEPrimaryPhase.Coord) : ‖phase r s‖ ≤ 1 := by
  unfold phase QuadraticAllOddCRT.quadraticRaySign
  split_ifs <;> norm_num

theorem row_reciprocity (R I : Id) (hR : Supported R) (hI : Supported I) :
    rowValue R I = phase (ray I) (ray R) * rowValue I R :=
  idealRowHom_ideal_reciprocity I R hI hR

theorem operator_reverse_le (rows columns : Finset Id)
    (hr : ∀ R ∈ rows, Supported R) (hc : ∀ I ∈ columns, Supported I) :
    ‖operator (matrix rows columns)‖ ≤ 16 * ‖operator (matrix columns rows)‖ := by
  let A := matrix rows columns
  let B := (matrix columns rows).transpose
  let l : EisensteinEPrimaryPhase.Coord → rows → ℂ :=
    fun r R => if ray R.val = r then 1 else 0
  let v : EisensteinEPrimaryPhase.Coord → columns → ℂ :=
    fun r I => phase (ray I.val) r
  have hl : ∀ r R, ‖l r R‖ ≤ 1 := by intro r R; dsimp [l]; split_ifs <;> norm_num
  have hv : ∀ r I, ‖v r I‖ ≤ 1 := fun r I => phase_norm_le _ _
  have he : ∀ R I, A R I = ∑ r, (1 : ℂ) * (l r R * B R I * v r I) := by
    intro R I
    simp only [l, v, one_mul, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    change rowValue R.val I.val = rowValue I.val R.val * phase (ray I.val) (ray R.val)
    rw [row_reciprocity _ _ (hr _ R.property) (hc _ I.property), mul_comm]
  have ht := separated_phase_norm_le A B (fun _ => (1 : ℂ)) l v hl hv he
  have hb : ‖operator B‖ = ‖operator (matrix columns rows)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    exact CubicSieve.squaredNorm_transpose (matrix columns rows)
  simpa only [norm_one, Finset.sum_const, Finset.card_univ,
    EisensteinEPrimaryPhase.Coord, Fintype.card_prod, ZMod.card, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat, mul_one, show (4 : ℝ)*4=16 by norm_num, hb] using ht

theorem squaredNorm_reverse_le (rows columns : Finset Id)
    (hr : ∀ R ∈ rows, Supported R) (hc : ∀ I ∈ columns, Supported I) :
    squaredNorm rows columns ≤ 256 * squaredNorm columns rows := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (operator_reverse_le rows columns hr hc) 2
  simpa only [squaredNorm, mul_pow, show (16 : ℝ)^2=256 by norm_num] using h

end
end Candidate.Feedback.FourthPower.SieveOperator
