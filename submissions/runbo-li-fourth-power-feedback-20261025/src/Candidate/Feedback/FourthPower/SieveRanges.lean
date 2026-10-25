/- Copyright (c) 2026 Sil. Apache-2.0.
Concrete norm functions for the sixth-power-free and completed row families.
All bounds here are on actual matrices; the optimal sieve is still open. -/
import Candidate.Feedback.FourthPower.SieveInitialEnergy

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.SieveRanges
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalQuadraticSieve SexticSieve SieveOperator SixthDecomposition
open CenteredExceptionalCount FiniteSieveOperator
local notation "Id" => Ideal ActualEisensteinCubic.O

def fullRange (A : ℝ) : Finset Id := (idealsUpTo ⌊A⌋₊).filter Supported
def freeRange (A : ℝ) : Finset Id := (fullRange A).filter (PowerFree 6)

theorem mem_fullRange {A : ℝ} {I : Id} :
    I ∈ fullRange A ↔ Supported I ∧ (Ideal.absNorm I : ℝ) ≤ A := by
  rw [fullRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp,hn⟩,hs⟩
    refine ⟨hs,?_⟩
    have hA : 0 ≤ A := by
      by_contra! h
      have hz : ⌊A⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hn).trans (Nat.floor_le hA)
  · rintro ⟨hs,hn⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hs.1), Nat.le_floor hn⟩,hs⟩

theorem mem_freeRange {A : ℝ} {I : Id} :
    I ∈ freeRange A ↔ Supported I ∧ PowerFree 6 I ∧ (Ideal.absNorm I : ℝ) ≤ A := by
  simp only [freeRange, Finset.mem_filter, mem_fullRange]
  tauto

def theta (A B : ℝ) : ℝ := squaredNorm (freeRange A) (freeRange B)
def lambda (A B : ℝ) : ℝ := squaredNorm (fullRange A) (freeRange B)

theorem theta_nonneg (A B : ℝ) : 0 ≤ theta A B := sq_nonneg _
theorem lambda_nonneg (A B : ℝ) : 0 ≤ lambda A B := sq_nonneg _

theorem norm_mono {rows rows' columns columns' : Finset Id}
    (hr : rows ⊆ rows') (hc : columns ⊆ columns') :
    squaredNorm rows columns ≤ squaredNorm rows' columns' := by
  let r : rows → rows' := fun R => ⟨R.val,hr R.property⟩
  let c : columns → columns' := fun I => ⟨I.val,hc I.property⟩
  have hri : Function.Injective r := fun I J he =>
    Subtype.ext (show I.val = J.val from congrArg (fun x : rows' => x.val) he)
  have hci : Function.Injective c := fun I J he =>
    Subtype.ext (show I.val = J.val from congrArg (fun x : columns' => x.val) he)
  exact pow_le_pow_left₀ (norm_nonneg _)
    (FiniteSieveRestriction.submatrix_norm_le r hri c hci (matrix rows' columns')) 2

theorem fullRange_mono {A B : ℝ} (h : A ≤ B) : fullRange A ⊆ fullRange B := by
  intro I hI
  exact mem_fullRange.mpr ⟨(mem_fullRange.mp hI).1, (mem_fullRange.mp hI).2.trans h⟩

theorem freeRange_mono {A B : ℝ} (h : A ≤ B) : freeRange A ⊆ freeRange B := by
  intro I hI
  exact mem_freeRange.mpr ⟨(mem_freeRange.mp hI).1, (mem_freeRange.mp hI).2.1,
    (mem_freeRange.mp hI).2.2.trans h⟩

theorem theta_mono {A B A' B' : ℝ} (hA : A ≤ A') (hB : B ≤ B') : theta A B ≤ theta A' B' :=
  norm_mono (freeRange_mono hA) (freeRange_mono hB)

theorem lambda_mono {A B A' B' : ℝ} (hA : A ≤ A') (hB : B ≤ B') : lambda A B ≤ lambda A' B' :=
  norm_mono (fullRange_mono hA) (freeRange_mono hB)

theorem theta_le_lambda (A B : ℝ) : theta A B ≤ lambda A B :=
  norm_mono (Finset.filter_subset _ _) (Finset.Subset.refl _)

theorem theta_reverse (A B : ℝ) : theta A B ≤ 256*theta B A :=
  squaredNorm_reverse_le _ _ (fun _R hR => (mem_freeRange.mp hR).1)
    (fun _I hI => (mem_freeRange.mp hI).1)

theorem energy_le_theta (A B : ℝ) (rows columns : Finset Id)
    (hr : ∀ R ∈ rows, Supported R ∧ PowerFree 6 R ∧ (Ideal.absNorm R : ℝ) ≤ A)
    (hc : ∀ I ∈ columns, Supported I ∧ PowerFree 6 I ∧ (Ideal.absNorm I : ℝ) ≤ B)
    (a : Id → ℂ) : energy rows columns a ≤ theta A B * coefficientMass columns a := by
  apply (energy_bound rows columns a).trans
  apply mul_le_mul_of_nonneg_right _ (coefficientMass_nonneg _ _)
  exact norm_mono (fun R hR => mem_freeRange.mpr (hr R hR))
    (fun I hI => mem_freeRange.mpr (hc I hI))

theorem lambda_initial (A B : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    lambda A B ≤ QuadraticInitialBound.initialSieveConstant*(A+B^2) := by
  apply (bound_iff _ _ _ (by have := QuadraticInitialBound.initialSieveConstant_pos; positivity)).mpr
  intro a
  exact SieveInitialEnergy.initial_ideal_bound _ _
    (fun R hR => (mem_fullRange.mp hR).1)
    (fun I hI => ⟨(mem_freeRange.mp hI).1,(mem_freeRange.mp hI).2.1⟩)
    A B hA hB (fun R hR => (mem_fullRange.mp hR).2)
    (fun I hI => (mem_freeRange.mp hI).2.2) a

theorem theta_initial (A B : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    theta A B ≤ QuadraticInitialBound.initialSieveConstant*(A+B^2) :=
  (theta_le_lambda A B).trans (lambda_initial A B hA hB)

/-- Exact sixth-power extraction translated into the actual finite norms.
The surviving coefficients include the original coprimality mask. -/
theorem lambda_sixth_extraction (A B : ℝ) :
    lambda A B ≤ ∑ D ∈ (fullRange A).image sixthQuotient,
      theta (A/(Ideal.absNorm D : ℝ)^6) B := by
  apply (bound_iff _ _ _ (Finset.sum_nonneg (fun D _ => theta_nonneg _ _))).mpr
  intro a
  rw [exact_energy_decomposition _ _ (fun R hR => (mem_fullRange.mp hR).1)
    (fun I hI => (mem_freeRange.mp hI).1), Finset.sum_mul]
  apply Finset.sum_le_sum
  intro D _
  have hred : ∀ R ∈ reducedRows (fullRange A) D,
      Supported R ∧ PowerFree 6 R ∧ (Ideal.absNorm R : ℝ) ≤ A/(Ideal.absNorm D : ℝ)^6 := by
    intro R hR
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨hIA,hID⟩ := Finset.mem_filter.mp hI
    have hs := (mem_fullRange.mp hIA).1
    refine ⟨remainder_supported I hs, remainder_powerFree I, ?_⟩
    have hn := row_scale I hs A (mem_fullRange.mp hIA).2
    simpa only [hID] using hn
  apply (energy_le_theta _ B _ _ hred (fun I hI => mem_freeRange.mp hI) (maskedCoefficient a D)).trans
  exact mul_le_mul_of_nonneg_left (coefficientMass_mask_le _ a D) (theta_nonneg _ _)

end
end Candidate.Feedback.FourthPower.SieveRanges
