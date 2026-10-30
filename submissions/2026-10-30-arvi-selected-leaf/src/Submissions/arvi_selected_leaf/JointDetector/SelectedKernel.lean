/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Eisenstein.ConjugateLevelAction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.CoprimeBilinearBound

/-! Exact finite interfaces for the selected ordinary-source norm.
No selected analytic estimate is assumed or proved in this file. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentHeckeExpansion CenteredMomentSourceRow
open CenteredMomentWholeSlotDeletion
local notation "O" => ActualEisensteinCubic.O

/-- Selection is fixed on the natural rows, independently of the source ideal. -/
def selectedRows (rows : Finset O) (keep : O → Prop) : Finset O :=
  rows.filter keep

@[simp] theorem mem_selectedRows (rows : Finset O) (keep : O → Prop) (z : O) :
    z ∈ selectedRows rows keep ↔ z ∈ rows ∧ keep z := by
  simp [selectedRows]

/-- The source set is arbitrary: no squarefree projection or unit deletion. -/
def selectedMatrix (rows : Finset O) (sources : Finset (Ideal O)) :
    Matrix sources rows ℂ := fun I z => idealRowHom z.val I.val

def selectedDualEnergy (rows : Finset O) (sources : Finset (Ideal O))
    (coeff : rows → ℂ) : ℝ :=
  ∑ I : sources, ‖∑ z : rows, selectedMatrix rows sources I z * coeff z‖ ^ 2

def selectedNorm (rows : Finset O) (sources : Finset (Ideal O)) : ℝ :=
  ‖FiniteSieveOperator.operator (selectedMatrix rows sources)‖ ^ 2

theorem selectedDualEnergy_le (rows : Finset O) (sources : Finset (Ideal O))
    (coeff : rows → ℂ) :
    selectedDualEnergy rows sources coeff ≤ selectedNorm rows sources * ∑ z, ‖coeff z‖ ^ 2 :=
  FiniteSieveOperator.energy_bound (selectedMatrix rows sources) coeff

theorem selectedNorm_le_of_energy (rows : Finset O) (sources : Finset (Ideal O))
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ coeff : rows → ℂ, selectedDualEnergy rows sources coeff ≤ C * ∑ z, ‖coeff z‖ ^ 2) :
    selectedNorm rows sources ≤ C :=
  FiniteSieveOperator.squared_norm_le_of_energy (selectedMatrix rows sources) C hC h

theorem selectedNorm_mono_rows {rows larger : Finset O} (h : rows ⊆ larger)
    (sources : Finset (Ideal O)) : selectedNorm rows sources ≤ selectedNorm larger sources := by
  let f : rows → larger := fun z => ⟨z.val, h z.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : larger => z.val) hab
  have hn := FiniteSieveRestriction.column_restriction_norm_le f hf
    (selectedMatrix larger sources)
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem selectedNorm_filter_le (rows : Finset O) (keep : O → Prop)
    (sources : Finset (Ideal O)) :
    selectedNorm (selectedRows rows keep) sources ≤ selectedNorm rows sources :=
  selectedNorm_mono_rows (Finset.filter_subset _ _) sources

theorem selectedNorm_mono_sources (rows : Finset O)
    {sources larger : Finset (Ideal O)} (h : sources ⊆ larger) :
    selectedNorm rows sources ≤ selectedNorm rows larger := by
  let f : sources → larger := fun I => ⟨I.val, h I.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun I : larger => I.val) hab
  have hn := FiniteSieveRestriction.row_restriction_norm_le f hf
    (selectedMatrix rows larger)
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

@[simp] theorem selectedMatrix_unit (rows : Finset O) (sources : Finset (Ideal O))
    (hunit : (1 : Ideal O) ∈ sources) (z : rows) :
    selectedMatrix rows sources ⟨1, hunit⟩ z = 1 := by
  exact map_one (idealRowHom z.val)

theorem selectedMatrix_natural_zero (rows : Finset O) (sources : Finset (Ideal O))
    (z : rows) (I : sources) (P : Ideal O) (hP : Prime P)
    (hPI : P ∣ I.val) (hz : z.val ∈ P) :
    selectedMatrix rows sources I z = 0 :=
  idealRowHom_zero_of_dvd z.val hP hPI hz

/-- Fixed anchor, common mask, and height factors are coefficients, not row features. -/
def slotCoefficient (η : HeckeFamily.Character) (m A : O) (β : Ideal O → ℂ)
    (t : ℝ) (I : Ideal O) : ℂ := β I * rowWeight η m A 1 t I

theorem normalizedSlot_common_coefficients (η : HeckeFamily.Character) (m A z : O)
    (sources : Finset (Ideal O)) (β : Ideal O → ℂ) (t P : ℝ) :
    normalizedSlot η m A z sources β t P =
      (Real.sqrt P : ℂ)⁻¹ *
        ∑ I ∈ sources, slotCoefficient η m A β t I * idealRowHom z I := by
  unfold normalizedSlot
  rw [rowSlot_eq_weight]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [rowWeight_split]
  simp only [slotCoefficient]
  ring

/-- This reciprocity adapter changes the summed ideal variable to the element
argument used by `row_pair_poisson`; its finite ray phase is retained. -/
theorem idealRow_orientation (row source : Ideal O)
    (hr : Supported row) (hs : Supported source) :
    idealRowHom (primaryGenerator row) source =
      sexticReciprocityPhase (primaryGenerator source) (primaryGenerator row) *
        idealRowHom (primaryGenerator source) row :=
  idealRowHom_ideal_reciprocity source row hs hr

theorem idealRow_pair_orientation (left right source : Ideal O)
    (hl : Supported left) (hr : Supported right) (hs : Supported source) :
    idealRowHom (primaryGenerator left) source *
        star (idealRowHom (primaryGenerator right) source) =
      (sexticReciprocityPhase (primaryGenerator source) (primaryGenerator left) *
        star (sexticReciprocityPhase (primaryGenerator source) (primaryGenerator right))) *
      (idealRowHom (primaryGenerator source) left *
        star (idealRowHom (primaryGenerator source) right)) := by
  rw [idealRow_orientation left source hl hs, idealRow_orientation right source hr hs,
    star_mul]
  ring

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.selectedNorm_filter_le
#print axioms Qrh.JointDetector.selectedMatrix_natural_zero
#print axioms Qrh.JointDetector.normalizedSlot_common_coefficients
#print axioms Qrh.JointDetector.idealRow_pair_orientation
