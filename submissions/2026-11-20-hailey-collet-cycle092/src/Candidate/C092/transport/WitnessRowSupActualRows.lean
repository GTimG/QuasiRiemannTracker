/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Coordinates and exact finite-row identities of the authentic P4 witness. -/
import Candidate.C092.transport.WitnessRowSupNative
import Candidate.C092.transport.WitnessOriginalMark
import Candidate.C092.transport.WitnessConductorBank

set_option autoImplicit false
namespace QRH.Cycle092.WitnessRowSup.Actual
noncomputable section
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness

/-- Both rectangle coordinates come from the genuine selected zero. -/
theorem witness_coordinates {Label : Type*} {χ : Label→Character}
    {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε cutoff T allowance i) (ha : 0 ≤ a) :
    w.zero.re ∈ Icc (0:ℝ) 1 ∧
      |2*Real.pi*w.nu-w.zero.im| ≤ 2*Real.pi*allowance+(3*i : ℕ)*T :=
  ⟨⟨ha.trans w.zero_lower,w.toWitness.real_part_upper⟩,w.toWitness.frequency_bound⟩

/-- The actual detector allowance is smaller than the original U^tau
height budget. No witness coordinate or new profile estimate is a premise. -/
theorem witness_height_budget {U d dmax τ : ℝ} (hU : 1 < U)
    (hd : d ≤ dmax) (hdmax : 0 < dmax) (hτ : 0 ≤ τ) (i : ℕ) :
    0 ≤ 2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i : ℕ)*U^τ ∧
    2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i : ℕ)*U^τ ≤
      (2*Real.pi+(3*i : ℕ))*U^τ := by
  have hp : (U^d)^(τ/(2*dmax)) ≤ U^τ := by
    rw [←Real.rpow_mul (zero_le_one.trans hU.le)]
    apply Real.rpow_le_rpow_of_exponent_le hU.le
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2*dmax)).mpr
    have hm := mul_le_mul_of_nonneg_right hd hτ
    nlinarith
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2*Real.pi)]

/-- An exact subtype/finset equality, with the same original row values. -/
theorem subtype_sum {Row : Type*} (rows : Finset Row) (f : Row→ℝ) :
    (∑ u : rows,f u.val) = ∑ u ∈ rows,f u := Finset.sum_coe_sort rows f

/-- P4 may name its row set as elements of O. Forgetting the FreeRow proof
is injective, so it neither duplicates nor removes any original source row. -/
theorem free_row_image_sum (rows : Finset FreeRow) (f : HeckeFamily.O→ℝ) :
    (∑ u ∈ rows,f u.val) = ∑ z ∈ rows.image Subtype.val,f z := by
  symm
  exact Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)

#print axioms witness_coordinates
#print axioms witness_height_budget
#print axioms free_row_image_sum
end
end QRH.Cycle092.WitnessRowSup.Actual
