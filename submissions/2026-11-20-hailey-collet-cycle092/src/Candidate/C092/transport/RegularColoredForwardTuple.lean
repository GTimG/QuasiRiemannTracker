/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual colored finite tuple coefficient equals the native forward family,
with the original cube-free/supplier restriction and separate ordinary colors. -/
import Candidate.C092.transport.RegularColoredForwardFamily
import Candidate.C092.transport.TwistedRawSource
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedTupleRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower.KernelAssignmentReindex Candidate.FourthPower.KernelNaturalSlots
open KernelMarkedRows KernelRowProfiles KernelRowExpansion
open MixedCommonRestriction MixedCommonCoefficient MixedTupleRows
open QRH.Cycle092.TwistedRawSource
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance c092LocalInst_Candidate_C092_transport_RegularColoredForwardTuple_568c7d94cf146920_001 : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

/-- This is equality of the authentic weighted finite tuple sum, before
norms. In particular tupleWeight still imposes actual C.7 cube-freeness,
injectivity, supplier deletion and the same puncture product. -/
theorem normalized_colored_tuple_sum (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (pool : ι → Finset Id) (A B : Finset Id)
    (β : ι → Id → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    (∑ v ∈ Fintype.piFinset (pools (fun _ : ι => primeValues S) A B),
      coloredTuple (punctureProduct S H) ω₁ ω₂
        (rectangleCoefficient pool β P W₁ W₂ X₁ X₂) v *
        idealCoeff χ (finiteTupleProduct v)) =
      weightedSum (naturalCoefficients χ S pool β P)
        (fun slot => row χ ω₁ ω₂ (A ×ˢ B)
          (restrictedValue S (KernelPunctureRows.augmented S H (KernelLabelledSlots.marked S slot)))
          W₁ W₂ X₁ X₂) := by
  rw [split_tuple_sum,prime_tuple_sum]
  unfold weightedSum coloredTuple
  apply Finset.sum_congr rfl
  intro slot hslot
  simp_rw [packed_weight]
  by_cases hi : Function.Injective slot
  · simp only [hi,ite_true]
    rw [row,normalizedRow,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [pack_product,map_mul,natural_product_all]
    unfold rectangleCoefficient pairCharacter ordinaryColor color
    simp only [pack,Sum.elim_inl,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  · simp only [hi,ite_false,zero_mul,Finset.sum_const_zero]

/-- The actual finite colored column aggregate has exactly that same native
marked forward family. It is not a replacement coefficient bounded by norms. -/
theorem normalized_colored_column_sum (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (pool : ι → Finset Id) (A B : Finset Id)
    (β : ι → Id → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    let V := Fintype.piFinset (pools (fun _ : ι => primeValues S) A B)
    (∑ I ∈ finiteColumns V,
      coloredColumn V (punctureProduct S H) ω₁ ω₂
        (rectangleCoefficient pool β P W₁ W₂ X₁ X₂) I * idealCoeff χ I) =
      weightedSum (naturalCoefficients χ S pool β P)
        (fun slot => row χ ω₁ ω₂ (A ×ˢ B)
          (restrictedValue S (KernelPunctureRows.augmented S H (KernelLabelledSlots.marked S slot)))
          W₁ W₂ X₁ X₂) := by
  dsimp only
  rw [←colored_root_eq_columns]
  exact normalized_colored_tuple_sum χ ω₁ ω₂ S H pool A B β P W₁ W₂ X₁ X₂

/-- Both original signed scale arms remain present on the very same native
finite domain; the paired artificial-divisor normalizer is unchanged. -/
theorem centered_colored_tuple_sum (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (pool : ι → Finset Id) (A B : Finset Id)
    (β : ι → Id → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id × Id)
    (hX : 0 < X₁*X₂) (hXY : X₁*X₂=Y₁*Y₂) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) :
    (∑ v ∈ Fintype.piFinset (pools (fun _ : ι => primeValues S) A B),
      coloredTuple (punctureProduct S H) ω₁ ω₂
        (centeredCoefficient pool β P W₁ W₂ X₁ X₂ Y₁ Y₂ d) v *
        idealCoeff χ (finiteTupleProduct v)) =
      (Real.sqrt (pairNorm d) : ℂ)⁻¹ *
        (weightedSum (naturalCoefficients χ S pool β P)
          (fun slot => row χ ω₁ ω₂ (A ×ˢ B)
            (restrictedValue S (KernelPunctureRows.augmented S H (KernelLabelledSlots.marked S slot)))
            W₁ W₂ (X₁/d.1.absNorm) (X₂/d.2.absNorm)) -
         weightedSum (naturalCoefficients χ S pool β P)
          (fun slot => row χ ω₁ ω₂ (A ×ˢ B)
            (restrictedValue S (KernelPunctureRows.augmented S H (KernelLabelledSlots.marked S slot)))
            W₁ W₂ (Y₁/d.1.absNorm) (Y₂/d.2.absNorm))) := by
  unfold coloredTuple
  simp_rw [centered_extraction pool β P W₁ W₂ X₁ X₂ Y₁ Y₂ d hX hXY hd]
  rw [←normalized_colored_tuple_sum,←normalized_colored_tuple_sum,
    ←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  unfold coloredTuple
  ring

#print axioms normalized_colored_tuple_sum
#print axioms normalized_colored_column_sum
#print axioms centered_colored_tuple_sum
end
end QRH.Cycle092.RegularColoredForward
