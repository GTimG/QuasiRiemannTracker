/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Character-unit majorants and exact seed masks for independently colored
   literal coefficients. An aggregate need not be dominated by the old
   aggregate, because changing phases can remove cancellation. -/
import Candidate.C092.transport.TwistedRawSourceColumns

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawSource
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open QRH.SilDensitySplit.CubeFree.FP
local notation "Id" => Ideal HeckeFamily.O
local instance (priority := 2000) sumBoundsDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem ordinaryColor_norm_le_one (η₁ η₂ : Character) (v : Tuple ι) :
    ‖ordinaryColor (idealCoeff η₁) (idealCoeff η₂) v‖ ≤ 1 := by
  rw [ordinaryColor, norm_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul (idealCoeff_norm_le_one _ _)
      (idealCoeff_norm_le_one _ _) (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

/-- Tuple majorants transfer with constant one. This statement does not assert
    a false comparison between two differently cancelling aggregates. -/
theorem coloredTuple_norm_le (H : Id) (η₁ η₂ : Character) (F : Tuple ι → ℂ)
    (v : Tuple ι) :
    ‖coloredTuple H (idealCoeff η₁) (idealCoeff η₂) F v‖ ≤
      ‖MixedCommonCoefficient.tupleWeight H v * F v‖ := by
  unfold coloredTuple
  rw [show MixedCommonCoefficient.tupleWeight H v *
      ordinaryColor (idealCoeff η₁) (idealCoeff η₂) v * F v =
      (MixedCommonCoefficient.tupleWeight H v * F v) *
        ordinaryColor (idealCoeff η₁) (idealCoeff η₂) v by ring, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (ordinaryColor_norm_le_one η₁ η₂ v)

theorem sourceColumn_norm_majorant {a b : ℝ}
    (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a)
    (η₁ η₂ : Character) (seed I : Id) :
    ‖sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed I‖ ≤
      ∑ v ∈ (Fintype.piFinset (MixedPrincipalAllocations.tuplePools s)).filter
        (fun v => finiteTupleProduct v = I), ‖MixedOriginalSecondZero.originalTuple s ha seed v‖ := by
  unfold sourceColumn finiteColumnCoefficient
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro v hv
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (ordinaryColor_norm_le_one η₁ η₂ v)

/-- The native seed indicator is unchanged by the ordinary colors. -/
theorem originalTuple_seed {a b : ℝ}
    (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a) (seed : Id) (v : Tuple ι) :
    MixedOriginalSecondZero.originalTuple s ha seed v =
      if seed ∣ finiteTupleProduct v then MixedOriginalSecondZero.originalTuple s ha 1 v else 0 := by
  unfold MixedOriginalSecondZero.originalTuple profileCoefficient
  by_cases hd : seed ∣ finiteTupleProduct v <;> simp [hd]

/-- The signed second-stage sieve still acts on precisely the total live
    ideal. This is an equality before taking any absolute value. -/
theorem sourceColumn_seed {a b : ℝ}
    (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a)
    (ω₁ ω₂ : Id → ℂ) (seed I : Id) :
    sourceColumn s ha ω₁ ω₂ seed I =
      if seed ∣ I then sourceColumn s ha ω₁ ω₂ 1 I else 0 := by
  unfold sourceColumn finiteColumnCoefficient
  by_cases hd : seed ∣ I
  · rw [ite_eq_left hd]
    apply Finset.sum_congr rfl
    intro v hv
    change MixedOriginalSecondZero.originalTuple s ha seed v * ordinaryColor ω₁ ω₂ v = _
    rw [originalTuple_seed, ite_eq_left ((Finset.mem_filter.mp hv).2.symm ▸ hd)]
  · rw [ite_eq_right hd]
    apply Finset.sum_eq_zero
    intro v hv
    change MixedOriginalSecondZero.originalTuple s ha seed v * ordinaryColor ω₁ ω₂ v = _
    rw [originalTuple_seed, ite_eq_right ((Finset.mem_filter.mp hv).2.symm ▸ hd), zero_mul]

#print axioms ordinaryColor_norm_le_one
#print axioms coloredTuple_norm_le
#print axioms sourceColumn_norm_majorant
#print axioms originalTuple_seed
#print axioms sourceColumn_seed
end
end QRH.Cycle092.TwistedRawSource
