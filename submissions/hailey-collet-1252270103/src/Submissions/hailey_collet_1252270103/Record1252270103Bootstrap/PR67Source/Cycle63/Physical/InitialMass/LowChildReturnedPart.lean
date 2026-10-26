import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildReturned
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The returned part of a bound as a part: for every returned clause there is a returned part with the data of the
clause, the empty one when the returned bound is zero. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The returned part without classes, with the given energy scale, total length, amplifier and loss. -/
def ReturnedPart.empty {Base : Type} (base : Character → Base → Character) (η₀ : Character) (Z Bnorm T : ℝ)
    (v₁ : O) (scale length amp loss : ℝ) : ReturnedPart M H hH base η₀ Z Bnorm T v₁ where
  unit := fun _ _ => 0
  record := fun b => SecondStepHighCount.empty M H hH (base η₀) η₀ Z Bnorm T b v₁ (fun _ => 0)
  scale := scale
  length := length
  amp := amp
  loss := loss
  pays := fun _ σ => σ.elim

variable {M H hH}

/-- Every returned clause is the clause of a returned part: when the returned bound is zero the part is the empty
one at the caps, and then its count form is zero and it has no class. -/
theorem ReturnedClause.exists_part {AllowRet : Prop} {Base : Type} {base : Character → Base → Character}
    {η₀ : Character} {Z Bnorm T : ℝ} {v₁ : O} {scale loss lengthCap ampCap Kcap factor Ret : ℝ}
    (h : ReturnedClause M H hH AllowRet base η₀ Z Bnorm T v₁ scale loss lengthCap ampCap Kcap factor Ret) :
    ∃P : ReturnedPart M H hH base η₀ Z Bnorm T v₁, P.scale = scale ∧ P.loss = loss ∧ P.length ≤ lengthCap ∧
      P.amp ≤ ampCap ∧ (∀b, (Fintype.card (P.record b).Class : ℝ) ≤ max Kcap 0) ∧ Ret = factor * P.value := by
  rcases h with h0 | ⟨_, P, h1, h2, h3, h4, h5, h6⟩
  · refine ⟨ReturnedPart.empty M H hH base η₀ Z Bnorm T v₁ scale lengthCap ampCap loss, rfl, rfl, le_rfl, le_rfl,
      fun b => ?_, ?_⟩
    · have hc : Fintype.card (SecondStepHighCount.empty M H hH (base η₀) η₀ Z Bnorm T b v₁ (fun _ => 0)).Class = 0 :=
        Fintype.card_eq_zero_iff.mpr ⟨fun σ => Empty.elim σ⟩
      change (Fintype.card (SecondStepHighCount.empty M H hH (base η₀) η₀ Z Bnorm T b v₁ (fun _ => 0)).Class : ℝ) ≤ _
      rw [hc, Nat.cast_zero]
      exact le_max_right _ _
    · have hv : (ReturnedPart.empty M H hH base η₀ Z Bnorm T v₁ scale lengthCap ampCap loss).value = 0 := by
        unfold ReturnedPart.value
        exact Finset.sum_eq_zero fun b _ => SecondStepHighCount.empty_value
      rw [hv, h0, mul_zero]
  · exact ⟨P, h1, h2, h3, h4, fun b => (h5 b).trans (le_max_left _ _), h6⟩

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
