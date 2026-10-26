import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.SecondLevelCell
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.SecondApplicable
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The states of the second step at the ledger of a grid position: which states fit the ledger, and the facts about
them that the generic step asks. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical
open HeckeFamily CenteredMomentEnergyState Cycle63 Cycle63.Optimization

/-- The states of the second step whose plain lengths, slot length, unit, total length and amplifier fit the ledger at
the grid position `i`: the lengths in the unit `W` lie in the plain window of the position, and the total length and the
amplifier of the position in the unit `W` are at most `length` and `amp`. -/
def SecondStepFits (G : ℕ) (i : SecondIndex G) (x₁ x₂ z W length amp : ℝ) : Prop :=
  PlainWindow (gridPosition G i.1).windowBottom (gridPosition G i.1).sumBottom
    ((gridPosition G i.1).slotTop - (gridPosition G i.1).mesh) (gridPosition G i.1).slotTop secondSlope
    (gridPosition G i.1).intercept (x₁/W) (x₂/W) (z/W) ∧
  W*(gridPosition G i.1).totalA ≤ length ∧ W*(gridPosition G i.1).amp ≤ amp

/-- Every state to which the second step applies fits the ledger at one of the grid positions. -/
theorem secondApplicable_fits {Bmask bΦ : ℝ} {G : ℕ} (hG : 0 < G) (lossFloor : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → Prop)
    {η₀ : Character} {Z : ℝ} {s : NaturalState Z Bmask bΦ} {v₁ : O} {x₁ x₂ z W T length amp loss : ℝ}
    (hz : 0 ≤ z) (h : SecondApplicable G lossFloor Presented η₀ Z s v₁ x₁ x₂ z W T length amp loss) :
    ∃ i : SecondIndex G, SecondStepFits G i x₁ x₂ z W length amp := by
  obtain ⟨i, hi⟩ := SecondStepArithmetic.family hG hz h.1
  exact ⟨i, hi⟩

/-- The facts of a state of the second step at the ledger of its grid position, as the generic step asks them: the
unit is the width of the state and at least `2/5`, the presentation, the loss and the overshoot of the capacity over the
unit, the plain window of the ledger, the total length and the amplifier of its cell in the unit of the state, and the
amplifier of its cell above three times a number `δ` that is at most the weight of the LOW reserve. -/
theorem secondFamily_part {Bmask bΦ : ℝ} {G : ℕ} (i : SecondIndex G) (lossFloor δ : ℝ) (hδ : 3*δ ≤ lowReserveWeight)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask bΦ → O → ℝ → Prop)
    {η₀ : Character} {Z : ℝ} {s : NaturalState Z Bmask bΦ} {v₁ : O} {x₁ x₂ z W T length amp loss : ℝ}
    (h : SecondApplicable G lossFloor Presented η₀ Z s v₁ x₁ x₂ z W T length amp loss)
    (hfit : SecondStepFits G i x₁ x₂ z W length amp) :
    W = s.width ∧ 2/5 ≤ W ∧ Presented η₀ Z s v₁ T ∧ lossFloor ≤ loss ∧ x₁ + x₂ + 6*slotPrice*z - W ≤ 7/2500 ∧
      @AffineLedger.PlainWindow (secondFamily G i) (x₁/W) (x₂/W) (z/W) ∧
      @AffineLedger.totalA (secondFamily G i) (@AffineLedger.cellUpper (secondFamily G i)
        (@AffineLedger.originalCell (secondFamily G i) (z/W)))*W ≤ length ∧
      @AffineLedger.amp (secondFamily G i) (@AffineLedger.cellUpper (secondFamily G i)
        (@AffineLedger.originalCell (secondFamily G i) (z/W)))*W ≤ amp ∧
      3*δ ≤ @AffineLedger.amp (secondFamily G i) (@AffineLedger.cellUpper (secondFamily G i)
        (@AffineLedger.originalCell (secondFamily G i) (z/W))) := by
  obtain ⟨⟨hW, hfloor, hfacts, -, -, hloss, hover⟩, hpres⟩ := h
  obtain ⟨hwin, htot, hamp⟩ := hfit
  have hz : (gridPosition G i.1).slotTop - (gridPosition G i.1).mesh ≤ z/W ∧ z/W ≤ (gridPosition G i.1).slotTop :=
    ⟨hwin.slots_ge, hwin.slots_le⟩
  refine ⟨hW, hfloor, hpres, hloss, hover, hwin, ?_, ?_, ?_⟩
  · rw [secondFamily_cell_totalA G i hz]
    linarith
  · rw [secondFamily_cell_amp G i hz]
    linarith
  · rw [secondFamily_cell_amp G i hz]
    exact (by linarith : 3*δ ≤ lowReserveWeight).trans (SecondPosition.lowReserveWeight_le_amp i.2)

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
