import Candidate.Cycle62.Marked.ProfileMarkedShell
import Candidate.Cycle62.Marked.LabeledRawMax
import Candidate.Cycle62.Marked.OriginalSlotPartition
import Candidate.Cycle62.Marked.SmallSlotDiscard

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62MarkedPlain
noncomputable section
open scoped Classical BigOperators
open HeckeFamily Cycle62Moment CenteredMomentEnergyState CenteredMomentNaturalRowSource
local notation "O"=>HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)

/-- The full retained source factor is precisely the literal raw slot weight
on the surviving subset of the original coordinates. -/
theorem retained_weight_original_product {Row Slot J : Type}
    [Fintype J] [Fintype Slot] [DecidableEq Slot]
    (P : HighSourceParameters)(hB : P.B₀=2)(η₀ : Character)(Z : ℝ)
    (st : Row→NaturalState Z P.Bmask P.bΦ)(z : Row→O)(hz : ∀l,(st l).radial.keep (z l))
    (w σ v : Slot→ℝ)(θ : Slot→RayQuotient.Characters M H)(t : Row→ℝ)
    (f : J→Slot)(hf : Function.Injective f)(l : Row) :
    retainedSourceSlotWeight M H hH P η₀ Z (st l) (z l) (hz l)
      (fun j=>w (f j)) (fun j=>σ (f j)) (fun j=>v (f j)) (fun j=>θ (f j)) (t l)=
      (∏s∈Cycle62CommonSupply.originalSlots f,max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z
        w σ v t θ (fun l=>excluded (naturalRow (st l).character (z l)
          ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l s‖)^2 := by
  have hh:=Cycle62CommonSupply.prod_originalSlots f hf
    (fun s=>(max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
      (fun l=>excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l s‖)^2)
  simpa only [retainedSourceSlotWeight,labeledRawSlot,hB,Finset.prod_pow] using hh

/-- Positive widths in any surviving original subset retain the same total
upper bound as the original family. -/
theorem surviving_width_upper {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (slots : Finset Slot)(w : Slot→ℝ)(upper : ℝ)
    (hw : ∀s,0≤w s)(hupper : (∑s,w s)≤upper) :
    (∑s∈slots,w s)≤upper :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hw i)).trans hupper

end
end OAI.SevenEighths.Cycle62MarkedPlain
#print axioms OAI.SevenEighths.Cycle62MarkedPlain.retained_weight_original_product
