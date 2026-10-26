import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.ProfileMarkedShell
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.LabeledRawMax
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.OriginalSlotPartition
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.SmallSlotDiscard
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment CenteredMomentEnergyState CenteredMomentNaturalRowSource
variable (M : Ideal O) [NeZero M]
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
      (∏s∈Cycle63CommonSupply.originalSlots f,max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z
        w σ v t θ (fun l=>excluded (naturalRow (st l).character (z l)
          ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l s‖)^2 := by
  have hh:=Cycle63CommonSupply.prod_originalSlots f hf
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
end OAI.SevenEighths.Cycle63MarkedPlain

end Record1252270103Bootstrap.PR67
