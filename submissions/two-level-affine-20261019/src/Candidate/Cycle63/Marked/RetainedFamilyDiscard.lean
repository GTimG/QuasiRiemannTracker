import Candidate.Cycle63.Marked.RetainedWeightTransport
import Candidate.Cycle63.Marked.WeightedSlotDiscard

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment CenteredMomentEnergyState CenteredMomentNaturalRowSource
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)

/-- The entire moving retained source family is reindexed on the original
coordinates before tiny slots are paid. No residual allocation appears in
the surviving max-product. -/
theorem retained_family_discard {Row Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (J : Row→Type) [∀l,Fintype (J l)]
    (f : ∀l,J l→Slot)(hf : ∀l,Function.Injective (f l))
    (P : HighSourceParameters)(hB : P.B₀=2)(η₀ : Character)(Z : ℝ)
    (st : Row→NaturalState Z P.Bmask P.bΦ)(z : Row→O)(hz : ∀l,(st l).radial.keep (z l))
    (w σ v : Slot→ℝ)(θ : Slot→RayQuotient.Characters M H)(t : Row→ℝ)
    (rows : Finset Row)(base coeff : Row→ℝ)(C δ error extra wmin : ℝ)
    (hZ : 1<Z)(hC : 1≤C)(herror : 0≤error)(N : ℕ)(hN : Fintype.card Slot≤N)
    (hcoeff : ∀l∈rows,0≤ coeff l)
    (hcap : ∀l∈rows,∀s,(max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
      (fun l=>excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l s‖)^2≤
      C*Z^(δ*w s+error)) :
    let slots:=fun l=>Cycle63CommonSupply.originalSlots (f l)
    let large:=fun l=>largeSlots (slots l) w wmin
    let amplitude:=labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
      (fun l=>excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture)
    (∑l∈rows,coeff l*Z^(δ*(base l-∑j:J l,w (f l j))+extra)*
      retainedSourceSlotWeight M H hH P η₀ Z (st l) (z l) (hz l)
        (fun j=>w (f l j)) (fun j=>σ (f l j)) (fun j=>v (f l j)) (fun j=>θ (f l j)) (t l))≤
    C^N*Z^(extra+error*N)*
      ∑l∈rows,coeff l*Z^(δ*(base l-∑s∈large l,w s))*(∏s∈large l,max 1 ‖amplitude l s‖)^2 := by
  intro slots large amplitude
  have he (l : Row) : (∑j:J l,w (f l j))=∑s∈slots l,w s :=
    Cycle63CommonSupply.sum_originalSlots (f l) (hf l) w
  have hw (l : Row) := retained_weight_original_product M H hH P hB η₀ Z st z hz
    w σ v θ t (f l) (hf l) l
  simp only [he,hw]
  exact weighted_normalized_products_discard rows slots large
    (fun l _=>Finset.filter_subset _ _) w amplitude base coeff Z C δ error extra hZ hC herror
    N (fun l _=>(Finset.card_le_univ _).trans hN) hcoeff (fun l hl s _=>hcap l hl s)

end
end OAI.SevenEighths.Cycle63MarkedPlain
