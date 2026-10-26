/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.CommonRawWeights
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.WeightedSlotDiscard

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Record12518109Natural.WeightedHigh
noncomputable section
open scoped Classical BigOperators
open CommonSupply MarkedPlain
open HeckeFamily Cycle61Moment CenteredMomentEnergyState CenteredMomentNaturalRowSource
local notation "O"=>HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
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
    (hcoeff : ∀l∈rows,0≤coeff l)
    (weight : Row→ℝ)
    (hweight : ∀l∈rows,weight l=(∏s∈originalSlots (f l),max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
      (fun l=>excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l s‖)^2)
    (hcap : ∀l∈rows,∀s,(max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
      (fun l=>excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l s‖)^2≤
      C*Z^(δ*w s+error)) :
    let slots:=fun l=>CommonSupply.originalSlots (f l)
    let large:=fun l=>largeSlots (slots l) w wmin
    let amplitude:=labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
      (fun l=>excluded (naturalRow (st l).character (z l)
        ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture)
    (∑l∈rows,coeff l*Z^(δ*(base l-∑j:J l,w (f l j))+extra)*
      weight l)≤
    C^N*Z^(extra+error*N)*
      ∑l∈rows,coeff l*Z^(δ*(base l-∑s∈large l,w s))*(∏s∈large l,max 1 ‖amplitude l s‖)^2 := by
  intro slots large amplitude
  have he (l : Row) : (∑j:J l,w (f l j))=∑s∈slots l,w s :=
    CommonSupply.sum_originalSlots (f l) (hf l) w
  have hrw : (∑l∈rows,coeff l*Z^(δ*(base l-∑j:J l,w (f l j))+extra)*weight l)=
      ∑l∈rows,coeff l*Z^(δ*(base l-∑s∈slots l,w s)+extra)*(∏s∈slots l,max 1 ‖amplitude l s‖)^2 := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [he l,hweight l hl]
  rw [hrw]
  exact weighted_normalized_products_discard rows slots large
    (fun l _=>Finset.filter_subset _ _) w amplitude base coeff Z C δ error extra hZ hC herror
    N (fun l _=>(Finset.card_le_univ _).trans hN) hcoeff (fun l hl s _=>hcap l hl s)

end
end OAI.SevenEighths.Record12518109Natural.WeightedHigh
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.retained_family_discard
