import Candidate.Cycle63.Marked.SmallSlotDiscard

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators

/-- In a weighted family the tiny-slot high caps cancel their source widths
exactly. Their analytic errors and constants factor outside the row sum. -/
theorem weighted_normalized_products_discard {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row)(slots large : Row→Finset Slot)
    (hsub : ∀l∈rows,large l⊆slots l)(w : Slot→ℝ)(amp : Row→Slot→ℂ)
    (base coeff : Row→ℝ)(Z C δ error extra : ℝ)
    (hZ : 1<Z)(hC : 1≤C)(herror : 0≤error)(N : ℕ)
    (hN : ∀l∈rows,(slots l).card≤N)(hcoeff : ∀l∈rows,0≤coeff l)
    (hcap : ∀l∈rows,∀s∈slots l,(max 1 ‖amp l s‖)^2≤C*Z^(δ*w s+error)) :
    (∑l∈rows,coeff l*Z^(δ*(base l-∑s∈slots l,w s)+extra)*
        (∏s∈slots l,max 1 ‖amp l s‖)^2)≤
      C^N*Z^(extra+error*N)*
        ∑l∈rows,coeff l*Z^(δ*(base l-∑s∈large l,w s))*(∏s∈large l,max 1 ‖amp l s‖)^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have he:=normalized_product_discard (slots l) (large l) (hsub l hl) w (amp l)
    Z C δ error (δ*base l+extra) hZ hC herror N (hN l hl) (hcap l hl)
  rw [Finset.prod_pow, Finset.prod_pow] at he
  have hleft : (δ*base l+extra)-δ*(∑s∈slots l,w s)=δ*(base l-∑s∈slots l,w s)+extra:=by ring
  have hright : (δ*base l+extra)-δ*(∑s∈large l,w s)+error*N=
      (extra+error*N)+δ*(base l-∑s∈large l,w s):=by ring
  simp only [hleft,hright,Real.rpow_add (zero_lt_one.trans hZ)] at he
  have hh:=mul_le_mul_of_nonneg_left he (hcoeff l hl)
  simpa only [Real.rpow_add (zero_lt_one.trans hZ), mul_assoc, mul_left_comm, mul_comm] using hh

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.weighted_normalized_products_discard
