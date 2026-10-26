import Candidate.Cycle63.Marked.DeletionRawSlots

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators

/-- Maximal amplitudes expand into finitely many ordinary slot products.
This includes the empty subset, whose input is precisely the ordinary
unmarked row count. -/
theorem max_product_le_powerset {Slot : Type*} (slots : Finset Slot)
    (Q : Slot → ℂ) :
    (∏s∈slots,max 1 ‖Q s‖)^2 ≤ ∑J∈slots.powerset,‖∏s∈J,Q s‖^2 := by
  have hslot (s : Slot) : (max 1 ‖Q s‖)^2≤1+‖Q s‖^2 := by
    rcases le_total ‖Q s‖ 1 with hs|hs
    · rw [max_eq_left hs]
      nlinarith [sq_nonneg ‖Q s‖]
    · rw [max_eq_right hs]
      linarith
  calc
    _ = ∏s∈slots,(max 1 ‖Q s‖)^2 := by rw [Finset.prod_pow]
    _ ≤ ∏s∈slots,(1+‖Q s‖^2) :=
      Finset.prod_le_prod₀ (fun _ _=>sq_nonneg _) (fun s _=>hslot s)
    _ = ∑J∈slots.powerset,∏s∈J,‖Q s‖^2 := Finset.prod_one_add slots
    _ = _ := by
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [norm_prod,Finset.prod_pow]

/-- Uniform subset marked bounds imply the same saving for all maximal slot amplitudes, with the
explicit and fixed factor 2^number-of-slots, for a gain `G` whose deficit `δ x - G x` grows with the
width `x`. -/
theorem max_weighted_row_sum {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (Q : Row → Slot → ℂ)
    (w : Slot → ℝ) (U C ρ δ loss : ℝ) (G : ℝ → ℝ)
    (hw : ∀s∈slots,0≤w s) (hU : 1≤U) (hC : 0≤C) (hG : ∀ x y, x ≤ y → δ*x-G x ≤ δ*y-G y)
    (hsub : ∀J⊆slots,(∑u∈rows,‖∏s∈J,Q u s‖^2) ≤ C*U^(ρ+δ*(∑s∈J,w s)-G (∑s∈J,w s)+loss)) :
    (∑u∈rows,(∏s∈slots,max 1 ‖Q u s‖)^2) ≤
      (2:ℝ)^slots.card*C*U^(ρ+δ*(∑s∈slots,w s)-G (∑s∈slots,w s)+loss) := by
  have hs (J : Finset Slot) (hJ:J⊆slots) :
      ρ+δ*(∑s∈J,w s)-G (∑s∈J,w s)+loss ≤ ρ+δ*(∑s∈slots,w s)-G (∑s∈slots,w s)+loss := by
    have hh := hG _ _ (Finset.sum_le_sum_of_subset_of_nonneg hJ (fun s hs _=>hw s hs))
    linarith
  calc
    _ ≤ ∑u∈rows,∑J∈slots.powerset,‖∏s∈J,Q u s‖^2 :=
      Finset.sum_le_sum (fun u _=>max_product_le_powerset slots (Q u))
    _ = ∑J∈slots.powerset,∑u∈rows,‖∏s∈J,Q u s‖^2 := Finset.sum_comm
    _ ≤ ∑J∈slots.powerset,C*U^(ρ+δ*(∑s∈slots,w s)-G (∑s∈slots,w s)+loss) := by
      refine Finset.sum_le_sum fun J hJ => ?_
      have hJs := Finset.mem_powerset.mp hJ
      exact (hsub J hJs).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU (hs J hJs)) hC)
    _ = _ := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat];ring

/-- Convenient interface when the empty subset is supplied by the ordinary count and every nonempty
subset by the marked source, for a gain that vanishes at width zero. -/
theorem max_weighted_row_sum_of_nonempty {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (Q : Row → Slot → ℂ)
    (w : Slot → ℝ) (U C ρ δ loss : ℝ) (G : ℝ → ℝ)
    (hw : ∀s∈slots,0≤w s) (hU : 1≤U) (hC : 0≤C) (hG : ∀ x y, x ≤ y → δ*x-G x ≤ δ*y-G y)
    (hG0 : G 0 = 0) (hcount : (rows.card : ℝ)≤C*U^(ρ+loss))
    (hsub : ∀J⊆slots,J.Nonempty → (∑u∈rows,‖∏s∈J,Q u s‖^2) ≤
      C*U^(ρ+δ*(∑s∈J,w s)-G (∑s∈J,w s)+loss)) :
    (∑u∈rows,(∏s∈slots,max 1 ‖Q u s‖)^2) ≤
      (2:ℝ)^slots.card*C*U^(ρ+δ*(∑s∈slots,w s)-G (∑s∈slots,w s)+loss) := by
  apply max_weighted_row_sum rows slots Q w U C ρ δ loss G hw hU hC hG
  intro J hJ
  rcases J.eq_empty_or_nonempty with rfl|hne
  · simpa only [Finset.prod_empty,norm_one,one_pow,Finset.sum_const,Finset.sum_empty,
      nsmul_eq_mul,mul_one,mul_zero,hG0,sub_zero,add_zero] using hcount
  · exact hsub J hJ hne

end
end OAI.SevenEighths.Deletion26
