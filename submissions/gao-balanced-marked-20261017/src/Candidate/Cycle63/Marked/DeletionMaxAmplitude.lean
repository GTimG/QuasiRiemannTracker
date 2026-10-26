import Candidate.Cycle63.Marked.DeletionRawSlots

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators

/-- The gain is Lipschitz in surviving width, so paying more total width
always gives a weaker bound when the amplitude slope exceeds the gain. -/
theorem marked_exponent_monotone (δ g cap x y : ℝ)
    (hg : 0≤g) (hδ : g≤δ) (hxy : x≤y) :
    δ*x-g*min x cap ≤ δ*y-g*min y cap := by
  have hmin : min y cap-min x cap≤y-x := by
    rcases le_total cap x with hx|hx
    · rw [min_eq_right hx,min_eq_right (hx.trans hxy)]
      linarith
    · rw [min_eq_left hx]
      exact sub_le_sub_right (min_le_left _ _) x
  have hh := mul_le_mul_of_nonneg_left hmin hg
  have hd := mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr hxy)
  nlinarith

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
      apply Finset.sum_congr rfl
      intro J hJ
      rw [norm_prod,Finset.prod_pow]

/-- Uniform subset marked bounds imply the same saving for all maximal
slot amplitudes, with the explicit and fixed factor 2^number-of-slots. -/
theorem max_weighted_row_sum {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (Q : Row → Slot → ℂ)
    (w : Slot → ℝ) (U C ρ δ g cap loss : ℝ)
    (hw : ∀s∈slots,0≤w s) (hU : 1≤U) (hC : 0≤C) (hg : 0≤g) (hδ : g≤δ)
    (hsub : ∀J⊆slots,(∑u∈rows,‖∏s∈J,Q u s‖^2) ≤
      C*U^(ρ+δ*(∑s∈J,w s)-g*min (∑s∈J,w s) cap+loss)) :
    (∑u∈rows,(∏s∈slots,max 1 ‖Q u s‖)^2) ≤
      (2:ℝ)^slots.card*C*U^(ρ+δ*(∑s∈slots,w s)-g*min (∑s∈slots,w s) cap+loss) := by
  have hs (J : Finset Slot) (hJ:J⊆slots) :
      ρ+δ*(∑s∈J,w s)-g*min (∑s∈J,w s) cap+loss ≤
      ρ+δ*(∑s∈slots,w s)-g*min (∑s∈slots,w s) cap+loss := by
    have hh := marked_exponent_monotone δ g cap _ _ hg hδ
      (Finset.sum_le_sum_of_subset_of_nonneg hJ (fun s hs _=>hw s hs))
    linarith
  calc
    _ ≤ ∑u∈rows,∑J∈slots.powerset,‖∏s∈J,Q u s‖^2 :=
      Finset.sum_le_sum (fun u _=>max_product_le_powerset slots (Q u))
    _ = ∑J∈slots.powerset,∑u∈rows,‖∏s∈J,Q u s‖^2 := Finset.sum_comm
    _ ≤ ∑J∈slots.powerset,
        C*U^(ρ+δ*(∑s∈slots,w s)-g*min (∑s∈slots,w s) cap+loss) := by
      apply Finset.sum_le_sum
      intro J hJ
      have hJs := Finset.mem_powerset.mp hJ
      exact (hsub J hJs).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU (hs J hJs)) hC)
    _ = _ := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat];ring

/-- Convenient interface when the empty subset is supplied by the
ordinary count and every nonempty subset by the marked source. -/
theorem max_weighted_row_sum_of_nonempty {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (Q : Row → Slot → ℂ)
    (w : Slot → ℝ) (U C ρ δ g cap loss : ℝ)
    (hw : ∀s∈slots,0≤w s) (hU : 1≤U) (hC : 0≤C) (hg : 0≤g) (hδ : g≤δ)
    (hcap : 0≤cap)
    (hcount : (rows.card : ℝ)≤C*U^(ρ+loss))
    (hsub : ∀J⊆slots,J.Nonempty → (∑u∈rows,‖∏s∈J,Q u s‖^2) ≤
      C*U^(ρ+δ*(∑s∈J,w s)-g*min (∑s∈J,w s) cap+loss)) :
    (∑u∈rows,(∏s∈slots,max 1 ‖Q u s‖)^2) ≤
      (2:ℝ)^slots.card*C*U^(ρ+δ*(∑s∈slots,w s)-g*min (∑s∈slots,w s) cap+loss) := by
  apply max_weighted_row_sum rows slots Q w U C ρ δ g cap loss hw hU hC hg hδ
  intro J hJ
  rcases J.eq_empty_or_nonempty with rfl|hne
  · simpa only [Finset.prod_empty,norm_one,one_pow,Finset.sum_const,Finset.sum_empty,
      nsmul_eq_mul,mul_one,mul_zero,min_eq_left hcap,sub_zero,add_zero] using hcount
  · exact hsub J hJ hne

end
end OAI.SevenEighths.Deletion26
#print axioms OAI.SevenEighths.Deletion26.max_weighted_row_sum_of_nonempty
