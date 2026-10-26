/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion

set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open scoped BigOperators Classical
open OAI.SevenEighths

/-- A first-geometry cap controls erasure in every later surviving slot set.
The set is chosen using widths alone, before coefficients, rows or profiles. -/
theorem erase_to_first_cap {α : Type*} (S : Finset α) (w : α → ℝ)
    (mesh firstWidth cap : ℝ) (hmesh : 0 ≤ mesh) (hcap : 0 ≤ cap)
    (hfirst : cap ≤ firstWidth) (hw : ∀ i∈S, 0 ≤ w i)
    (hwm : ∀ i∈S, w i ≤ mesh) (htotal : (∑ i∈S,w i) ≤ firstWidth) :
    ∃ R : Finset α, R ⊆ S ∧ (∑ i∈S\R,w i) ≤ cap ∧
      (∑ i∈R,w i) ≤ firstWidth-cap+mesh := by
  by_cases hsmall : (∑ i∈S,w i) ≤ cap
  · refine ⟨∅,Finset.empty_subset _,?_,?_⟩
    · simpa using hsmall
    · simp only [Finset.sum_empty]
      linarith
  · have hexcess : 0 ≤ 6*((∑ i∈S,w i)-cap) := by linarith
    obtain ⟨R,hR,hcost,hpay,_⟩ :=
      CenteredMomentWholeSlotDeletion.whole_removal S w
        (6*((∑ i∈S,w i)-cap)) 1 mesh hexcess (by norm_num) hmesh hw hwm
    refine ⟨R,hR,?_,?_⟩
    · rcases hpay with hpay|hpay
      · subst R
        simpa using hcap
      · have hsum := Finset.sum_sdiff hR (f:=w)
        nlinarith only [hpay,hsum]
    · have hc := hcost.trans (min_le_right _ _)
      norm_num only [mul_one,div_self_mul_self] at hc
      linarith

/-- Uniform price for the removed whole slots in the literal normalized
two-plain product. The original plain factors and every surviving slot are
unchanged. -/
theorem actual_product_first_cap {α : Type*} (S : Finset α) (w : α → ℝ)
    (mesh firstWidth cap : ℝ) (hmesh : 0 ≤ mesh) (hcap : 0 ≤ cap)
    (hfirst : cap ≤ firstWidth) (hw : ∀ i∈S, 0 ≤ w i)
    (hwm : ∀ i∈S, w i ≤ mesh) (htotal : (∑ i∈S,w i) ≤ firstWidth) :
    ∃ R : Finset α, R ⊆ S ∧ (∑ i∈S\R,w i) ≤ cap ∧
      ∀ (η : HeckeFamily.Character) (m A z : HeckeFamily.O)
        (W₁ W₂ : ℝ → ℂ) (pool : α → Finset (Ideal HeckeFamily.O))
        (β : α → Ideal HeckeFamily.O → ℂ) (P : α → ℝ)
        (t X₁ X₂ Z q : ℝ) (hZ : 1 ≤ Z) (hq : 0 ≤ q) (B : α → ℝ),
      (∀ i∈R, 0 ≤ B i) →
      (∀ i∈R,
        ‖CenteredMomentWholeSlotDeletion.normalizedSlot η m A z (pool i) (β i) t (P i)‖^2 ≤
          B i*Z^(q*w i)) →
      ‖CenteredMomentWholeSlotDeletion.selectedProduct S η m A z W₁ W₂ pool β P t X₁ X₂‖^2 ≤
        ((∏ i∈R,B i)*Z^(q*(firstWidth-cap+mesh)))*
          ‖CenteredMomentWholeSlotDeletion.selectedProduct (S\R) η m A z W₁ W₂ pool β P t X₁ X₂‖^2 := by
  obtain ⟨R,hR,hleft,hcost⟩ := erase_to_first_cap S w mesh firstWidth cap
    hmesh hcap hfirst hw hwm htotal
  refine ⟨R,hR,hleft,?_⟩
  intro η m A z W₁ W₂ pool β P t X₁ X₂ Z q hZ hq B hB hslot
  have he := CenteredMomentWholeSlotDeletion.selectedProduct_energy_remove S R hR
    η m A z W₁ W₂ pool β P t X₁ X₂ Z q (zero_lt_one.trans_le hZ) w B hB hslot
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg hB)
  exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_left hcost hq)

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.erase_to_first_cap
#print axioms QRH.Record12518109Source.actual_product_first_cap
