/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Mathlib

set_option autoImplicit false
namespace OAI.SevenEighths.AuxiliaryHigh
noncomputable section
open scoped Classical BigOperators

/-- A finite source family is split by its actual removed common width.
The constants and height degree are fixed before the source family moves. -/
theorem high_branch_sum_join {ι : Type*} (s : Finset ι)
    (f removed : ι→ℝ) (threshold : ℝ) (factor CU CM height rest : ℝ)
    (JU JM : ℕ) (hfactor : 0 ≤ factor) (hCU : 0 ≤ CU) (hCM : 0 ≤ CM)
    (hheight : 1 ≤ height) (hrest : 0 ≤ rest)
    (hunmarked : ∀ls : Finset ι,ls⊆s →
      (∀l∈ls,threshold ≤ removed l) →
      (∑l∈ls,f l) ≤ factor*CU*height^JU*rest)
    (hmarked : ∀ls : Finset ι,ls⊆s →
      (∀l∈ls,removed l ≤ threshold) →
      (∑l∈ls,f l) ≤ factor*CM*height^JM*rest) :
    (∑l∈s,f l) ≤ factor*(CU+CM)*height^(max JU JM)*rest := by
  have hu := pow_le_pow_right₀ hheight (le_max_left JU JM)
  have hm := pow_le_pow_right₀ hheight (le_max_right JU JM)
  let small:=s.filter (fun l=>removed l ≤ threshold)
  let large:=s.filter (fun l=>¬removed l ≤ threshold)
  have hms:=hmarked small (Finset.filter_subset _ _)
    (fun l hl=>(Finset.mem_filter.mp hl).2)
  have hus:=hunmarked large (Finset.filter_subset _ _)
    (fun l hl=>le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hl).2))
  have hsum : (∑l∈small,f l)+(∑l∈large,f l)=∑l∈s,f l :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hmb:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (mul_nonneg hfactor hCM)) hrest
  have hub:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (mul_nonneg hfactor hCU)) hrest
  have hh:=add_le_add (hms.trans hmb) (hus.trans hub)
  rw [hsum] at hh
  calc
    _ ≤ _:=hh
    _=_:=by ring

end
end OAI.SevenEighths.AuxiliaryHigh
