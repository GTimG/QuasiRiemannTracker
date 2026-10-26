import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators
variable {Slot : Type*} [DecidableEq Slot]

def largeSlots (slots : Finset Slot) (w : Slot→ℝ) (wmin : ℝ) : Finset Slot:=
  slots.filter (fun s=>wmin≤w s)

theorem discarded_width_le (slots : Finset Slot) (w : Slot→ℝ) (wmin : ℝ)
    (N : ℕ) (hN : slots.card≤N) (hmin : 0≤wmin) :
    (∑s∈slots\largeSlots slots w wmin,w s)≤N*wmin := by
  calc
    _≤∑_s∈slots\largeSlots slots w wmin,wmin:=by
      refine Finset.sum_le_sum fun s hs => ?_
      have hn:¬wmin≤w s:=by
        intro hh
        exact (Finset.mem_sdiff.mp hs).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hs).1,hh⟩)
      exact (lt_of_not_ge hn).le
    _=((slots\largeSlots slots w wmin).card:ℝ)*wmin:=by simp
    _≤N*wmin:=mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans hN) hmin

theorem large_width_lower (slots : Finset Slot) (w : Slot→ℝ) (wmin : ℝ)
    (N : ℕ) (hN : slots.card≤N) (hmin : 0≤wmin) :
    (∑s∈slots,w s)-N*wmin≤∑s∈largeSlots slots w wmin,w s := by
  have he:=Finset.sum_sdiff (f:=w) (Finset.filter_subset (fun s=>wmin≤w s) slots)
  have hb:=discarded_width_le slots w wmin N hN hmin
  change (∑s∈slots\largeSlots slots w wmin,w s)+
    (∑s∈largeSlots slots w wmin,w s)=∑s∈slots,w s at he
  linarith

/-- Tiny physical slots use their actual high-bin caps, leaving the entire
large-slot product available to the marked count. -/
theorem full_product_discard (slots : Finset Slot) (large : Finset Slot)
    (hsub : large⊆slots) (w : Slot→ℝ) (A : Slot→ℂ)
    (Z C δ error : ℝ) (hZ : 1<Z) (hC : 1≤C) (herror : 0≤error)
    (N : ℕ) (hN : slots.card≤N)
    (hcap : ∀s∈slots,(max 1 ‖A s‖)^2≤C*Z^(δ*w s+error)) :
    (∏s∈slots,(max 1 ‖A s‖)^2)≤
      C^N*Z^(δ*(∑s∈slots\large,w s)+error*N)*∏s∈large,(max 1 ‖A s‖)^2 := by
  have hz : 0<Z:=zero_lt_one.trans hZ
  have hs : (∏s∈slots\large,(max 1 ‖A s‖)^2)≤
      C^N*Z^(δ*(∑s∈slots\large,w s)+error*N) := by
    calc
      _≤∏s∈slots\large,C*Z^(δ*w s+error):=
        Finset.prod_le_prod₀ (fun _ _=>sq_nonneg _) (fun s hs=>hcap s (Finset.mem_sdiff.mp hs).1)
      _=C^((slots\large).card)*Z^(δ*(∑s∈slots\large,w s)+error*(slots\large).card) := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hz]
        congr 2
        rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
        ring
      _≤_:=by
        apply mul_le_mul
        · exact pow_le_pow_right₀ hC ((Finset.card_le_card Finset.sdiff_subset).trans hN)
        · apply Real.rpow_le_rpow_of_exponent_le hZ.le
          have hc : ((slots\large).card:ℝ)≤N:=by
            exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans hN
          nlinarith
        · exact Real.rpow_nonneg hz.le _
        · exact pow_nonneg (zero_le_one.trans hC) _
  rw [←Finset.prod_sdiff hsub]
  exact mul_le_mul_of_nonneg_right hs (Finset.prod_nonneg (fun _ _=>sq_nonneg _))

/-- The discarded widths cancel exactly against the source normalization.
Only their fixed per-slot analytic errors remain. -/
theorem normalized_product_discard (slots large : Finset Slot)
    (hsub : large⊆slots) (w : Slot→ℝ) (A : Slot→ℂ)
    (Z C δ error e : ℝ) (hZ : 1<Z) (hC : 1≤C) (herror : 0≤error)
    (N : ℕ) (hN : slots.card≤N)
    (hcap : ∀s∈slots,(max 1 ‖A s‖)^2≤C*Z^(δ*w s+error)) :
    Z^(e-δ*(∑s∈slots,w s))*(∏s∈slots,(max 1 ‖A s‖)^2)≤
      C^N*Z^(e-δ*(∑s∈large,w s)+error*N)*(∏s∈large,(max 1 ‖A s‖)^2) := by
  have hs:=Finset.sum_sdiff (f:=w) hsub
  have hb:=mul_le_mul_of_nonneg_left
    (full_product_discard slots large hsub w A Z C δ error hZ hC herror N hN hcap)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le (e-δ*(∑s∈slots,w s)))
  apply hb.trans_eq
  calc
    _=C^N*(Z^(e-δ*(∑s∈slots,w s))*Z^(δ*(∑s∈slots\large,w s)+error*N))*
        (∏s∈large,(max 1 ‖A s‖)^2) := by ring
    _=_ := by
      rw [←Real.rpow_add (zero_lt_one.trans hZ)]
      congr 2
      congr 1
      rw [←hs]
      ring

end
end OAI.SevenEighths.Cycle63MarkedPlain

end Record1252270103Bootstrap.PR67
