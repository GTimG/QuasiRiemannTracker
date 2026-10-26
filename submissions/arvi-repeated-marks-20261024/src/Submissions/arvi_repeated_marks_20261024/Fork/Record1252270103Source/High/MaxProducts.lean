/- Repeated marks: fork of Record1252270103Source.High.MaxProducts (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.MaxProducts
import Submissions.arvi_repeated_marks_20261024.Source.GainC
import Submissions.arvi_repeated_marks_20261024.Source.CountWrappersK
import Submissions.arvi_repeated_marks_20261024.Source.GainPaymentK
import Submissions.arvi_repeated_marks_20261024.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_20261024.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_20261024.Finite.SourceValid2
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section
open scoped Classical BigOperators
theorem max_product_of_subproducts_rm {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (w : Slot→ℝ) (a : Row→Slot→ℝ)
    (ν F U A loss B lam h : ℝ) (hlam : 1<lam) (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hU : 1≤U) (hA : 0≤A)
    (hw : ∀s∈slots,0≤w s) (ha : ∀u∈rows,∀s∈slots,0≤a u s)
    (hsub : ∀selected : Finset Slot,selected⊆slots →
      (∑u∈rows,∏s∈selected,a u s)≤A*U^(rho ν+ν*(∑s∈selected,w s)-QRH.RepeatedMarks.Source.gainC ν B lam h (∑s∈selected,w s) F+loss)) :
    (∑u∈rows,∏s∈slots,max 1 (a u s)) ≤
      (2^slots.card : ℝ)*A*U^(rho ν+ν*(∑s∈slots,w s)-QRH.RepeatedMarks.Source.gainC ν B lam h (∑s∈slots,w s) F+loss) := by
  have hwidth (selected : Finset Slot) (hs : selected⊆slots) :
      (∑s∈selected,w s)≤∑s∈slots,w s :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun s hs _=>hw s hs)
  have hone (selected : Finset Slot) (hs : selected⊆slots) :
      (∑u∈rows,∏s∈selected,a u s) ≤
        A*U^(rho ν+ν*(∑s∈slots,w s)-QRH.RepeatedMarks.Source.gainC ν B lam h (∑s∈slots,w s) F+loss) :=
    (hsub selected hs).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU
        (by linarith [weighted_exponent_mono_rm (B:=B) (h:=h) (Q:=F) hν0 hν1 hlam (hwidth selected hs)])) hA)
  calc
    _ ≤ ∑u∈rows,∏s∈slots,(1+a u s) := by
      apply Finset.sum_le_sum
      intro u hu
      exact Finset.prod_le_prod₀ (fun s hs=>le_trans (by norm_num) (le_max_left _ _))
        (fun s hs=>max_le (by linarith [ha u hu s hs]) (by linarith))
    _ = ∑u∈rows,∑selected∈slots.powerset,∏s∈selected,a u s := by
      apply Finset.sum_congr rfl
      intro u hu
      exact Finset.prod_one_add slots
    _ = ∑selected∈slots.powerset,∑u∈rows,∏s∈selected,a u s := Finset.sum_comm
    _ ≤ ∑selected∈slots.powerset,
        A*U^(rho ν+ν*(∑s∈slots,w s)-QRH.RepeatedMarks.Source.gainC ν B lam h (∑s∈slots,w s) F+loss) :=
      Finset.sum_le_sum (fun selected hs=>hone selected (Finset.mem_powerset.mp hs))
    _ = _ := by simp [Finset.card_powerset,mul_assoc]

end
end QRH.Record1252270103Source.High
