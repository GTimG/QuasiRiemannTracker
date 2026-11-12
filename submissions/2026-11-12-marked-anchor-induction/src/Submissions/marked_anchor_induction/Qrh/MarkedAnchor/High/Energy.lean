/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Price
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# High.Energy

Assembly of the HIGH energy from the class counts.

* `energy_le_classes`: a nonnegative row sum over finitely many classes, each with
  `#rows ≤ K Z^(N c)` and every row term `≤ K' Z^(P c)`, is `≤ #classes · K K' Z^E` when
  `N c + P c ≤ E` for every class.
* `restored_le`: restoring sixth powers. A core of width `v ∈ (0, M]` whose relative count rate is
  `max (1 - ν w - e min(σ(w), s/v)) (1/6 + (5/6-ν) t)` gives the absolute exponent
  `(M-v)/6 + v·rate ≤ max (shortCnt …) (longCnt …)` (both rates `≥ 1/6` after the `max`).
* `tiny_exponent`: the tiny-core exponent for cores of width `v ≤ 2/25`.
* `class_exponent`, `high_class_exponent`: count + pointwise `≤ M + detEx` resp. `≤ M + highPriceF + ε'`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped BigOperators

/-- **Class summation.** -/
theorem energy_le_classes {ι κ : Type*} [DecidableEq κ] (rows : Finset ι) (cls : ι → κ)
    (cs : Finset κ) (hcls : ∀ u ∈ rows, cls u ∈ cs) (f : ι → ℝ) (hf : ∀ u ∈ rows, 0 ≤ f u)
    (N P : κ → ℝ) (K K' Z E : ℝ) (hZ : 1 ≤ Z) (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hcount : ∀ c ∈ cs, ((rows.filter fun u => cls u = c).card : ℝ) ≤ K * Z ^ (N c))
    (hpt : ∀ u ∈ rows, f u ≤ K' * Z ^ (P (cls u))) (hE : ∀ c ∈ cs, N c + P c ≤ E) :
    ∑ u ∈ rows, f u ≤ (cs.card : ℝ) * K * K' * Z ^ E := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  rw [← Finset.sum_fiberwise_of_maps_to hcls]
  have hc : ∀ c ∈ cs, ∑ u ∈ rows.filter (fun u => cls u = c), f u ≤ K * K' * Z ^ E := by
    intro c hc
    have h1 : ∑ u ∈ rows.filter (fun u => cls u = c), f u ≤
        ∑ u ∈ rows.filter (fun u => cls u = c), K' * Z ^ (P c) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [← hu.2]
      exact hpt u hu.1
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : ((rows.filter fun u => cls u = c).card : ℝ) * (K' * Z ^ (P c)) ≤
        K * Z ^ (N c) * (K' * Z ^ (P c)) :=
      mul_le_mul_of_nonneg_right (hcount c hc) (mul_nonneg hK' (Real.rpow_nonneg hZ0.le _))
    have h3 : K * Z ^ (N c) * (K' * Z ^ (P c)) = K * K' * Z ^ (N c + P c) := by
      rw [Real.rpow_add hZ0]; ring
    have h4 : K * K' * Z ^ (N c + P c) ≤ K * K' * Z ^ E :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (hE c hc)) (mul_nonneg hK hK')
    linarith
  calc ∑ c ∈ cs, ∑ u ∈ rows.filter (fun u => cls u = c), f u ≤ ∑ c ∈ cs, K * K' * Z ^ E :=
        Finset.sum_le_sum hc
    _ = (cs.card : ℝ) * K * K' * Z ^ E := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Restoring sixth powers** at core width `v ∈ (0, M]`, relative supply `s/v ≥ s/M`. -/
theorem restored_le {a0 a1 ν e w s M v : ℝ} (hv : 0 < v) (hvM : v ≤ M) (hν : ν ≤ 3 / 4)
    (he0 : 0 ≤ e) (hs : 0 ≤ s) (hw : w ∈ cutoffs) :
    (M - v) / 6 + v * max (1 - ν * w - e * min (sig a0 a1 w) (s / v))
        (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000)) ≤
      max (shortCnt a0 a1 ν e w s M) (longCnt ν w M) := by
  obtain ⟨hw1, hw2⟩ := hw
  unfold cutLo at hw1; unfold cutHi at hw2
  have hM : 0 < M := hv.trans_le hvM
  set B := 1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) with hBdef
  set A := 1 - ν * w - e * min (sig a0 a1 w) (s / v) with hAdef
  have hB : 1 / 6 ≤ B := by rw [hBdef]; nlinarith
  have hlong : longCnt ν w M = M * B := by unfold longCnt; rw [hBdef]; ring
  have hshort : M * A ≤ shortCnt a0 a1 ν e w s M := by
    unfold shortCnt
    rw [hAdef]
    have hσ := sig_nonneg a0 a1 w
    have hm : min (M * sig a0 a1 w) s ≤ M * min (sig a0 a1 w) (s / v) := by
      rw [mul_min_of_nonneg _ _ hM.le]
      apply min_le_min le_rfl
      rw [mul_div_assoc', le_div_iff₀ hv]
      nlinarith
    have hm' : min s (M * sig a0 a1 w) ≤ M * min (sig a0 a1 w) (s / v) := by
      rw [min_comm]; exact hm
    have := mul_le_mul_of_nonneg_left hm' he0
    nlinarith
  rcases le_total A B with hAB | hAB
  · rw [max_eq_right hAB]
    have : (M - v) / 6 + v * B ≤ M * B := by nlinarith
    calc (M - v) / 6 + v * B ≤ M * B := this
      _ = longCnt ν w M := hlong.symm
      _ ≤ _ := le_max_right _ _
  · rw [max_eq_left hAB]
    rcases le_total (1 / 6) A with hA | hA
    · have : (M - v) / 6 + v * A ≤ M * A := by nlinarith
      exact this.trans (hshort.trans (le_max_left _ _))
    · have : (M - v) / 6 + v * A ≤ M * B := by nlinarith
      calc (M - v) / 6 + v * A ≤ M * B := this
        _ = longCnt ν w M := hlong.symm
        _ ≤ _ := le_max_right _ _

/-- Tiny cores of width `v ≤ 2/25`: count `(M-v)/6 + v`, pointwise `(3/4) P + s`. -/
theorem tiny_exponent {P s M v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 2 / 25) :
    ((M - v) / 6 + v) + (3 / 4 * P + s) ≤ M + tinyEx P s M := by
  unfold tinyEx; linarith

/-- Count plus pointwise exponent of a detector class is `M + detEx`. -/
theorem class_exponent {a0 a1 ν e w P s M N Q l1 l2 : ℝ}
    (hN : N ≤ max (shortCnt a0 a1 ν e w s M) (longCnt ν w M) + l1)
    (hQ : Q ≤ ν * P + e * s + l2) :
    N + Q ≤ M + detEx a0 a1 ν e w P s M + l1 + l2 := by
  unfold detEx; linarith

/-- The same with the cutoff chosen by `exists_cutoff`: `≤ M + highPriceF + ε' + l1 + l2`. -/
theorem high_class_exponent {a0 a1 k ν e w P s M N Q l1 l2 ε' : ℝ}
    (hw : detEx a0 a1 ν e w P s M < highPriceF a0 a1 k P s M + ε')
    (hN : N ≤ max (shortCnt a0 a1 ν e w s M) (longCnt ν w M) + l1)
    (hQ : Q ≤ ν * P + e * s + l2) :
    N + Q ≤ M + highPriceF a0 a1 k P s M + ε' + l1 + l2 := by
  have := class_exponent (a0 := a0) (a1 := a1) hN hQ
  linarith

/-- Tiny cores against the price. -/
theorem tiny_class_exponent {a0 a1 k P s M v N Q l1 l2 : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 2 / 25)
    (hN : N ≤ (M - v) / 6 + v + l1) (hQ : Q ≤ 3 / 4 * P + s + l2) :
    N + Q ≤ M + highPriceF a0 a1 k P s M + l1 + l2 := by
  have h1 := tiny_exponent (P := P) (s := s) (M := M) hv0 hv
  have h2 := tinyEx_le_highPriceF a0 a1 k P s M
  linarith

end
end Qrh.MarkedAnchor.High
