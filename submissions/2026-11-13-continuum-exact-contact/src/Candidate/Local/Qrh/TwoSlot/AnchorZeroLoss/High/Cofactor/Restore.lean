/- Modified by Joseph Bebel (2026-11-12): positive source and detector
pads for the stronger anchor target. The actual physical coefficient,
mask and height contracts are preserved. Inherited attribution follows. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Energy

/-!
# High.Cofactor.Restore

Price-level restoration of sixth powers (at core width `v` the exponent is
`(H-v)/6 + v·rate ≤ H·rate`).

A raw HIGH row `z = f⁶c` with sixth-free core `c` of norm `Z^d` and cofactor `N(f) = Z^((M-d)/6)`
is counted inside the core batch at radius `d`; the `Z^((M-d)/6)` cofactors are paid by
* `restored_price_le`: `(M-d)/6 + d + highPriceF(P,S,d) ≤ M + highPriceF(P,S,M)` (`0 < d ≤ M`);
* `tiny_restored_le`: `(M-d)/6 + (d + (3/4)P + S) ≤ M + highPriceF(P,S,M)` (`0 ≤ d ≤ 2/25`).

The core batch price of `High.Batch.anchor_batch_price` is relative (radius `1`, widths `P/d`,
`S/d`); `scaled_detPrice` / `scaled_highPriceF_le` / `scaled_maxDet_le` convert it:
`d · highPriceF(P/d,S/d,1) ≤ highPriceF(P,S,d)` for `0 < d ≤ 1`, and
`d · max 0 (detPrice(P/d,S/d,1)) ≤ highPriceF(P,S,d)` for every `d > 0`.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Cofactor
noncomputable section
variable [shift : WitnessShift]

open Qrh.TwoSlot.AnchorZeroLoss.High

variable {a0 a1 k : ℝ}

/-- Homogeneity of the detector excess. -/
theorem detEx_scale (ν e w P S : ℝ) {d : ℝ} (hd : 0 < d) :
    d * detEx a0 a1 ν e w (P / d) (S / d) 1 = detEx a0 a1 ν e w P S d := by
  have hd0 : d ≠ 0 := hd.ne'
  have hs : d * shortCnt a0 a1 ν e w (S / d) 1 = shortCnt a0 a1 ν e w S d := by
    unfold shortCnt
    have h1 : d * min (S / d) (1 * sig a0 a1 w) = min S (d * sig a0 a1 w) := by
      rw [one_mul, mul_min_of_nonneg _ _ hd.le, mul_div_cancel₀ _ hd0]
    linear_combination (-e) * h1
  have hl : d * longCnt ν w 1 = longCnt ν w d := by unfold longCnt; ring
  have hP : d * (ν * (P / d)) = ν * P := by field_simp
  have hS : d * (e * (S / d)) = e * S := by field_simp
  unfold detEx
  rw [mul_sub, mul_add, mul_add, mul_max_of_nonneg _ _ hd.le, hs, hl, hP, hS, mul_one]

/-- The detector excess at core radius `d` plus the cofactor count `(M-d)/6` is at most the
excess at radius `M` (`High.restored_le`, both rates `≥ 1/6`). -/
theorem detEx_restored {ν e w P S d M : ℝ} (hd : 0 < d) (hdM : d ≤ M) (hν : ν ≤ 3 / 4)
    (he : 0 ≤ e) (hS : 0 ≤ S) (hw : w ∈ cutoffs) :
    detEx a0 a1 ν e w P S d ≤ detEx a0 a1 ν e w P S M + 5 * (M - d) / 6 := by
  have hr := restored_le (a0 := a0) (a1 := a1) (e := e) hd hdM hν he hS hw
  have hd0 : d ≠ 0 := hd.ne'
  have hs : shortCnt a0 a1 ν e w S d =
      d * (1 - ν * w - e * min (sig a0 a1 w) (S / d)) := by
    unfold shortCnt
    have h1 : d * min (sig a0 a1 w) (S / d) = min S (d * sig a0 a1 w) := by
      rw [mul_min_of_nonneg _ _ hd.le, mul_div_cancel₀ _ hd0, min_comm]
    linear_combination e * h1
  have hl : longCnt ν w d = d * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + WitnessShift.value)) := by
    unfold longCnt; ring
  have hmax : max (shortCnt a0 a1 ν e w S d) (longCnt ν w d) =
      d * max (1 - ν * w - e * min (sig a0 a1 w) (S / d))
        (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + WitnessShift.value)) := by
    rw [hs, hl, mul_max_of_nonneg _ _ hd.le]
  unfold detEx
  rw [hmax]
  linarith

/-- **Restoring sixth powers, price form.** -/
theorem restored_price_le (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P S d M : ℝ} (hd : 0 < d)
    (hdM : d ≤ M) (hS : 0 ≤ S) :
    (M - d) / 6 + d + highPriceF a0 a1 k P S d ≤ M + highPriceF a0 a1 k P S M := by
  have h := highPriceF_le_add (a0 := a0) (a1 := a1) (P := P) (s := S) (M := M) (P' := P)
    (s' := S) (M' := d) (c := 5 * (M - d) / 6) hk0 hk1 (by linarith)
    (by unfold tinyEx; linarith) (fun p hp w hw => by
      obtain ⟨h1, h2, h3, h4⟩ := hp
      exact detEx_restored hd hdM h2 h3 hS hw)
  linarith

/-- **Tiny cores**: cores of width `d ≤ 2/25` are counted trivially (`Z^d`) and paid
pointwise by `(3/4) P + S`. -/
theorem tiny_restored_le {P S d M : ℝ} (_hd0 : 0 ≤ d) (hd : d ≤ 2 / 25) :
    (M - d) / 6 + (d + 3 / 4 * P + S) ≤ M + highPriceF a0 a1 k P S M := by
  have := tinyEx_le_highPriceF a0 a1 k P S M
  unfold tinyEx at this
  linarith

/-- Relative detector price at radius `1` versus the absolute one at radius `d`. -/
theorem scaled_detPrice (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P S d : ℝ} (hd : 0 < d) :
    d * detPrice a0 a1 k (P / d) (S / d) 1 ≤ detPrice a0 a1 k P S d := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have key : detPrice a0 a1 k (P / d) (S / d) 1 ≤ (detPrice a0 a1 k P S d + ε) / d := by
    refine detPrice_le_of hk0 hk1 fun p hp => ?_
    have h1 := infW_le_detPrice (a0 := a0) (a1 := a1) hk0 hp P S d
    obtain ⟨w, hw, hlt⟩ := exists_lt_infW
      (show infW (fun w => detEx a0 a1 p.1 p.2 w P S d) <
        infW (fun w => detEx a0 a1 p.1 p.2 w P S d) + ε by linarith)
    refine ⟨w, hw, ?_⟩
    rw [le_div_iff₀ hd, mul_comm, detEx_scale p.1 p.2 w P S hd]
    linarith
  rw [le_div_iff₀ hd] at key
  linarith

/-- `d · max 0 (detPrice(P/d,S/d,1)) ≤ highPriceF(P,S,d)` for every `d > 0`. -/
theorem scaled_maxDet_le (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P S d : ℝ} (hd : 0 < d) :
    d * max 0 (detPrice a0 a1 k (P / d) (S / d) 1) ≤ highPriceF a0 a1 k P S d := by
  rw [mul_max_of_nonneg _ _ hd.le, mul_zero]
  exact max_le (highPriceF_nonneg a0 a1 k P S d)
    ((scaled_detPrice hk0 hk1 hd).trans (detPrice_le_highPriceF a0 a1 k P S d))

/-- `d · highPriceF(P/d,S/d,1) ≤ highPriceF(P,S,d)` for `0 < d ≤ 1` (the tiny term is not
homogeneous: its constant `1/15` is absolute). -/
theorem scaled_highPriceF_le (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P S d : ℝ} (hd : 0 < d)
    (hd1 : d ≤ 1) :
    d * highPriceF a0 a1 k (P / d) (S / d) 1 ≤ highPriceF a0 a1 k P S d := by
  have hd0 : d ≠ 0 := hd.ne'
  have ht : d * tinyEx (P / d) (S / d) 1 ≤ tinyEx P S d := by
    have e1 : d * tinyEx (P / d) (S / d) 1 = d / 6 + d / 15 + 3 / 4 * P + S - d := by
      unfold tinyEx; field_simp
    rw [e1]; unfold tinyEx; linarith
  unfold highPriceF
  rw [mul_max_of_nonneg _ _ hd.le, mul_max_of_nonneg _ _ hd.le, mul_zero]
  refine max_le_max le_rfl (max_le_max ht (scaled_detPrice hk0 hk1 hd))

/-- The core batch exponent of `anchor_batch_price` (relative price, radius `Z^d`) restored to
the raw row radius `Z^M`, for core widths `d ∈ (0, min 1 M]`. -/
theorem core_restored_le (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P S d M : ℝ} (hd : 0 < d)
    (hdM : d ≤ M) (hd1 : d ≤ 1) (hS : 0 ≤ S) :
    (M - d) / 6 + d * (1 + highPriceF a0 a1 k (P / d) (S / d) 1) ≤
      M + highPriceF a0 a1 k P S M := by
  have h1 := scaled_highPriceF_le (a0 := a0) (a1 := a1) (P := P) (S := S) hk0 hk1 hd hd1
  have h2 := restored_price_le (a0 := a0) (a1 := a1) (P := P) hk0 hk1 hd hdM hS
  nlinarith

/-- The same with the detector part only, for every `d ∈ (0, M]`. -/
theorem core_restored_le_det (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P S d M : ℝ} (hd : 0 < d)
    (hdM : d ≤ M) (hS : 0 ≤ S) :
    (M - d) / 6 + d * (1 + max 0 (detPrice a0 a1 k (P / d) (S / d) 1)) ≤
      M + highPriceF a0 a1 k P S M := by
  have h1 := scaled_maxDet_le (a0 := a0) (a1 := a1) (P := P) (S := S) hk0 hk1 hd
  have h2 := restored_price_le (a0 := a0) (a1 := a1) (P := P) hk0 hk1 hd hdM hS
  nlinarith

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Cofactor
