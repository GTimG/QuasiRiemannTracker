/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.PriceFloor
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Leaf.Chain

/-!
# High.Inverse.Ledger — the scalar ledger of the inverse HIGH child

The inverse child of chain stage `n` at the point `r` lives on `chainChildRect n r β κ`, normalized
at radius `1` (physically radius `Hc = 1-6u-κ = H-κ`, `H = r/R`): free width `Hc·P ≤ r-β+2κ`, marks
`Hc·S ≤ s-δ-β+3κ ≤ s` (`s = fs`, `δ = 4·10^-8`). Its HIGH price must be at most the excess
`chainExcess n r κ = u/(1-6u-κ)`.

* `detEx_child` — one class `(ν, e)` at one cutoff `w`: if `detEx(w, r, s, H) ≤ u` (the stage
  ledger at radius `H`) then `detEx(w, P, S, 1) ≤ u/(H-κ)`, for `5/36 ≤ ν ≤ 3/4`, `0 ≤ e ≤ ν`,
  `w + sig(w) ≤ 6`, `8κ ≤ β`. The radius shift `H → H-κ` costs at most `6νκ` (branchwise, sharper
  than `highPriceF_lipM`) and the free-width decrement pays `ν(β-2κ)`.
* `tinyEx_child` — the tiny cores at the child scale.
* `child_highPriceFW_le` — the floored price from the per-class data.
* **`chain_child_price_le`** — for every `(P, S)` admitted by `chainChildRect n r β κ` at radius `1`:
  `highPriceFW (a0 n) (a1 n) (cut n) (R n + 10^-6) P S 1 ≤ chainExcess n r κ`, with the chain
  cutoffs `fw … r ν` (`≥ R n + 10^-6`) and the gates of `High.Gates` / `Price.stageHyp_chain`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Inverse
noncomputable section

open Qrh.MarkedAnchor.High
open Qrh.MarkedAnchor.Anchor ChainData ChainCheck
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Inverse.Leaf

/-- Homogeneity of `detEx` (as `High.BatchAbs.detEx_homog`). -/
theorem detEx_homog' (a0 a1 ν e w x y M : ℝ) (hM : 0 < M) :
    detEx a0 a1 ν e w (M*x) (M*y) M = M * detEx a0 a1 ν e w x y 1 := by
  have h1 : min (M*y) (M*sig a0 a1 w) = M * min y (sig a0 a1 w) :=
    (mul_min_of_nonneg _ _ hM.le).symm
  have hA : M - ν*M*w - e*(M*min y (sig a0 a1 w)) =
      M*(1 - ν*1*w - e*min y (1*sig a0 a1 w)) := by rw [one_mul]; ring
  have hB : M/6 + (5/6-ν)*M*(3*w/2 + 1/1000000) =
      M*(1/6 + (5/6-ν)*1*(3*w/2 + 1/1000000)) := by ring
  unfold detEx shortCnt longCnt
  rw [h1, hA, hB, ← mul_max_of_nonneg _ _ hM.le]
  ring

/-- The radius shift `H → H - κ` of one detector excess costs at most `6νκ`. -/
theorem detEx_shift {a0 a1 ν e w r s H κ : ℝ} (hν5 : 5/36 ≤ ν) (hν1 : ν ≤ 3/4) (he0 : 0 ≤ e)
    (he : e ≤ ν) (hw0 : 0 ≤ w) (hwσ : w + sig a0 a1 w ≤ 6) (hκ0 : 0 ≤ κ) :
    detEx a0 a1 ν e w r s (H - κ) ≤ detEx a0 a1 ν e w r s H + 6*ν*κ := by
  rw [detEx_eq, detEx_eq]
  have hσ0 := sig_nonneg a0 a1 w
  generalize sig a0 a1 w = σ at hσ0 hwσ ⊢
  have hmin : min s (H*σ) ≤ min s ((H-κ)*σ) + κ*σ := by
    have hk : 0 ≤ κ*σ := mul_nonneg hκ0 hσ0
    rcases le_total s ((H-κ)*σ) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by linarith)
  have hA : -(ν*(H-κ)*w) - e*min s ((H-κ)*σ) ≤ -(ν*H*w) - e*min s (H*σ) + 6*ν*κ := by
    have h1 : e*min s (H*σ) ≤ e*min s ((H-κ)*σ) + e*(κ*σ) := by
      have := mul_le_mul_of_nonneg_left hmin he0
      linarith
    have h2 : e*(κ*σ) ≤ ν*(κ*σ) := mul_le_mul_of_nonneg_right he (mul_nonneg hκ0 hσ0)
    have h3 : ν*κ*(w+σ) ≤ ν*κ*6 :=
      mul_le_mul_of_nonneg_left hwσ (mul_nonneg (by linarith) hκ0)
    nlinarith
  have hB : (H-κ)*(1/6 + (5/6-ν)*(3*w/2 + 1/1000000) - 1) ≤
      H*(1/6 + (5/6-ν)*(3*w/2 + 1/1000000) - 1) + 6*ν*κ := by
    have hc : 0 ≤ (5/6-ν)*(3*w/2 + 1/1000000) := mul_nonneg (by linarith) (by positivity)
    have hκc : -(κ*(5/6-ν)*(3*w/2 + 1/1000000)) ≤ 0 := by
      have := mul_nonneg hκ0 hc
      linarith [mul_assoc κ (5/6-ν) (3*w/2 + 1/1000000)]
    nlinarith
  have := max_le_max hA hB
  have e1 : max (-(ν*H*w) - e*min s (H*σ) + 6*ν*κ)
      (H*(1/6 + (5/6-ν)*(3*w/2 + 1/1000000) - 1) + 6*ν*κ) =
      max (-(ν*H*w) - e*min s (H*σ)) (H*(1/6 + (5/6-ν)*(3*w/2 + 1/1000000) - 1)) + 6*ν*κ :=
    max_add_add_right _ _ _
  rw [e1] at this
  linarith

/-- **One class at one cutoff**: the stage ledger at radius `H` gives the child ledger at radius
`1` (child normalized at `H - κ`). -/
theorem detEx_child {a0 a1 ν e w r s H u β κ P S : ℝ} (hν5 : 5/36 ≤ ν) (hν1 : ν ≤ 3/4)
    (he0 : 0 ≤ e) (he : e ≤ ν) (hw0 : 0 ≤ w) (hwσ : w + sig a0 a1 w ≤ 6) (hκ0 : 0 ≤ κ)
    (hκβ : 8*κ ≤ β) (hHc : 0 < H - κ) (hP : (H-κ)*P ≤ r - β + 2*κ) (hS : (H-κ)*S ≤ s)
    (hdet : detEx a0 a1 ν e w r s H ≤ u) :
    detEx a0 a1 ν e w P S 1 ≤ u/(H-κ) := by
  rw [le_div_iff₀ hHc, mul_comm, ← detEx_homog' a0 a1 ν e w P S (H-κ) hHc]
  have h1 : detEx a0 a1 ν e w ((H-κ)*P) ((H-κ)*S) (H-κ) ≤
      detEx a0 a1 ν e w (r-β+2*κ) ((H-κ)*S) (H-κ) := by
    have := detEx_P a0 a1 ν e w ((H-κ)*P) ((H-κ)*S) (H-κ) ((r-β+2*κ) - (H-κ)*P)
    rw [show (H-κ)*P + ((r-β+2*κ) - (H-κ)*P) = r-β+2*κ by ring] at this
    have : 0 ≤ ν*((r-β+2*κ) - (H-κ)*P) := mul_nonneg (by linarith) (by linarith)
    linarith
  have h2 : detEx a0 a1 ν e w (r-β+2*κ) ((H-κ)*S) (H-κ) ≤
      detEx a0 a1 ν e w (r-β+2*κ) s (H-κ) := by
    have := (detEx_s (a0 := a0) (a1 := a1) (ν := ν) (w := w) he0 (r-β+2*κ) ((H-κ)*S) (H-κ)
      (s - (H-κ)*S) (by linarith)).1
    rwa [show (H-κ)*S + (s - (H-κ)*S) = s by ring] at this
  have h3 : detEx a0 a1 ν e w r s (H-κ) =
      detEx a0 a1 ν e w (r-β+2*κ) s (H-κ) + ν*(β-2*κ) := by
    have := detEx_P a0 a1 ν e w (r-β+2*κ) s (H-κ) (β-2*κ)
    rwa [show r-β+2*κ + (β-2*κ) = r by ring] at this
  have h4 := detEx_shift (r := r) (s := s) (H := H) hν5 hν1 he0 he hw0 hwσ hκ0
  have h5 : ν*(8*κ - β) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  nlinarith

/-- The tiny cores of the child (threshold `2/25` at the child scale). -/
theorem tinyEx_child {r s H u β κ P S : ℝ} (hκ0 : 0 ≤ κ) (hκβ : 8*κ ≤ β) (hHc : 0 < H - κ)
    (hHc1 : H - κ ≤ 1) (hP : (H-κ)*P ≤ r - β + 2*κ) (hS : (H-κ)*S ≤ s)
    (ht : tinyEx r s H ≤ u - 3/100) :
    tinyEx P S 1 ≤ u/(H-κ) := by
  rw [le_div_iff₀ hHc]
  unfold tinyEx at ht ⊢
  have e : (1/6 + 1/15 + 3/4*P + S - 1)*(H-κ) =
      (H-κ)/6 + (H-κ)/15 + 3/4*((H-κ)*P) + (H-κ)*S - (H-κ) := by ring
  rw [e]
  linarith

/-- The floored HIGH price of the child from per-class cutoffs. -/
theorem child_highPriceFW_le {a0 a1 k wlo r s H u β κ P S : ℝ} (hk5 : 5/36 ≤ k)
    (hk1 : k ≤ 3/4) (hu : 0 ≤ u) (hκ0 : 0 ≤ κ) (hκβ : 8*κ ≤ β) (hHc : 0 < H - κ)
    (hHc1 : H - κ ≤ 1) (hP : (H-κ)*P ≤ r - β + 2*κ) (hS : (H-κ)*S ≤ s)
    (ht : tinyEx r s H ≤ u - 3/100)
    (hcut : ∀ p ∈ classes k, ∃ w ∈ cutoffs, wlo ≤ w ∧ w + sig a0 a1 w ≤ 6 ∧
      detEx a0 a1 p.1 p.2 w r s H ≤ u) :
    highPriceFW a0 a1 k wlo P S 1 ≤ u/(H-κ) := by
  have hk0 : 0 ≤ k := by linarith
  have h := highPriceFW_le_of (a0 := a0) (a1 := a1) (wlo := wlo) (P := P) (s := S) (M := 1)
    (c := u/(H-κ)) hk0 hk1 (tinyEx_child hκ0 hκβ hHc hHc1 hP hS ht) (fun p hp => by
      obtain ⟨w, hw, hlo, hwσ, hdet⟩ := hcut p hp
      obtain ⟨h1, h2, h3, h4⟩ := hp
      have hw1 := hw.1
      unfold cutLo at hw1
      exact ⟨w, hw, hlo, detEx_child (by linarith) h2 h3 h4 (by linarith) hwσ hκ0 hκβ hHc hP hS
        hdet⟩)
  exact h.trans (max_le (div_nonneg hu hHc.le) le_rfl)

/-- **The scalar ledger of the inverse HIGH child at chain stage `n`.** Every `(P, S)` admitted by
`chainChildRect n r β κ` at radius `1` has floored HIGH price at most `chainExcess n r κ`. -/
theorem chain_child_price_le (n : ℕ) (hn : n < 176) (r : ℝ) (h1 : (left n : ℝ) ≤ r)
    (h2 : r ≤ R n) (β : ℝ) (_hβ0 : 0 < β) (_hβ1 : β ≤ 1/1000) (κ : ℝ) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ β/8) (P S : ℝ) (hadm : (chainChildRect n r β κ).Admissible P S 1) :
    highPriceFW (a0 n) (a1 n) (cut n) ((R n : ℝ) + 1/1000000) P S 1 ≤ chainExcess n r κ := by
  have hS0 := Qrh.MarkedAnchor.Price.stageHyp_chain n hn r h1 h2
  have h := chain_hyp n hn r h1 h2
  have hu0 := hS0.u_nonneg
  have hu1 := hS0.hu
  have hg2 := hS0.g2
  have hR0 := hS0.R_pos
  have hHeq : fH (R n : ℝ) r = 1 - 6*fu (R n : ℝ) r := hS0.H_eq
  have hHc : 0 < fH (R n : ℝ) r - κ := by rw [hHeq]; linarith
  have hHc' : 1 - 6*fu (R n : ℝ) r - κ = fH (R n : ℝ) r - κ := by rw [hHeq]
  have hHc1 : fH (R n : ℝ) r - κ ≤ 1 := by rw [hHeq]; linarith
  obtain ⟨hP0, hP, hSS0, hS⟩ := hadm
  simp only [chainChildRect, Qrh.MarkedAnchor.Inverse.childRect, mul_one] at hP hS
  rw [hHc'] at hP hS
  have hP' : (fH (R n : ℝ) r - κ)*P ≤ r - β + 2*κ := by
    have := (le_div_iff₀ hHc).mp hP; linarith
  have hS' : (fH (R n : ℝ) r - κ)*S ≤ fs (R n : ℝ) (gain n) (cut n) r := by
    have := (le_div_iff₀ hHc).mp hS
    have e : (1 - r)/2 + (fY (R n : ℝ) (gain n) (cut n) r - 1/25000000) - β - fu (R n : ℝ) r +
        3*κ = fs (R n : ℝ) (gain n) (cut n) r - 1/25000000 - β + 3*κ := by
      simp only [fs, fS]; ring
    linarith
  have hk := chain_cut_mem n hn
  have ht : tinyEx r (fs (R n : ℝ) (gain n) (cut n) r) (fH (R n : ℝ) r) ≤
      fu (R n : ℝ) r - 3/100 := by
    have := Stg.tiny_le h
    rwa [chainStg_r n hn, chainStg_s n hn, chainStg_H n hn, chainStg_u n hn] at this
  have hfs : fs (R n : ℝ) (gain n) (cut n) r ≤ 137/1000 := by
    simp only [fs]; linarith
  unfold chainExcess
  rw [hHc']
  refine child_highPriceFW_le (by linarith [hk.1]) hk.2 hu0 hκ0.le (by linarith) hHc hHc1 hP' hS'
    ht (fun p hp => ?_)
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  obtain ⟨hmem, hdet⟩ := chain_detEx_le n hn r h1 h2 hp1 hp2 hp3 hp4
  refine ⟨_, hmem, ?_, ?_, hdet⟩
  · have := Stg.R_le_w h hp1
    rw [chainStg_w n hn] at this
    exact this
  · have hsup := Stg.sig_le_supply h hp1
    rw [chainStg_w n hn, chainStg_H n hn, chainStg_s n hn] at hsup
    have hσ0 := sig_nonneg (a0 n : ℝ) (a1 n) (fw (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r p.1)
    have hw2 := hmem.2
    unfold cutHi at hw2
    have hH : (1/2 : ℝ) ≤ fH (R n : ℝ) r := by rw [hHeq]; linarith
    have hsup' : fH (R n : ℝ) r *
        sig (a0 n : ℝ) (a1 n) (fw (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r p.1) ≤
        fs (R n : ℝ) (gain n) (cut n) r := hsup
    have : sig (a0 n : ℝ) (a1 n) (fw (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r p.1) ≤ 1 := by
      by_contra hc
      have hc' := lt_of_not_ge hc
      have := mul_lt_mul_of_pos_left hc' (show (0:ℝ) < fH (R n : ℝ) r by linarith)
      linarith
    linarith

end
end Qrh.MarkedAnchor.High.Inverse

#print axioms Qrh.MarkedAnchor.High.Inverse.detEx_child
#print axioms Qrh.MarkedAnchor.High.Inverse.chain_child_price_le
