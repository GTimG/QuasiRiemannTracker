/- Modified by Joseph Bebel (2026-11-12): generic child-price ledger
for the smaller-tolerance HIGH source, independent of a stage table. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.PriceFloor
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Leaf.Stage

/-!
# Generic inverse child ledger

The radius shift from `H` to `H-κ` costs at most `6νκ` in each detector
class. The free-width decrement pays that cost when `8κ≤β`. The retained
`child_highPriceFW_le` theorem covers the entire child rectangle, including
tiny cores and every permitted class/cutoff; no numerical stage is assumed.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Inverse
noncomputable section
variable [shift : WitnessShift]

open Qrh.TwoSlot.AnchorZeroLoss.High
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Inverse.Leaf

/-- Homogeneity of `detEx` (as `High.BatchAbs.detEx_homog`). -/
theorem detEx_homog' (a0 a1 ν e w x y M : ℝ) (hM : 0 < M) :
    detEx a0 a1 ν e w (M*x) (M*y) M = M * detEx a0 a1 ν e w x y 1 := by
  have h1 : min (M*y) (M*sig a0 a1 w) = M * min y (sig a0 a1 w) :=
    (mul_min_of_nonneg _ _ hM.le).symm
  have hA : M - ν*M*w - e*(M*min y (sig a0 a1 w)) =
      M*(1 - ν*1*w - e*min y (1*sig a0 a1 w)) := by rw [one_mul]; ring
  have hB : M/6 + (5/6-ν)*M*(3*w/2 + WitnessShift.value) =
      M*(1/6 + (5/6-ν)*1*(3*w/2 + WitnessShift.value)) := by ring
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
  have hshift0 := WitnessShift.pos
  have hB : (H-κ)*(1/6 + (5/6-ν)*(3*w/2 + WitnessShift.value) - 1) ≤
      H*(1/6 + (5/6-ν)*(3*w/2 + WitnessShift.value) - 1) + 6*ν*κ := by
    have hc : 0 ≤ (5/6-ν)*(3*w/2 + WitnessShift.value) := mul_nonneg (by linarith) (by positivity)
    have hκc : -(κ*(5/6-ν)*(3*w/2 + WitnessShift.value)) ≤ 0 := by
      have := mul_nonneg hκ0 hc
      linarith [mul_assoc κ (5/6-ν) (3*w/2 + WitnessShift.value)]
    nlinarith
  have := max_le_max hA hB
  have e1 : max (-(ν*H*w) - e*min s (H*σ) + 6*ν*κ)
      (H*(1/6 + (5/6-ν)*(3*w/2 + WitnessShift.value) - 1) + 6*ν*κ) =
      max (-(ν*H*w) - e*min s (H*σ)) (H*(1/6 + (5/6-ν)*(3*w/2 + WitnessShift.value) - 1)) + 6*ν*κ :=
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


end
end Qrh.TwoSlot.AnchorZeroLoss.High.Inverse
