/- Modified by Joseph Bebel (2026-11-12): smaller-tolerance inverse
HIGH leaf; original coefficient, mask and principal-row proofs are retained. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Leaf.HighInput

/-!
# High.Inverse.Bin — the buffered zero bin of one inverse HIGH row

The ordinary leaf reads its zero bins off the packed state (`selectBin`). The inverse leaf has no
packed state; it bins each row itself:

* `exists_stable_cell` — pigeonhole over heights: a real sequence `f` with `f i0 ≥ lo`,
  `f (i0+N+1) ≤ hi`, `hi - lo ≤ N h`, stays in ONE cell `[g0 + p h, g0 + p h + h)` of the grid of
  step `h` over some step `j → j+1`, `j ∈ [i0, i0+N]`.
* `exists_zero_bin` — the instance `f j = zeroMaximum χ ((3j) T)` (values in `[51/100, 1]`), grid
  `g0 = (1+k)/2`, step `2e`: there are `j ∈ [i0, i0 + N]` and `p : ℤ` with
  `a := (1+k)/2 + p·2e`, the lower guard `a ≤ zeroMaximum χ ((3j) T)` (witness of real part `a`)
  and the upper guard `zeroMaximum χ (3(j+1) T) < a + 2e` (pointwise bound / slot envelope), in
  exactly the form of `High.LeafCoreBatch.core_batch_class` and `High.Inverse.inverse_row_pointwise`.
* `slotHigh_lt` / `bin_ge_of_slotHigh` — the LOW slot supplier in abstract form: if every slot of
  the row obeys the envelope `‖slot‖² ≤ A Z^((2(a+2e)-1) ell + lam')` with `lam' < lam`, `A ≤ c`,
  then a `SlotHigh c lam k` row has `k < 2(a+2e)-1`; on the grid this forces `p ≥ 0`, i.e.
  `(1+k)/2 ≤ a`: the row's class `ν = 2a-1` is a price class (`ν ≥ k`).
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Inverse
noncomputable section

open OAI OAI.SevenEighths HeckeFamily
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Inverse.Leaf
local notation "O" => HeckeFamily.O

/-- **Pigeonhole over heights.** -/
theorem exists_stable_cell (f : ℕ → ℝ) (g0 h lo hi : ℝ) (hh : 0 < h) (i0 N : ℕ)
    (hlo : lo ≤ f i0) (hhi : f (i0+N+1) ≤ hi) (hN : hi - lo ≤ N*h) :
    ∃ j : ℕ, i0 ≤ j ∧ j ≤ i0 + N ∧ ∃ p : ℤ, g0 + p*h ≤ f j ∧ f (j+1) < g0 + p*h + h := by
  by_contra hcon
  push Not at hcon
  set p0 : ℤ := ⌊(f i0 - g0)/h⌋ with hp0
  have hfl : g0 + (p0 : ℝ)*h ≤ f i0 := by
    have := Int.floor_le ((f i0 - g0)/h)
    rw [← hp0] at this
    have := mul_le_mul_of_nonneg_right this hh.le
    rw [div_mul_cancel₀ _ hh.ne'] at this
    linarith
  have hfl' : f i0 < g0 + ((p0 : ℝ) + 1)*h := by
    have := Int.lt_floor_add_one ((f i0 - g0)/h)
    rw [← hp0] at this
    have := mul_lt_mul_of_pos_right this hh
    rw [div_mul_cancel₀ _ hh.ne'] at this
    linarith
  have hstep : ∀ m : ℕ, m ≤ N+1 → g0 + ((p0 + m : ℤ) : ℝ)*h ≤ f (i0+m) := by
    intro m
    induction m with
    | zero => intro _; simpa using hfl
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hcon (i0+m) (by omega) (by omega) (p0 + m) h1
      have e : i0 + (m+1) = i0 + m + 1 := by omega
      rw [e]
      push_cast at h2 ⊢
      linarith
  have hlast := hstep (N+1) le_rfl
  have e : i0 + (N+1) = i0 + N + 1 := by omega
  rw [e] at hlast
  push_cast at hlast
  nlinarith

/-- **The zero bin of a row family**: some height step in `[i0, i0+N]` has both buffered guards
at a grid value `a = (1+k)/2 + p·2e`. -/
theorem exists_zero_bin {ι : Type*} [Fintype ι] (χ : ι → Character)
    (hχ : ∀ j, (χ j).residue ≠ 1) (T k e : ℝ) (he : 0 < e) (i0 N : ℕ)
    (hN : (49/100 : ℝ) ≤ N*(2*e)) :
    ∃ j : ℕ, i0 ≤ j ∧ j ≤ i0 + N ∧ ∃ p : ℤ,
      (1+k)/2 + p*(2*e) ≤ HeckeDetectorZeros.zeroMaximum χ hχ ((3*j : ℕ)*T) ∧
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(j+1 : ℕ)*T) < (1+k)/2 + p*(2*e) + 2*e := by
  let f : ℕ → ℝ := fun j => HeckeDetectorZeros.zeroMaximum χ hχ ((3*j : ℕ)*T)
  obtain ⟨j, hj1, hj2, p, hp1, hp2⟩ := exists_stable_cell f ((1+k)/2) (2*e) (51/100) 1
    (by positivity) i0 N (HeckeDetectorZeros.zeroMaximum_bounds χ hχ _).1
    (HeckeDetectorZeros.zeroMaximum_bounds χ hχ _).2 (by linarith)
  refine ⟨j, hj1, hj2, p, hp1, ?_⟩
  have e1 : (3*(j+1 : ℕ)*T : ℝ) = ((3*(j+1) : ℕ) : ℝ)*T := by push_cast; ring
  rw [e1]
  exact hp2

/-- **LOW slot supplier, abstract form**: a `SlotHigh` row whose slots obey the envelope of the
upper guard `a + h` has `k < 2(a+h)-1`. -/
theorem slotHigh_lt {c lam k Z A lam' a h : ℝ} (hZ : 1 < Z) (hA : 0 < A) (hcA : A ≤ c)
    (hlam : lam' < lam) {ι : Type} {L : ι → Finset (Ideal O)} {ell : ι → ℝ}
    {β : ι → Ideal O → ℂ} {u : HeckeInverseAmplification.NonzeroElement}
    (hell : ∀ i, 0 ≤ ell i)
    (henv : ∀ i, ‖directSlot u.val (L i) (β i) (Z^(ell i))‖^2 ≤
      A * Z^((2*(a+h)-1)*ell i + lam'))
    (hhigh : SlotHigh c lam k Z L ell β u) : k < 2*(a+h)-1 := by
  obtain ⟨i, hi⟩ := hhigh
  have h1 : c * Z^(k * ell i + lam) < A * Z^((2*(a+h)-1)*ell i + lam') :=
    hi.trans_le (henv i)
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have h2 : A * Z^(k * ell i + lam) ≤ c * Z^(k * ell i + lam) :=
    mul_le_mul_of_nonneg_right hcA (Real.rpow_nonneg hZ0.le _)
  have h3 : Z^(k * ell i + lam) < Z^((2*(a+h)-1)*ell i + lam') :=
    lt_of_mul_lt_mul_left (h2.trans_lt h1) hA.le
  have h4 : k * ell i + lam < (2*(a+h)-1)*ell i + lam' :=
    (Real.rpow_lt_rpow_left_iff hZ).mp h3
  by_contra hk
  push Not at hk
  have := mul_le_mul_of_nonneg_right hk (hell i)
  linarith

/-- On the grid of step `h` based at `(1+k)/2`, `k < 2(a+h)-1` forces `(1+k)/2 ≤ a`. -/
theorem grid_ge {k h : ℝ} (hh : 0 < h) (p : ℤ) (hk : k < 2*((1+k)/2 + p*h + h) - 1) :
    (1+k)/2 ≤ (1+k)/2 + p*h ∧ 0 ≤ p := by
  have h1 : 0 < ((p : ℝ) + 1)*h := by linarith
  have h2 : (-1 : ℝ) < p := by
    by_contra hc
    push Not at hc
    have : ((p : ℝ) + 1)*h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hh.le
    linarith
  have h3 : (-1 : ℤ) < p := by exact_mod_cast h2
  have h4 : (0 : ℤ) ≤ p := by omega
  have h5 : (0 : ℝ) ≤ p := by exact_mod_cast h4
  exact ⟨by nlinarith, h4⟩

/-- **The class of a HIGH row is a price class**: with the bin `a = (1+k)/2 + p·2e` of
`exists_zero_bin` and the slot envelope of its upper guard, a `SlotHigh` row has `p ≥ 0`, i.e.
`ν = 2a - 1 ≥ k`. -/
theorem bin_ge_of_slotHigh {c lam k Z A lam' e : ℝ} (hZ : 1 < Z) (hA : 0 < A) (hcA : A ≤ c)
    (hlam : lam' < lam) (he : 0 < e) (p : ℤ) {ι : Type} {L : ι → Finset (Ideal O)}
    {ell : ι → ℝ} {β : ι → Ideal O → ℂ} {u : HeckeInverseAmplification.NonzeroElement}
    (hell : ∀ i, 0 ≤ ell i)
    (henv : ∀ i, ‖directSlot u.val (L i) (β i) (Z^(ell i))‖^2 ≤
      A * Z^((2*(((1+k)/2 + p*(2*e)) + 2*e)-1)*ell i + lam'))
    (hhigh : SlotHigh c lam k Z L ell β u) :
    k ≤ 2*((1+k)/2 + p*(2*e)) - 1 ∧ 0 ≤ p := by
  have h := slotHigh_lt hZ hA hcA hlam hell henv hhigh
  obtain ⟨h1, h2⟩ := grid_ge (by positivity : (0:ℝ) < 2*e) p h
  exact ⟨by linarith, h2⟩

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Inverse

#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.exists_stable_cell
#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.exists_zero_bin
#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.bin_ge_of_slotHigh
