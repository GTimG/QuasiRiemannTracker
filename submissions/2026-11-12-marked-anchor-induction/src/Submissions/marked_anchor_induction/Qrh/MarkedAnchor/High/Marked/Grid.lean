/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Sources

/-!
# High.Marked.Grid

The sources of the HIGH child of stage `n` with slack, uniformly in the witness width.

* `stage_line`: `0 ≤ a1 n < 2/5`-type facts and `l(TOP) ≤ 0` for every stage.
* `top_native_gates`: for `x ∈ [TOP - 10^-7, 1)` and `0 ≤ S ≤ sig x`, the native inverse gates
  `x + 2S < 1`, `2x + 8S < 3` hold.
* `top_global_face`: one global ordinary source (from `ReserveParametricSource` at `η = 10^-8`)
  admits `x + L S ≤ B`, `S ≤ c` for every `x ∈ [TOP - 10^-7, 1)` and `0 < S ≤ sig x`.
* `stage_grid`: for `n ≥ 1`, finitely many rectangles, each carrying both anchor contracts (earlier
  stages), such that every `x ∈ (R n, TOP - 10^-7)` is admitted with its full selection `sig x`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Marked
noncomputable section
open Qrh.MarkedAnchor.Anchor ChainData ChainCheck
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.MarkedAnchor.High

/-- The top of the improved range minus the pad. -/
def topLo : ℝ := 311/400 - 1/10000000

theorem Rn_ge (n : ℕ) (hn : n < 176) : (1467/2000 : ℝ) ≤ R n := by
  have : (1467/2000 : ℚ) ≤ R n := by
    rw [R_eq]; have : (n : ℚ) ≤ 175 := by exact_mod_cast (by omega : n ≤ 175)
    linarith
  have h' : ((1467/2000 : ℚ) : ℝ) ≤ ((R n : ℚ) : ℝ) := Rat.cast_le.mpr this
  rw [show ((1467/2000 : ℚ) : ℝ) = 1467/2000 by norm_num] at h'
  exact h'

theorem Rn_le (n : ℕ) : (R n : ℝ) ≤ 311/400 - n/4000 := by
  have h : ((R n : ℚ) : ℝ) = ((311/400 - n/4000 : ℚ) : ℝ) := by rw [R_eq]
  rw [h]; push_cast; exact le_rfl

/-- Line facts of every stage: `0 ≤ a1 ≤ 2/5`, `l(TOP) ≤ 0`. -/
theorem stage_line (n : ℕ) (hn : n < 176) :
    (0 : ℝ) ≤ a1 n ∧ (a1 n : ℝ) ≤ 2/5 ∧ (a0 n : ℝ) - a1 n * (311/400) ≤ 0 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [a0_zero, a1_zero]; norm_num
  · obtain ⟨hT, ha1, ha1', -⟩ := chain_line n hpos hn
    simp only [fline] at hT
    exact ⟨ha1.le, ha1'.le, hT.le⟩

/-- `sig` is either zero or the affine expression. -/
theorem le_sig_cases {a0 a1 x S : ℝ} (hS : S ≤ sig a0 a1 x) :
    S ≤ 0 ∨ S ≤ (1-x)/2 + (a0 - a1*x) - 1/10000000 := by
  unfold sig at hS
  rcases le_total 0 ((1-x)/2 + (a0 - a1*x) - 1/10000000) with h | h
  · rw [max_eq_right h] at hS; exact Or.inr hS
  · rw [max_eq_left h] at hS; exact Or.inl hS

/-- Native inverse gates above `TOP - 10^-7`. -/
theorem top_native_gates {a0 a1 : ℝ} (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 2/5)
    (hl : a0 - a1*(311/400) ≤ 0) {x S : ℝ} (hx : topLo ≤ x) (hx1 : x < 1)
    (hS0 : 0 ≤ S) (hS : S ≤ sig a0 a1 x) : x + 2*S < 1 ∧ 2*x + 8*S < 3 := by
  unfold topLo at hx
  have hlx : a0 - a1*x ≤ 2/5*(1/10000000) := by nlinarith
  rcases le_sig_cases hS with h | h
  · have : S = 0 := le_antisymm h hS0
    subst this; constructor <;> linarith
  · constructor <;> linarith

/-- One global ordinary source covers the top range. -/
theorem top_global_face (hres : ReserveParametricSource) :
    ∃ B L c : ℝ, QRH.Record1252270103Source.GlobalSource B L c ∧ 0 ≤ L ∧
      ∀ a0 a1 : ℝ, 0 ≤ a1 → a1 ≤ 2/5 → a0 - a1*(311/400) ≤ 0 →
      ∀ x S : ℝ, topLo ≤ x → x < 1 → 0 < S → S ≤ sig a0 a1 x →
        x + L*S ≤ B ∧ S ≤ c := by
  obtain ⟨B, L, c, hsrc, hL0, hL, hB, hc⟩ := hres (1/100000000) (by norm_num)
  refine ⟨B, L, c, hsrc, hL0, ?_⟩
  intro a0 a1 ha1 ha1' hl x S hx hx1 hS0 hS
  unfold topLo at hx
  have hlx : a0 - a1*x ≤ 2/5*(1/10000000) := by nlinarith
  rcases le_sig_cases hS with h | h
  · linarith
  · have hS1 : S ≤ 3/25 := by linarith
    have hLS : L*S ≤ (2 + 1/100000000)*S := mul_le_mul_of_nonneg_right hL hS0.le
    constructor <;> nlinarith

/-- The anchor of stage `j` has a nonnegative gain at every free width of the stage. -/
theorem fY_nonneg (j : ℕ) (hj : j < 176) (r : ℝ) (h0 : 0 ≤ r) (hr2 : r ≤ R j) :
    0 ≤ fY (R j : ℝ) (gain j) (cut j) r := by
  have hRj := R_pos j hj
  have hk := cut_bounds j hj
  have hg := gain_nonneg j hj
  have hk0 : (0 : ℝ) < cut j := by linarith [hk.2.1]
  simp only [fY, fu]
  have h1' : 0 ≤ r / (R j : ℝ) * gain j :=
    mul_nonneg (div_nonneg h0 hRj.le) hg
  have h2' : 0 ≤ 1 / (cut j : ℝ) - 2 := by
    rw [sub_nonneg, le_div_iff₀ hk0]; linarith [hk.2.2]
  have h3' : 0 ≤ (1 - r / (R j : ℝ)) / 6 := by
    have : r / (R j : ℝ) ≤ 1 := by rw [div_le_one hRj]; exact hr2
    linarith
  have := mul_nonneg h2' h3'
  linarith

/-- Grid step and decrement. -/
def gridH : ℝ := 1/20000000

/-- **Finite slack grid of earlier anchors.** -/
theorem stage_grid (n : ℕ) (h1 : 1 ≤ n) (hn : n < 176) (IH : EarlierAnchors n) :
    ∃ (N : ℕ) (ρ : Fin N → AnchorRect),
      (∀ k, UniformInverseRectSource canonicalFamily (ρ k) ∧ OrdinaryRectSource (ρ k)) ∧
      ∀ x : ℝ, (R n : ℝ) < x → x < topLo →
        ∃ k, (ρ k).Admissible x (sig (a0 n) (a1 n) x) 1 := by
  obtain ⟨-, ha1, ha1', -⟩ := chain_line n h1 hn
  have hRn := Rn_ge n hn
  have hRn' : (R n : ℝ) ≤ 311/400 - 1/4000 := by
    have := Rn_le n
    have : (1:ℝ) ≤ n := by exact_mod_cast h1
    linarith
  set N : ℕ := ⌈((311/400 : ℝ) - R n)/gridH⌉₊ + 1 with hN
  -- the free width of the anchor used by cell `k`
  let rp : Fin N → ℝ := fun k => min ((R n : ℝ) + (k : ℕ)*gridH + 2*gridH) (311/400)
  have hrp_lo (k : Fin N) : (R n : ℝ) < rp k := by
    have hk0 : (0:ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
    have : (0:ℝ) ≤ (k : ℕ)*gridH := mul_nonneg hk0 (by norm_num [gridH])
    refine lt_min ?_ (by linarith)
    have : (0:ℝ) < gridH := by norm_num [gridH]
    linarith
  have hrp_hi (k : Fin N) : rp k ≤ 311/400 := min_le_right _ _
  have hstage (k : Fin N) : ∃ j < n, (left j : ℝ) ≤ rp k ∧ rp k ≤ R j := by
    obtain ⟨j, hj, hr1, hr2⟩ := exists_stage (rp k) (by linarith [hrp_lo k]) (hrp_hi k)
    refine ⟨j, ?_, hr1, hr2⟩
    by_contra hc
    push Not at hc
    rcases eq_or_lt_of_le hc with h | h
    · subst h; linarith [hrp_lo k]
    · have := R_lt_of_lt h; linarith [hrp_lo k]
  choose jj hjj hjl hjr using hstage
  let ρ : Fin N → AnchorRect := fun k =>
    anchorRect (rp k) (fY (R (jj k) : ℝ) (gain (jj k)) (cut (jj k)) (rp k) - 1/25000000) gridH
  refine ⟨N, ρ, fun k => IH (jj k) (hjj k) (rp k) (hjl k) (hjr k) gridH (by norm_num [gridH]), ?_⟩
  intro x hx1 hx2
  have hh : (0:ℝ) < gridH := by norm_num [gridH]
  set q : ℕ := ⌊(x - R n)/gridH⌋₊ with hq
  have hq0 : 0 ≤ (x - R n)/gridH := div_nonneg (by linarith) hh.le
  have hq1 : (q : ℝ) ≤ (x - R n)/gridH := Nat.floor_le hq0
  have hq2 : (x - R n)/gridH < q + 1 := Nat.lt_floor_add_one _
  have hqδ : (x - R n)/gridH*gridH = x - R n := by field_simp
  have e1 := mul_le_mul_of_nonneg_right hq1 hh.le
  have e2 := mul_lt_mul_of_pos_right hq2 hh
  have hqN : q < N := by
    have hle : (x - R n)/gridH ≤ ((311/400 : ℝ) - R n)/gridH :=
      div_le_div_of_nonneg_right (by unfold topLo at hx2; linarith) hh.le
    have hc : ((311/400 : ℝ) - R n)/gridH ≤ (⌈((311/400 : ℝ) - R n)/gridH⌉₊ : ℝ) := Nat.le_ceil _
    have : (q : ℝ) < (N : ℝ) := by
      rw [hN]; push_cast; linarith
    exact_mod_cast this
  let k : Fin N := ⟨q, hqN⟩
  refine ⟨k, ?_⟩
  -- the cell: `R n + q h ≤ x < R n + (q+1) h`
  have hk : ((k : ℕ) : ℝ) = q := rfl
  have hxlo : (R n : ℝ) + q*gridH ≤ x := by linarith
  have hxhi : x < (R n : ℝ) + q*gridH + gridH := by linarith
  have hrpk : rp k = (R n : ℝ) + q*gridH + 2*gridH := by
    show min _ _ = _
    rw [hk]
    apply min_eq_left
    unfold topLo gridH at *
    linarith
  have hmin := chain_minorant_Icc n h1 hn (jj k) (hjj k) (rp k) (hjl k) (hjr k)
  have hY := fY_nonneg (jj k) (by have := hjj k; omega) (rp k) (by linarith [hrp_lo k])
    (hjr k)
  simp only [fline] at hmin
  refine ⟨by linarith, ?_, sig_nonneg _ _ _, ?_⟩
  · show x ≤ (rp k - gridH)*1
    rw [hrpk]; linarith
  · show sig (a0 n) (a1 n) x ≤ ((1 - rp k)/2 + (fY (R (jj k) : ℝ) (gain (jj k)) (cut (jj k)) (rp k)
      - 1/25000000) - gridH)*1
    rw [mul_one]
    unfold sig
    refine max_le ?_ ?_
    · have := hrp_hi k
      unfold gridH; linarith
    · have hd : rp k - x ≤ 2*gridH := by rw [hrpk]; linarith
      have hd0 : 0 ≤ rp k - x := by rw [hrpk]; linarith
      have h3 : (a1 n : ℝ)*(rp k - x) ≤ 2/5*(2*gridH) :=
        mul_le_mul ha1'.le hd (by linarith) (by norm_num)
      unfold gridH at *
      nlinarith

end
end Qrh.MarkedAnchor.High.Marked
