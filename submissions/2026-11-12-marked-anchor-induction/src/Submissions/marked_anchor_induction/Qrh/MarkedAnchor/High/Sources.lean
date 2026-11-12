/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Gates
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Interface.Native

/-!
# High.Sources

Which source pays a short witness of the HIGH child of stage `n`.

At witness width `w' ∈ (R n, 1)` the HIGH child selects whole slots of width
`σ(w') = sig (a0 n) (a1 n) w'`. The point `(w', σ(w'))` is admitted
* for `w' < TOP = 311/400`: by the anchor of an EARLIER stage `j < n` (at a free width `r' ∈ (w', w' + η]`
  of stage `j`, decrement `η`), because the line of stage `n` is a strict minorant (margin `pad`) of
  the proved gain of stage `j` (`ChainCheck.chain_minorant_Icc`) — `earlier_anchor_admits`;
* for `w' ≥ TOP`: by the native inverse (`r + 2S < 1`, `2r + 8S < 3`) and the
  reserve-parametric ordinary face, since `l(w') ≤ l(TOP) ≤ 0` — `native_inverse_admits`,
  `native_ordinary_admits`.
`high_child_sources` combines them. The induction hypothesis `EarlierAnchors n` is exactly what the
stages `j < n` prove (`AnchorAt r (Y_j(r) - δ)` on `[left j, R j]`), so the induction stays acyclic.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open Qrh.MarkedAnchor.Anchor ChainData ChainCheck
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native

/-- The anchors proved by the stages before `n`. -/
def EarlierAnchors (n : ℕ) : Prop :=
  ∀ j < n, ∀ r : ℝ, (left j : ℝ) ≤ r → r ≤ R j →
    AnchorAt r (fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000)

theorem R_lt_of_lt {j n : ℕ} (h : j < n) : (R n : ℝ) < R j := by
  have : R n < R j := by
    rw [R_eq, R_eq]
    have : (j : ℚ) < n := by exact_mod_cast h
    linarith
  exact_mod_cast this

theorem gain_nonneg (j : ℕ) (hj : j < 176) : (0 : ℝ) ≤ gain j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp [gain_zero]
  · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    exact gain_succ_nonneg m (by omega)

/-- **Short witnesses below `TOP` are paid by an earlier anchor.** -/
theorem earlier_anchor_admits (n : ℕ) (h1 : 1 ≤ n) (hn : n < 176) (IH : EarlierAnchors n)
    (w' : ℝ) (hw1 : (R n : ℝ) < w') (hw2 : w' < 311 / 400) :
    ∃ ρ : AnchorRect, (UniformInverseRectSource canonicalFamily ρ ∧ OrdinaryRectSource ρ) ∧
      ρ.Admissible w' (sig (a0 n) (a1 n) w') 1 := by
  obtain ⟨-, ha1, ha1', -⟩ := chain_line n h1 hn
  set η : ℝ := min ((311 / 400 - w') / 2) (1 / 100000000) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hη1 : η ≤ (311 / 400 - w') / 2 := min_le_left _ _
  have hη2 : η ≤ 1 / 100000000 := min_le_right _ _
  set r' := w' + η with hr'
  have hRn : (1467 / 2000 : ℝ) ≤ R n := by
    have : (1467 / 2000 : ℚ) ≤ R n := by
      rw [R_eq]; have : (n : ℚ) ≤ 175 := by exact_mod_cast (by omega : n ≤ 175)
      linarith
    have h' : ((1467 / 2000 : ℚ) : ℝ) ≤ ((R n : ℚ) : ℝ) := Rat.cast_le.mpr this
    rw [show ((1467 / 2000 : ℚ) : ℝ) = 1467 / 2000 by norm_num] at h'
    exact h'
  obtain ⟨j, hj, hr1, hr2⟩ := exists_stage r' (by linarith) (by linarith)
  have hjn : j < n := by
    by_contra hc
    push_neg at hc
    rcases eq_or_lt_of_le hc with h | h
    · subst h; linarith
    · have := R_lt_of_lt h; linarith
  have hmin := chain_minorant_Icc n h1 hn j hjn r' hr1 hr2
  obtain ⟨hinv, hord⟩ := IH j hjn r' hr1 hr2 η hη
  refine ⟨_, ⟨hinv, hord⟩, ?_⟩
  -- the rectangle `anchorRect r' (Y_j(r') - δ) η`
  have hY : 0 ≤ fY (R j : ℝ) (gain j) (cut j) r' := by
    have hRj := R_pos j (by omega)
    have hk := cut_bounds j (by omega)
    have hg := gain_nonneg j (by omega)
    have hk0 : (0 : ℝ) < cut j := by linarith [hk.2.1]
    simp only [fY, fu]
    have h1' : 0 ≤ r' / (R j : ℝ) * gain j :=
      mul_nonneg (div_nonneg (by linarith) hRj.le) hg
    have h2' : 0 ≤ 1 / (cut j : ℝ) - 2 := by
      rw [sub_nonneg, le_div_iff₀ hk0]; linarith [hk.2.2]
    have h3' : 0 ≤ (1 - r' / (R j : ℝ)) / 6 := by
      have : r' / (R j : ℝ) ≤ 1 := by rw [div_le_one hRj]; exact hr2
      linarith
    have := mul_nonneg h2' h3'
    linarith
  refine ⟨by linarith, by simp only [anchorRect, mul_one]; linarith, sig_nonneg _ _ _, ?_⟩
  simp only [anchorRect, mul_one]
  unfold sig
  refine max_le (by linarith) ?_
  simp only [fline] at hmin
  have h3 : (a1 n : ℝ) * η ≤ 2 / 5 * η := mul_le_mul_of_nonneg_right ha1'.le hη.le
  have h4 : (a1 n : ℝ) * r' = a1 n * w' + a1 n * η := by rw [hr']; ring
  linarith

/-- **Native inverse above `TOP`.** -/
theorem native_inverse_admits (hnat : NativeDirectInverse) {a0 a1 : ℝ} (ha1 : 0 ≤ a1)
    (hl : a0 - a1 * (311 / 400) ≤ 0) (w' : ℝ) (hw1 : 311 / 400 ≤ w') (hw2 : w' < 1) :
    ∃ ρ : AnchorRect, UniformInverseRectSource canonicalFamily ρ ∧
      ρ.Admissible w' (sig a0 a1 w') 1 := by
  have hX : (1 - w') / 2 + (a0 - a1 * w') - 1 / 10000000 ≤ (1 - w') / 2 - 1 / 10000000 := by
    nlinarith
  refine ⟨⟨w', sig a0 a1 w'⟩, inverseRectSource_of_native hnat canonicalFamily ?_, ?_⟩
  · simp only [AnchorRect.NativeInverse]
    unfold sig
    rcases le_total 0 ((1 - w') / 2 + (a0 - a1 * w') - 1 / 10000000) with h | h
    · rw [max_eq_right h]; constructor <;> linarith
    · rw [max_eq_left h]; constructor <;> linarith
  · exact ⟨by linarith, by simp, sig_nonneg _ _ _, by simp⟩

/-- **Native ordinary above `TOP`** (reserve-parametric face). -/
theorem native_ordinary_admits (hres : ReserveParametricSource) {a0 a1 : ℝ} (ha1 : 0 ≤ a1)
    (hl : a0 - a1 * (311 / 400) ≤ 0) (w' : ℝ) (hw1 : 311 / 400 ≤ w') (hw2 : w' < 1) :
    ∃ ρ : AnchorRect, OrdinaryRectSource ρ ∧ ρ.Admissible w' (sig a0 a1 w') 1 := by
  have hX : (1 - w') / 2 + (a0 - a1 * w') - 1 / 10000000 ≤ (1 - w') / 2 - 1 / 10000000 := by
    nlinarith
  set η : ℝ := min ((1 - w') / 2) (1 / 100000000) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hη1 : η ≤ (1 - w') / 2 := min_le_left _ _
  have hη2 : η ≤ 1 / 100000000 := min_le_right _ _
  obtain ⟨B, L, c, hsrc, hL0, hL, hB, hc⟩ := hres η hη
  have hσ0 := sig_nonneg a0 a1 w'
  have hσ : sig a0 a1 w' ≤ max 0 ((1 - w') / 2 - 1 / 10000000) := max_le_max le_rfl hX
  refine ⟨⟨w', sig a0 a1 w'⟩, ordinaryRectSource_of_global hsrc hL0 ?_ ?_, ?_⟩
  · show w' + L * sig a0 a1 w' ≤ B
    have hLs : L * sig a0 a1 w' ≤ (2 + η) * sig a0 a1 w' := mul_le_mul_of_nonneg_right hL hσ0
    rcases le_total 0 ((1 - w') / 2 - 1 / 10000000) with h | h
    · rw [max_eq_right h] at hσ
      have : (2 + η) * sig a0 a1 w' ≤ (2 + η) * ((1 - w') / 2 - 1 / 10000000) :=
        mul_le_mul_of_nonneg_left hσ (by linarith)
      have h5 : η * (1 - w') ≤ η := by nlinarith
      nlinarith
    · rw [max_eq_left h] at hσ
      have : sig a0 a1 w' = 0 := le_antisymm hσ hσ0
      rw [this, mul_zero, add_zero]
      linarith
  · show sig a0 a1 w' ≤ c
    rcases le_total 0 ((1 - w') / 2 - 1 / 10000000) with h | h
    · rw [max_eq_right h] at hσ; linarith
    · rw [max_eq_left h] at hσ; linarith
  · exact ⟨by linarith, by simp, hσ0, by simp⟩

/-- **The sources of the short witnesses of the HIGH child of stage `n`.** For every witness width
`w' ∈ (R n, 1)` both the inverse and the ordinary contract admit `(w', σ(w'))`: earlier anchors
below `TOP`, native sources above. -/
theorem high_child_sources (hnat : NativeDirectInverse) (hres : ReserveParametricSource)
    (n : ℕ) (hn : n < 176) (IH : EarlierAnchors n) (w' : ℝ) (hw1 : (R n : ℝ) < w')
    (hw2 : w' < 1) :
    (∃ ρ : AnchorRect, UniformInverseRectSource canonicalFamily ρ ∧
      ρ.Admissible w' (sig (a0 n) (a1 n) w') 1) ∧
    (∃ ρ : AnchorRect, OrdinaryRectSource ρ ∧ ρ.Admissible w' (sig (a0 n) (a1 n) w') 1) := by
  -- the line of stage `n` is nonpositive at `TOP` and has nonnegative slope
  have hline : (0 : ℝ) ≤ a1 n ∧ (a0 n : ℝ) - a1 n * (311 / 400) ≤ 0 := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [a0_zero, a1_zero]
    · obtain ⟨hT, ha1, -, -⟩ := chain_line n hpos hn
      simp only [fline] at hT
      exact ⟨ha1.le, hT.le⟩
  obtain ⟨ha1, hl⟩ := hline
  by_cases hT : w' < 311 / 400
  · have hpos : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        have : ((R 0 : ℚ) : ℝ) = 311 / 400 := by rw [R_eq]; norm_num
        rw [this] at hw1; linarith
      · exact h0
    obtain ⟨ρ, ⟨hi, ho⟩, ha⟩ := earlier_anchor_admits n hpos hn IH w' hw1 hT
    exact ⟨⟨ρ, hi, ha⟩, ⟨ρ, ho, ha⟩⟩
  · push_neg at hT
    exact ⟨native_inverse_admits hnat ha1 hl w' hT hw2, native_ordinary_admits hres ha1 hl w' hT hw2⟩

end
end Qrh.MarkedAnchor.High
