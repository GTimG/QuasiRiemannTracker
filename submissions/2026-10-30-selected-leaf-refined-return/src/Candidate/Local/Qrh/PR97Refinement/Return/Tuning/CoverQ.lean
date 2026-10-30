/- Adapted by Joseph Bebel (2026-10-30) for the fixed five-window return. -/
import Candidate.Local.Qrh.PR97Refinement.Return.Tuning.RowsQ
import Candidate.Local.Qrh.PR97Refinement.Return.CountWindow

/-!
# Windows from rational data, and the kernel-computed edge cover

A window is rational data `WinQ` (branch, `δ ∈ [dlo, dhi]`, `p ∈ [plo, 1/2]`). `WinQ.ok` checks its
bounds and its fifteen guards (`windowCheck`); `mkWindow` turns a passed check into a
`ReturnCountWindow` of `arvi_density` (the window structure of the return).

`coverOK e ws k` certifies the row inequality of the conductor edge `e` on a box: the kernel tries the old
count, then every window of `ws` that contains the box (first fit), and otherwise splits the longer side
(at most `k` times). There is no cover tree, no branch assignment and no certificate data:
`coverOK_sound` holds for any envelope bounded by the old count and by the count of every window.
-/

set_option autoImplicit false

namespace QRH.PR97Refinement.ReturnTuning

open QRH.PR97Refinement.Return QRH.ArviReturnTuning

/-- Rational data of a window: a branch on `[dlo, dhi] × [plo, 1/2]`. -/
structure WinQ where
  branch : CountBranch
  dlo : ℚ
  dhi : ℚ
  plo : ℚ

/-- Bounds and the fifteen guards (subdivision depth `k`). -/
def WinQ.ok (k : ℕ) (w : WinQ) : Bool :=
  decide (w.branch ≠ .old) && decide (0 ≤ w.dlo) && decide (w.dhi ≤ 3 / 4) && decide (0 ≤ w.plo) &&
    decide (w.plo ≤ 1 / 2) && windowCheck (toQ w.branch) k w.dlo w.dhi w.plo

theorem WinQ.ok_spec {k : ℕ} {w : WinQ} (h : w.ok k = true) :
    w.branch ≠ .old ∧ 0 ≤ w.dlo ∧ w.dhi ≤ 3 / 4 ∧ 0 ≤ w.plo ∧ w.plo ≤ 1 / 2 ∧
      windowCheck (toQ w.branch) k w.dlo w.dhi w.plo = true := by
  simp only [WinQ.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

noncomputable section

/-- The window of `arvi_density`'s return defined by checked rational data. -/
def mkWindow (k : ℕ) (w : WinQ) (h : w.ok k = true) : ReturnCountWindow where
  branch := w.branch
  nonold := (WinQ.ok_spec h).1
  deltaLo := (w.dlo : ℝ)
  deltaHi := (w.dhi : ℝ)
  pLo := (w.plo : ℝ)
  deltaBounds := by
    obtain ⟨_, h1, h2, _⟩ := WinQ.ok_spec h
    have h2' : ((w.dhi : ℚ) : ℝ) ≤ ((3 / 4 : ℚ) : ℝ) := by exact_mod_cast h2
    exact ⟨by exact_mod_cast h1, by simpa using h2'⟩
  pBounds := by
    obtain ⟨_, _, _, h3, h4, _⟩ := WinQ.ok_spec h
    have h4' : ((w.plo : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast h4
    exact ⟨by exact_mod_cast h3, by simpa using h4'⟩
  certificate := fun hδ hp j =>
    admission_of_check w.branch (WinQ.ok_spec h).1 k w.dlo w.dhi w.plo (WinQ.ok_spec h).2.2.2.2.2 hδ hp j

theorem ok_of_mem {k : ℕ} {ws : List WinQ} (h : ws.all (WinQ.ok k) = true) {w : WinQ} (hw : w ∈ ws) :
    w.ok k = true :=
  List.all_eq_true.mp h w hw

/-- The windows of a list whose checks all passed. -/
def mkWindows (k : ℕ) (ws : List WinQ) (h : ws.all (WinQ.ok k) = true) : List ReturnCountWindow :=
  ws.attach.map fun w : {x // x ∈ ws} => mkWindow k w.1 (ok_of_mem h w.2)

theorem mkWindow_mem {k : ℕ} {ws : List WinQ} (h : ws.all (WinQ.ok k) = true) {w : WinQ} (hw : w ∈ ws) :
    mkWindow k w (ok_of_mem h hw) ∈ mkWindows k ws h :=
  List.mem_map.mpr ⟨⟨w, hw⟩, List.mem_attach _ _, rfl⟩

end

/-! ### The edge cover -/

/-- A leaf: the old count, or the first window of `ws` that contains the box. -/
def leafOK (e : Edge) (ws : List WinQ) (a b c d : ℚ) : Bool :=
  bernCheck (rowOldQ e) a b c d ||
    ws.any fun w => decide (w.branch ≠ .old) && decide (w.dlo ≤ a) && decide (b ≤ w.dhi) &&
      decide (w.plo ≤ c) && bernCheck (rowBrQ e (toQ w.branch)) a b c d

/-- The kernel-computed cover of the box `[a,b] × [c,d]` (at most `k` bisections deep). -/
def coverOK (e : Edge) (ws : List WinQ) : ℕ → ℚ → ℚ → ℚ → ℚ → Bool
  | 0, a, b, c, d => leafOK e ws a b c d
  | k + 1, a, b, c, d =>
    leafOK e ws a b c d ||
      (if 3 * (d - c) ≤ 2 * (b - a) then
        coverOK e ws k a ((a + b) / 2) c d && coverOK e ws k ((a + b) / 2) b c d
      else coverOK e ws k a b c ((c + d) / 2) && coverOK e ws k a b ((c + d) / 2) d)

section
variable (e : Edge) (ws : List WinQ) (env : ℝ → ℝ → ℝ)
  (hold : ∀ δ p, δ ∈ Set.Icc (0 : ℝ) (3 / 4) → p ∈ Set.Icc (0 : ℝ) (1 / 2) →
    env δ p ≤ countN .old δ p / countJ .old δ p)
  (hwin : ∀ w ∈ ws, w.branch ≠ .old → ∀ δ p, δ ∈ Set.Icc (w.dlo : ℝ) w.dhi →
    p ∈ Set.Icc (w.plo : ℝ) (1 / 2) → env δ p ≤ countN w.branch δ p / countJ w.branch δ p)
include hold hwin

theorem leafOK_sound (a b c d : ℚ) (h : leafOK e ws a b c d = true) {δ p : ℝ} (hd0 : (a : ℝ) ≤ δ)
    (hd1 : δ ≤ b) (hp0 : (c : ℝ) ≤ p) (hp1 : p ≤ d) (hδ : δ ∈ Set.Icc (0 : ℝ) (3 / 4))
    (hp : p ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    Ebase (edgeD e) (edgeC e) δ p + 3 / 4 * edgeD e * env δ p < theta - reserve := by
  simp only [leafOK, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨w, hw, ⟨⟨⟨⟨hb, ha⟩, hbd⟩, hc⟩, hrow⟩⟩
  · have hF : 0 < rowMargin e .old δ p := by
      rw [← ev_rowOldQ]; exact bernCheck_sound _ a b c d h hd0 hd1 hp0 hp1
    exact exponent_lt_of_margin (countJ_pos .old hδ hp) hF (hold δ p hδ hp)
  · have hF : 0 < rowMargin e w.branch δ p := by
      rw [← ev_rowBrQ δ p e w.branch hb]; exact bernCheck_sound _ a b c d hrow hd0 hd1 hp0 hp1
    have ha' : (w.dlo : ℝ) ≤ a := by exact_mod_cast ha
    have hbd' : (b : ℝ) ≤ w.dhi := by exact_mod_cast hbd
    have hc' : (w.plo : ℝ) ≤ c := by exact_mod_cast hc
    exact exponent_lt_of_margin (countJ_pos w.branch hδ hp) hF
      (hwin w hw hb δ p ⟨ha'.trans hd0, hd1.trans hbd'⟩ ⟨hc'.trans hp0, hp.2⟩)

theorem coverOK_sound (k : ℕ) : ∀ (a b c d : ℚ), coverOK e ws k a b c d = true →
    ∀ {δ p : ℝ}, (a : ℝ) ≤ δ → δ ≤ b → (c : ℝ) ≤ p → p ≤ d → δ ∈ Set.Icc (0 : ℝ) (3 / 4) →
      p ∈ Set.Icc (0 : ℝ) (1 / 2) →
      Ebase (edgeD e) (edgeC e) δ p + 3 / 4 * edgeD e * env δ p < theta - reserve := by
  induction k with
  | zero =>
    intro a b c d h δ p hd0 hd1 hp0 hp1 hδ hp
    exact leafOK_sound e ws env hold hwin a b c d h hd0 hd1 hp0 hp1 hδ hp
  | succ k ih =>
    intro a b c d h δ p hd0 hd1 hp0 hp1 hδ hp
    simp only [coverOK, Bool.or_eq_true] at h
    rcases h with h | h
    · exact leafOK_sound e ws env hold hwin a b c d h hd0 hd1 hp0 hp1 hδ hp
    · split_ifs at h with hs
      · simp only [Bool.and_eq_true] at h
        rcases le_total δ (((a + b) / 2 : ℚ) : ℝ) with hm | hm
        · exact ih _ _ _ _ h.1 hd0 hm hp0 hp1 hδ hp
        · exact ih _ _ _ _ h.2 hm hd1 hp0 hp1 hδ hp
      · simp only [Bool.and_eq_true] at h
        rcases le_total p (((c + d) / 2 : ℚ) : ℝ) with hm | hm
        · exact ih _ _ _ _ h.1 hd0 hd1 hp0 hm hδ hp
        · exact ih _ _ _ _ h.2 hd0 hd1 hm hp1 hδ hp

/-- A passed check of the whole root box `[0, 3/4] × [0, 1/2]`. -/
theorem edge_of_coverOK (k : ℕ) (h : coverOK e ws k 0 (3 / 4) 0 (1 / 2) = true) {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (3 / 4)) (hp : p ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    Ebase (edgeD e) (edgeC e) δ p + 3 / 4 * edgeD e * env δ p < theta - reserve :=
  coverOK_sound e ws env hold hwin k 0 (3 / 4) 0 (1 / 2) h (by simpa using hδ.1) (by simpa using hδ.2)
    (by simpa using hp.1) (by simpa using hp.2) hδ hp

end

end QRH.PR97Refinement.ReturnTuning
