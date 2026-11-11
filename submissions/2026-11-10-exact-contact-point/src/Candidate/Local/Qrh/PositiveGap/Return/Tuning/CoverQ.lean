import Candidate.Local.Qrh.PositiveGap.Return.Tuning.RowsQ
import Candidate.Local.Qrh.PositiveGap.Return.CountWindow
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.PositiveGap.ReturnTuning
open QRH.PositiveGap.Return QRH.ArviReturnTuning
structure WinQ where
  branch : CountBranch
  dlo : ℚ
  dhi : ℚ
  plo : ℚ
def WinQ.ok (k : ℕ) (w : WinQ) : Bool :=
  decide (w.branch = .C ∨ w.branch = .capP) && decide (0 ≤ w.dlo) && decide (w.dhi ≤ 3 / 4) &&
    decide (0 ≤ w.plo) && decide (w.plo ≤ 1 / 2) && windowCheckB (toQ w.branch) k w.dlo w.dhi w.plo
theorem WinQ.ok_spec {k : ℕ} {w : WinQ} (h : w.ok k = true) :
    (w.branch = .C ∨ w.branch = .capP) ∧ 0 ≤ w.dlo ∧ w.dhi ≤ 3 / 4 ∧ 0 ≤ w.plo ∧ w.plo ≤ 1 / 2 ∧
      windowCheckB (toQ w.branch) k w.dlo w.dhi w.plo = true := by
  simp only [WinQ.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
theorem WinQ.nonold_of_ok {k : ℕ} {w : WinQ} (h : w.ok k = true) : w.branch ≠ .old := by
  rcases (WinQ.ok_spec h).1 with h1 | h1 <;> rw [h1] <;> decide
noncomputable section
variable [TargetC]
def mkWindow (k : ℕ) (w : WinQ) (h : w.ok k = true) : ReturnCountWindow where
  branch := w.branch
  nonold := WinQ.nonold_of_ok h
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
  certificate := fun hδ hp j => by
    obtain ⟨hb, hd0, hd1, hp0, _, hchk⟩ := WinQ.ok_spec h
    exact admission_of_check w.branch hb k w.dlo w.dhi w.plo hd0 hd1 hp0 hchk hδ hp j
omit [TargetC] in
theorem ok_of_mem {k : ℕ} {ws : List WinQ} (h : ws.all (WinQ.ok k) = true) {w : WinQ} (hw : w ∈ ws) :
    w.ok k = true :=
  List.all_eq_true.mp h w hw
def mkWindows (k : ℕ) (ws : List WinQ) (h : ws.all (WinQ.ok k) = true) : List ReturnCountWindow :=
  ws.attach.map fun w : {x // x ∈ ws} => mkWindow k w.1 (ok_of_mem h w.2)
theorem mkWindow_mem {k : ℕ} {ws : List WinQ} (h : ws.all (WinQ.ok k) = true) {w : WinQ} (hw : w ∈ ws) :
    mkWindow k w (ok_of_mem h hw) ∈ mkWindows k ws h :=
  List.mem_map.mpr ⟨⟨w, hw⟩, List.mem_attach _ _, rfl⟩
end
def leafOK (e : Edge) (ws : List WinQ) (a b c d : ℚ) : Bool :=
  bernCheck (Q2.sub (rowOldQ e) (Q2.C (1 / 100000))) a b c d ||
    ws.any fun w => decide (w.branch = .C ∨ w.branch = .capP) && decide (w.dlo ≤ a) && decide (b ≤ w.dhi) &&
      decide (w.plo ≤ c) && bernCheck (Q2.sub (rowBrQ e (toQ w.branch)) (Q2.C (1 / 100000))) a b c d
def coverOK (e : Edge) (ws : List WinQ) : ℕ → ℚ → ℚ → ℚ → ℚ → Bool
  | 0, a, b, c, d => leafOK e ws a b c d
  | k + 1, a, b, c, d =>
    leafOK e ws a b c d ||
      (if 3 * (d - c) ≤ 2 * (b - a) then
        coverOK e ws k a ((a + b) / 2) c d && coverOK e ws k ((a + b) / 2) b c d
      else coverOK e ws k a b c ((c + d) / 2) && coverOK e ws k a b ((c + d) / 2) d)
section
variable [TargetC] (e : Edge) (ws : List WinQ) (env : ℝ → ℝ → ℝ)
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
  · have hpos := bernCheck_sound _ a b c d h hd0 hd1 hp0 hp1
    rw [Q2.ev_sub, Q2.ev_C] at hpos; push_cast at hpos
    have hle := rowOldQ_le e hδ hp
    have hF : 0 < rowMargin e .old δ p := by linarith
    exact exponent_lt_of_margin (countJ_pos .old hδ hp) hF (hold δ p hδ hp)
  · have hpos := bernCheck_sound _ a b c d hrow hd0 hd1 hp0 hp1
    rw [Q2.ev_sub, Q2.ev_C] at hpos; push_cast at hpos
    have hle := rowBrQ_le e w.branch hb hδ hp
    have hF : 0 < rowMargin e w.branch δ p := by linarith
    have hne : w.branch ≠ .old := by rcases hb with h1 | h1 <;> rw [h1] <;> decide
    have ha' : (w.dlo : ℝ) ≤ a := by exact_mod_cast ha
    have hbd' : (b : ℝ) ≤ w.dhi := by exact_mod_cast hbd
    have hc' : (w.plo : ℝ) ≤ c := by exact_mod_cast hc
    exact exponent_lt_of_margin (countJ_pos w.branch hδ hp) hF
      (hwin w hw hne δ p ⟨ha'.trans hd0, hd1.trans hbd'⟩ ⟨hc'.trans hp0, hp.2⟩)
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
theorem edge_of_coverOK (k : ℕ) (h : coverOK e ws k 0 (3 / 4) 0 (1 / 2) = true) {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0 : ℝ) (3 / 4)) (hp : p ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    Ebase (edgeD e) (edgeC e) δ p + 3 / 4 * edgeD e * env δ p < theta - reserve :=
  coverOK_sound e ws env hold hwin k 0 (3 / 4) 0 (1 / 2) h (by simpa using hδ.1) (by simpa using hδ.2)
    (by simpa using hp.1) (by simpa using hp.2) hδ hp
end
end QRH.PositiveGap.ReturnTuning
