/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Anchor.ChainData

/-!
# Anchor.ChainCheck

Kernel check of all gates of the 176-stage chain of `Anchor.ChainData`.

* `checkAll : Bool` checks everything required of the chain: the 14 gates
  (`4928 = 176 · 2 · 14` values) and the identities for `s0` and `g(k)` at both endpoints of every
  stage, `wb ≥ R`, `9/25 < k < 1/2`, `k ≥ 45457/125000`, `next_gain ≥ 0`, the checks of the line
  used by each stage `1..175` against all earlier stages, the own lines of the outer stages
  93, 96, 107, 120 against all 176 stages, and `left 175 = 1467/2000`.
* `chain_ok : checkAll = true`, assembled from 42 chunked `decide +kernel` theorems
  (`stages_ok_*`, `chainLines_ok_*`, `outer_ok_*`, `left_end_ok`).
* `chainOK : ChainOK` (the propositional form) and the real-valued lemmas `gate1_real` …
  `gate14_real`, `s0_identity`, `g_identity`, `wb_ge_R`, `cut_bounds`, `gain_succ_nonneg`,
  `chain_line`, `chain_minorant(_Icc)`, `outer_line`, `outer_minorant`, `outer_minorant_chain`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Anchor.ChainCheck
open ChainData

/-- The 14 gates at the point `r` of stage `s` (gate 13 split into its two `max` branches) and
the two identities `s0 = H((1-R)/2 + z) + u/k`, `g(k) = H wb`. -/
abbrev EndpointGates (s : Stage) (r : ℚ) : Prop :=
  0 < gate1 s.R s.gain s.cut s.a0 s.a1 r ∧ 0 < gate2 s.R s.gain s.cut r ∧
  0 < gate3 s.R s.gain s.cut r ∧ 0 < gate4 s.R s.gain s.cut r ∧ 0 < gate5 s.R s.gain s.cut r ∧
  0 < gate6 s.R s.gain s.cut r ∧ 0 < gate7 s.R s.gain s.cut r ∧ 0 < gate8 s.R s.gain s.cut r ∧
  0 < gate9 s.R s.gain s.cut s.a1 r ∧ 0 < gate10 s.R s.gain s.cut r ∧
  0 < gate11 s.R s.gain s.cut s.a0 s.a1 r ∧ 0 < gate12 s.R s.gain s.cut s.a0 s.a1 r ∧
  0 < 1 - 3 / 4 * fw s.R s.gain s.cut s.a0 s.a1 r (3 / 4) - 1 / 6 ∧
  0 < 1 - 3 / 4 * fw s.R s.gain s.cut s.a0 s.a1 r (3 / 4)
      - 3 / 4 * fsig s.R s.gain s.cut s.a0 s.a1 r - 1 / 6 ∧
  0 < gate14 s.R r ∧
  fs s.R s.gain s.cut r = fH s.R r * ((1 - s.R) / 2 + s.gain) + fu s.R r / s.cut ∧
  fg s.R s.gain s.cut s.a0 s.a1 r s.cut = fH s.R r * s.wb

/-- Per-stage checks: gates at both endpoints, `wb ≥ R`, `9/25 < k < 1/2`, the lower bound
`45457/125000 ≤ k`, `next_gain ≥ 0`. -/
abbrev StageGates (s : Stage) : Prop :=
  EndpointGates s s.left ∧ EndpointGates s s.R ∧ s.R ≤ s.wb ∧ 9 / 25 < s.cut ∧ s.cut < 1 / 2 ∧
  45457 / 125000 ≤ s.cut ∧ 0 ≤ s.nextGain

/-- Strict minorant (margin `PAD`) of `Y - DELTA` at both endpoints of stage `t`. -/
abbrev MinorantAt (a0 a1 : ℚ) (t : Stage) : Prop :=
  0 < t.Y t.left - DELTA - fline a0 a1 t.left - PAD ∧ 0 < t.Y t.R - DELTA - fline a0 a1 t.R - PAD

/-- `l(TOP) < 0`, `0 < a1 < 2/5`. -/
abbrev LineGates (a0 a1 : ℚ) : Prop := fline a0 a1 TOP < 0 ∧ 0 < a1 ∧ a1 < 2 / 5

/-- Checks of the line used by stage `n ≥ 1`: `LineGates`, below the entry gain at `R n`, and a
strict minorant on every earlier stage. -/
abbrev ChainLine (n : ℕ) : Prop :=
  LineGates (a0 n) (a1 n) ∧ 0 < gain n - fline (a0 n) (a1 n) (R n) ∧
    ∀ j < n, MinorantAt (a0 n) (a1 n) (stage j)

/-- The own line of stage `i` as an outer line: `LineGates` and a strict minorant on all 176
stages. -/
abbrev OuterLine (i : ℕ) : Prop :=
  LineGates (own0 i) (own1 i) ∧ ∀ j < 176, MinorantAt (own0 i) (own1 i) (stage j)

/-- Everything required of the chain. -/
abbrev ChainOK : Prop :=
  (∀ n < 176, StageGates (stage n)) ∧ (∀ n < 175, ChainLine (n + 1)) ∧
  OuterLine 93 ∧ OuterLine 96 ∧ OuterLine 107 ∧ OuterLine 120 ∧ left 175 = LEFT

/-! ### The Boolean checker (one `decide` per atomic inequality) -/

/-- `EndpointGates` at the point `r`. -/
def endpointOK (s : Stage) (r : ℚ) : Bool :=
  decide (0 < gate1 s.R s.gain s.cut s.a0 s.a1 r) && (decide (0 < gate2 s.R s.gain s.cut r) &&
  (decide (0 < gate3 s.R s.gain s.cut r) && (decide (0 < gate4 s.R s.gain s.cut r) &&
  (decide (0 < gate5 s.R s.gain s.cut r) && (decide (0 < gate6 s.R s.gain s.cut r) &&
  (decide (0 < gate7 s.R s.gain s.cut r) && (decide (0 < gate8 s.R s.gain s.cut r) &&
  (decide (0 < gate9 s.R s.gain s.cut s.a1 r) && (decide (0 < gate10 s.R s.gain s.cut r) &&
  (decide (0 < gate11 s.R s.gain s.cut s.a0 s.a1 r) &&
  (decide (0 < gate12 s.R s.gain s.cut s.a0 s.a1 r) &&
  (decide (0 < 1 - 3 / 4 * fw s.R s.gain s.cut s.a0 s.a1 r (3 / 4) - 1 / 6) &&
  (decide (0 < 1 - 3 / 4 * fw s.R s.gain s.cut s.a0 s.a1 r (3 / 4)
      - 3 / 4 * fsig s.R s.gain s.cut s.a0 s.a1 r - 1 / 6) &&
  (decide (0 < gate14 s.R r) &&
  (decide (fs s.R s.gain s.cut r = fH s.R r * ((1 - s.R) / 2 + s.gain) + fu s.R r / s.cut) &&
  decide (fg s.R s.gain s.cut s.a0 s.a1 r s.cut = fH s.R r * s.wb))))))))))))))))

/-- `StageGates`. -/
def stageOK (s : Stage) : Bool :=
  endpointOK s s.left && (endpointOK s s.R && (decide (s.R ≤ s.wb) && (decide (9 / 25 < s.cut) &&
  (decide (s.cut < 1 / 2) && (decide (45457 / 125000 ≤ s.cut) && decide (0 ≤ s.nextGain))))))

/-- `MinorantAt`. -/
def minorOK (a0 a1 : ℚ) (t : Stage) : Bool :=
  decide (0 < t.Y t.left - DELTA - fline a0 a1 t.left - PAD) &&
    decide (0 < t.Y t.R - DELTA - fline a0 a1 t.R - PAD)

/-- `LineGates`. -/
def lineOK (a0 a1 : ℚ) : Bool :=
  decide (fline a0 a1 TOP < 0) && (decide (0 < a1) && decide (a1 < 2 / 5))

/-- `ChainLine n` for stage `n ≥ 1`. -/
def chainLineOK (n : ℕ) : Bool :=
  lineOK (a0 n) (a1 n) && (decide (0 < gain n - fline (a0 n) (a1 n) (R n)) &&
    (List.range n).all fun j => minorOK (a0 n) (a1 n) (stage j))

/-- `OuterLine i`. -/
def outerOK (i : ℕ) : Bool :=
  lineOK (own0 i) (own1 i) && (List.range 176).all fun j => minorOK (own0 i) (own1 i) (stage j)

/-- The Boolean checker of `ChainOK`. -/
def checkAll : Bool :=
  (List.range 176).all (fun n => stageOK (stage n)) &&
  ((List.range 175).all (fun n => chainLineOK (n + 1)) &&
  (outerOK 93 && (outerOK 96 && (outerOK 107 && (outerOK 120 && decide (left 175 = LEFT))))))

/-- `p lo && p (lo + 1) && … && p (lo + k - 1)`. -/
def allFrom (p : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, k + 1 => p lo && allFrom p (lo + 1) k

theorem allFrom_sound {p : ℕ → Bool} :
    ∀ {lo k : ℕ}, allFrom p lo k = true → ∀ m, lo ≤ m → m < lo + k → p m = true
  | _, 0, _, _, h1, h2 => absurd h2 (by omega)
  | lo, k + 1, h, m, h1, h2 => by
    simp only [allFrom, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact h.1
    · exact allFrom_sound h.2 m h1' (by omega)

/-! Kernel checks, split into chunks (each declaration is checked with a fresh kernel cache). -/

theorem stages_ok_0 : allFrom (fun n => stageOK (stage n)) 0 22 = true := by
  decide +kernel

theorem stages_ok_22 : allFrom (fun n => stageOK (stage n)) 22 22 = true := by
  decide +kernel

theorem stages_ok_44 : allFrom (fun n => stageOK (stage n)) 44 22 = true := by
  decide +kernel

theorem stages_ok_66 : allFrom (fun n => stageOK (stage n)) 66 22 = true := by
  decide +kernel

theorem stages_ok_88 : allFrom (fun n => stageOK (stage n)) 88 22 = true := by
  decide +kernel

theorem stages_ok_110 : allFrom (fun n => stageOK (stage n)) 110 22 = true := by
  decide +kernel

theorem stages_ok_132 : allFrom (fun n => stageOK (stage n)) 132 22 = true := by
  decide +kernel

theorem stages_ok_154 : allFrom (fun n => stageOK (stage n)) 154 22 = true := by
  decide +kernel

theorem chainLines_ok_1 : allFrom chainLineOK 1 34 = true := by
  decide +kernel

theorem chainLines_ok_35 : allFrom chainLineOK 35 14 = true := by
  decide +kernel

theorem chainLines_ok_49 : allFrom chainLineOK 49 11 = true := by
  decide +kernel

theorem chainLines_ok_60 : allFrom chainLineOK 60 9 = true := by
  decide +kernel

theorem chainLines_ok_69 : allFrom chainLineOK 69 8 = true := by
  decide +kernel

theorem chainLines_ok_77 : allFrom chainLineOK 77 7 = true := by
  decide +kernel

theorem chainLines_ok_84 : allFrom chainLineOK 84 6 = true := by
  decide +kernel

theorem chainLines_ok_90 : allFrom chainLineOK 90 6 = true := by
  decide +kernel

theorem chainLines_ok_96 : allFrom chainLineOK 96 6 = true := by
  decide +kernel

theorem chainLines_ok_102 : allFrom chainLineOK 102 5 = true := by
  decide +kernel

theorem chainLines_ok_107 : allFrom chainLineOK 107 5 = true := by
  decide +kernel

theorem chainLines_ok_112 : allFrom chainLineOK 112 5 = true := by
  decide +kernel

theorem chainLines_ok_117 : allFrom chainLineOK 117 5 = true := by
  decide +kernel

theorem chainLines_ok_122 : allFrom chainLineOK 122 4 = true := by
  decide +kernel

theorem chainLines_ok_126 : allFrom chainLineOK 126 4 = true := by
  decide +kernel

theorem chainLines_ok_130 : allFrom chainLineOK 130 4 = true := by
  decide +kernel

theorem chainLines_ok_134 : allFrom chainLineOK 134 4 = true := by
  decide +kernel

theorem chainLines_ok_138 : allFrom chainLineOK 138 4 = true := by
  decide +kernel

theorem chainLines_ok_142 : allFrom chainLineOK 142 4 = true := by
  decide +kernel

theorem chainLines_ok_146 : allFrom chainLineOK 146 4 = true := by
  decide +kernel

theorem chainLines_ok_150 : allFrom chainLineOK 150 3 = true := by
  decide +kernel

theorem chainLines_ok_153 : allFrom chainLineOK 153 3 = true := by
  decide +kernel

theorem chainLines_ok_156 : allFrom chainLineOK 156 3 = true := by
  decide +kernel

theorem chainLines_ok_159 : allFrom chainLineOK 159 3 = true := by
  decide +kernel

theorem chainLines_ok_162 : allFrom chainLineOK 162 3 = true := by
  decide +kernel

theorem chainLines_ok_165 : allFrom chainLineOK 165 3 = true := by
  decide +kernel

theorem chainLines_ok_168 : allFrom chainLineOK 168 3 = true := by
  decide +kernel

theorem chainLines_ok_171 : allFrom chainLineOK 171 3 = true := by
  decide +kernel

theorem chainLines_ok_174 : allFrom chainLineOK 174 2 = true := by
  decide +kernel

theorem outer_ok_93 : outerOK 93 = true := by
  decide +kernel

theorem outer_ok_96 : outerOK 96 = true := by
  decide +kernel

theorem outer_ok_107 : outerOK 107 = true := by
  decide +kernel

theorem outer_ok_120 : outerOK 120 = true := by
  decide +kernel

theorem left_end_ok : left 175 = LEFT := by
  decide +kernel

theorem stages_all (n : ℕ) (hn : n < 176) : stageOK (stage n) = true := by
  by_cases c0 : n < 22
  · exact allFrom_sound stages_ok_0 n (by omega) (by omega)
  by_cases c22 : n < 44
  · exact allFrom_sound stages_ok_22 n (by omega) (by omega)
  by_cases c44 : n < 66
  · exact allFrom_sound stages_ok_44 n (by omega) (by omega)
  by_cases c66 : n < 88
  · exact allFrom_sound stages_ok_66 n (by omega) (by omega)
  by_cases c88 : n < 110
  · exact allFrom_sound stages_ok_88 n (by omega) (by omega)
  by_cases c110 : n < 132
  · exact allFrom_sound stages_ok_110 n (by omega) (by omega)
  by_cases c132 : n < 154
  · exact allFrom_sound stages_ok_132 n (by omega) (by omega)
  exact allFrom_sound stages_ok_154 n (by omega) (by omega)

theorem chainLines_all (n : ℕ) (h1 : 1 ≤ n) (hn : n < 176) : chainLineOK n = true := by
  by_cases c1 : n < 35
  · exact allFrom_sound chainLines_ok_1 n (by omega) (by omega)
  by_cases c35 : n < 49
  · exact allFrom_sound chainLines_ok_35 n (by omega) (by omega)
  by_cases c49 : n < 60
  · exact allFrom_sound chainLines_ok_49 n (by omega) (by omega)
  by_cases c60 : n < 69
  · exact allFrom_sound chainLines_ok_60 n (by omega) (by omega)
  by_cases c69 : n < 77
  · exact allFrom_sound chainLines_ok_69 n (by omega) (by omega)
  by_cases c77 : n < 84
  · exact allFrom_sound chainLines_ok_77 n (by omega) (by omega)
  by_cases c84 : n < 90
  · exact allFrom_sound chainLines_ok_84 n (by omega) (by omega)
  by_cases c90 : n < 96
  · exact allFrom_sound chainLines_ok_90 n (by omega) (by omega)
  by_cases c96 : n < 102
  · exact allFrom_sound chainLines_ok_96 n (by omega) (by omega)
  by_cases c102 : n < 107
  · exact allFrom_sound chainLines_ok_102 n (by omega) (by omega)
  by_cases c107 : n < 112
  · exact allFrom_sound chainLines_ok_107 n (by omega) (by omega)
  by_cases c112 : n < 117
  · exact allFrom_sound chainLines_ok_112 n (by omega) (by omega)
  by_cases c117 : n < 122
  · exact allFrom_sound chainLines_ok_117 n (by omega) (by omega)
  by_cases c122 : n < 126
  · exact allFrom_sound chainLines_ok_122 n (by omega) (by omega)
  by_cases c126 : n < 130
  · exact allFrom_sound chainLines_ok_126 n (by omega) (by omega)
  by_cases c130 : n < 134
  · exact allFrom_sound chainLines_ok_130 n (by omega) (by omega)
  by_cases c134 : n < 138
  · exact allFrom_sound chainLines_ok_134 n (by omega) (by omega)
  by_cases c138 : n < 142
  · exact allFrom_sound chainLines_ok_138 n (by omega) (by omega)
  by_cases c142 : n < 146
  · exact allFrom_sound chainLines_ok_142 n (by omega) (by omega)
  by_cases c146 : n < 150
  · exact allFrom_sound chainLines_ok_146 n (by omega) (by omega)
  by_cases c150 : n < 153
  · exact allFrom_sound chainLines_ok_150 n (by omega) (by omega)
  by_cases c153 : n < 156
  · exact allFrom_sound chainLines_ok_153 n (by omega) (by omega)
  by_cases c156 : n < 159
  · exact allFrom_sound chainLines_ok_156 n (by omega) (by omega)
  by_cases c159 : n < 162
  · exact allFrom_sound chainLines_ok_159 n (by omega) (by omega)
  by_cases c162 : n < 165
  · exact allFrom_sound chainLines_ok_162 n (by omega) (by omega)
  by_cases c165 : n < 168
  · exact allFrom_sound chainLines_ok_165 n (by omega) (by omega)
  by_cases c168 : n < 171
  · exact allFrom_sound chainLines_ok_168 n (by omega) (by omega)
  by_cases c171 : n < 174
  · exact allFrom_sound chainLines_ok_171 n (by omega) (by omega)
  exact allFrom_sound chainLines_ok_174 n (by omega) (by omega)

/-- The Boolean checker evaluates to `true`.  (Proved from the chunked kernel checks above; a single
`decide +kernel` on `checkAll` exceeds the 8 GiB memory budget.) -/
theorem chain_ok : checkAll = true := by
  simp only [checkAll, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  exact ⟨fun n hn => stages_all n hn, fun n hn => chainLines_all (n + 1) (by omega) (by omega),
    outer_ok_93, outer_ok_96, outer_ok_107, outer_ok_120, left_end_ok⟩

theorem endpointOK_sound {s : Stage} {r : ℚ} (h : endpointOK s r = true) : EndpointGates s r := by
  simp only [endpointOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem stageOK_sound {s : Stage} (h : stageOK s = true) : StageGates s := by
  simp only [stageOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨endpointOK_sound h1, endpointOK_sound h2, h3⟩

theorem minorOK_sound {a0 a1 : ℚ} {t : Stage} (h : minorOK a0 a1 t = true) :
    MinorantAt a0 a1 t := by
  simp only [minorOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem lineOK_sound {a0 a1 : ℚ} (h : lineOK a0 a1 = true) : LineGates a0 a1 := by
  simp only [lineOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem chainLineOK_sound {n : ℕ} (h : chainLineOK n = true) : ChainLine n := by
  simp only [chainLineOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨lineOK_sound h1, h2, fun j hj => minorOK_sound (h3 j hj)⟩

theorem outerOK_sound {i : ℕ} (h : outerOK i = true) : OuterLine i := by
  simp only [outerOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨lineOK_sound h1, fun j hj => minorOK_sound (h2 j hj)⟩

/-- All checks of the chain, as a proposition. -/
theorem chainOK : ChainOK := by
  have h := chain_ok
  simp only [checkAll, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨fun n hn => stageOK_sound (h1 n hn), fun n hn => chainLineOK_sound (h2 n hn),
    outerOK_sound h3, outerOK_sound h4, outerOK_sound h5, outerOK_sound h6, h7⟩

/-- Spot values of the last stage. -/
theorem stage175_values :
    R 175 = 587 / 800 ∧ gain 175 = 15174277 / 5000000000 ∧
    a0 175 = 11287478127 / 91137500000 ∧ a1 175 = 4405863521813 / 26757970000000 ∧
    cut 175 = 45457 / 125000 ∧ (stage 175).nextGain = 30763623 / 10000000000 ∧
    own0 175 = 71012363629 / 568212500000 ∧ own1 175 = 27715222890411 / 166770368750000 := by
  decide +kernel

/-- The own lines of the outer stages. -/
theorem outer_line_values :
    own0 93 = 849533611667 / 16201387500000 ∧ own1 93 = 670173583216777 / 9775917217500000 ∧
    own0 96 = 146461855453 / 2685612500000 ∧ own1 96 = 115490765783031 / 1618887215000000 ∧
    own0 107 = 987208710793 / 15788362500000 ∧ own1 107 = 388629866762299 / 4741245258750000 ∧
    own0 120 = 372636268299 / 5132087500000 ∧ own1 120 = 58574022395129 / 613797665000000 := by
  decide +kernel

/-! ## Soundness: real-valued statements

All statements below are about the casts to `ℝ` of the exact rational stage data, with the gate
formulas of `ChainData` instantiated at `ℝ`.  Endpoint form: `r` ranges over `{left n, R n}`. -/

section Real

private theorem cast_pos_of {q : ℚ} {x : ℝ} (h : 0 < q) (e : ((q : ℚ) : ℝ) = x) : 0 < x := by
  rw [← e]; exact_mod_cast h

private theorem cast_lt_of {q q' : ℚ} {x x' : ℝ} (h : q < q') (e : ((q : ℚ) : ℝ) = x)
    (e' : ((q' : ℚ) : ℝ) = x') : x < x' := by
  rw [← e, ← e']; exact_mod_cast h

private theorem cast_le_of {q q' : ℚ} {x x' : ℝ} (h : q ≤ q') (e : ((q : ℚ) : ℝ) = x)
    (e' : ((q' : ℚ) : ℝ) = x') : x ≤ x' := by
  rw [← e, ← e']; exact_mod_cast h

private theorem cast_eq_of {q q' : ℚ} {x x' : ℝ} (h : q = q') (e : ((q : ℚ) : ℝ) = x)
    (e' : ((q' : ℚ) : ℝ) = x') : x = x' := by
  rw [← e, ← e', h]

/-- Unfold the gate formulas and push the casts to the leaves. -/
local macro "chain_cast" : tactic =>
  `(tactic| (simp only [gate1, gate2, gate3, gate4, gate5, gate6, gate7, gate8, gate9, gate10,
      gate11, gate12, gate14, fH, fu, fY, fS, fs, fwb, fF0, fg, fw, fsig, fline, Stage.Y, Stage.wb,
      DELTA, PAD, TOP]; push_cast; try ring))

/-- The gates and identities hold at both endpoints of every stage (exact rational form). -/
theorem endpoint (n : ℕ) (hn : n < 176) (r : ℚ) (hr : r = left n ∨ r = R n) :
    EndpointGates (stage n) r := by
  obtain ⟨hl, hR, -⟩ := chainOK.1 n hn
  rcases hr with rfl | rfl
  · exact hl
  · exact hR

section Gates
variable (n : ℕ) (hn : n < 176) (r : ℚ) (hr : r = left n ∨ r = R n)
include hn hr

/-- Gate 1: `H F0 > 3·10^-5`. -/
theorem gate1_real :
    0 < fH (R n : ℝ) r * fF0 (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) - 3 / 100000 := by
  obtain ⟨g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Gate 2: `S < 137/1000`. -/
theorem gate2_real : 0 < 137 / 1000 - fS (R n : ℝ) (gain n) (cut n) r := by
  obtain ⟨-, g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Gate 3: `S/H < 14/100`. -/
theorem gate3_real : 0 < 14 / 100 - fS (R n : ℝ) (gain n) (cut n) r / fH (R n : ℝ) r := by
  obtain ⟨-, -, g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Gate 4: `r + S + 4u < 9/10`. -/
theorem gate4_real :
    0 < 9 / 10 - (r : ℝ) - fS (R n : ℝ) (gain n) (cut n) r - 4 * fu (R n : ℝ) r := by
  obtain ⟨-, -, -, g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Gate 5: `r + S + 4u < 91/100`. -/
theorem gate5_real :
    0 < 91 / 100 - (r : ℝ) - fS (R n : ℝ) (gain n) (cut n) r - 4 * fu (R n : ℝ) r := by
  obtain ⟨-, -, -, -, g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Gate 6: `r + S + 3u + 1/100 < 5/6 + 21/250`. -/
theorem gate6_real :
    0 < 5 / 6 + 21 / 250 - (r : ℝ) - fS (R n : ℝ) (gain n) (cut n) r - 3 * fu (R n : ℝ) r
      - 1 / 100 := by
  obtain ⟨-, -, -, -, -, g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Gate 7: `2r + 8 s0 + 1/5 < 3H`. -/
theorem gate7_real :
    0 < 3 * fH (R n : ℝ) r - 2 * (r : ℝ) - 8 * fs (R n : ℝ) (gain n) (cut n) r - 1 / 5 := by
  obtain ⟨-, -, -, -, -, -, g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Gate 8: `1/2 + Y - u + 1/5 < r`. -/
theorem gate8_real :
    0 < (r : ℝ) - 1 / 2 - fY (R n : ℝ) (gain n) (cut n) r + fu (R n : ℝ) r - 1 / 5 := by
  obtain ⟨-, -, -, -, -, -, -, g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Gate 9: the derivative bound `dG/dν > 1/10`. -/
theorem gate9_real :
    0 < (r : ℝ) / 2 - fs (R n : ℝ) (gain n) (cut n) r
      - 3 / 2 * (5 / 6 - (cut n : ℝ)) * (fu (R n : ℝ) r / ((cut n : ℝ) * cut n))
        / (1 / 2 - (a1 n : ℝ)) - 1 / 10 := by
  obtain ⟨-, -, -, -, -, -, -, -, g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Gate 10: `H + u - H/6 - 1/15 - (3/4) r - s0 > 3/100`. -/
theorem gate10_real :
    0 < fH (R n : ℝ) r + fu (R n : ℝ) r - fH (R n : ℝ) r / 6 - 1 / 15 - 3 / 4 * (r : ℝ)
      - fs (R n : ℝ) (gain n) (cut n) r - 3 / 100 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Gate 11: `w_lo = w(k) > 2/3`. -/
theorem gate11_real :
    0 < fw (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r (cut n) - 2 / 3 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Gate 12: `w_hi = w(3/4) < 79/100`. -/
theorem gate12_real :
    0 < 79 / 100 - fw (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r (3 / 4) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Gate 13: `1 - (3/4) w_hi - (3/4) max 0 σ > 1/6`. -/
theorem gate13_real :
    0 < 1 - 3 / 4 * fw (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r (3 / 4)
      - 3 / 4 * max 0 (fsig (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r) - 1 / 6 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ga, gb, -⟩ := endpoint n hn r hr
  have hA := cast_pos_of ga
    (x := 1 - 3 / 4 * fw (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r (3 / 4) - 1 / 6)
    (by chain_cast)
  have hB := cast_pos_of gb
    (x := 1 - 3 / 4 * fw (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r (3 / 4)
      - 3 / 4 * fsig (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r - 1 / 6)
    (by chain_cast)
  rcases le_total (fsig (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r) 0 with hs | hs
  · rw [max_eq_left hs]; linarith
  · rw [max_eq_right hs]; linarith

/-- Gate 14: `r + (2 + 10^-11) u < 79/100`. -/
theorem gate14_real : 0 < 79 / 100 - (r : ℝ) - (2 + 1 / 100000000000) * fu (R n : ℝ) r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, g, -⟩ := endpoint n hn r hr
  exact cast_pos_of g (by chain_cast)

/-- Identity: `s0 = H((1-R)/2 + z) + u/k`. -/
theorem s0_identity :
    fs (R n : ℝ) (gain n) (cut n) r
      = fH (R n : ℝ) r * ((1 - (R n : ℝ)) / 2 + gain n) + fu (R n : ℝ) r / cut n := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e, -⟩ := endpoint n hn r hr
  exact cast_eq_of e (by chain_cast) (by chain_cast)

/-- Identity: `g(k) = H w_b`. -/
theorem g_identity :
    fg (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r (cut n)
      = fH (R n : ℝ) r * fwb (R n : ℝ) (gain n) (a0 n) (a1 n) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e⟩ := endpoint n hn r hr
  exact cast_eq_of e (by chain_cast) (by chain_cast)

end Gates

section StageFacts
variable (n : ℕ) (hn : n < 176)
include hn

/-- `w_b ≥ R`. -/
theorem wb_ge_R : (R n : ℝ) ≤ fwb (R n : ℝ) (gain n) (a0 n) (a1 n) := by
  obtain ⟨-, -, h, -⟩ := chainOK.1 n hn
  exact cast_le_of h rfl (by chain_cast)

/-- Bounds on the threshold: `45457/125000 ≤ k`, `9/25 < k < 1/2`. -/
theorem cut_bounds :
    (45457 / 125000 : ℝ) ≤ cut n ∧ (9 / 25 : ℝ) < cut n ∧ (cut n : ℝ) < 1 / 2 := by
  obtain ⟨-, -, -, h1, h2, h3, -⟩ := chainOK.1 n hn
  exact ⟨cast_le_of h3 (by norm_num) rfl, cast_lt_of h1 (by norm_num) rfl,
    cast_lt_of h2 rfl (by norm_num)⟩

/-- The next gain is nonnegative. -/
theorem gain_succ_nonneg : (0 : ℝ) ≤ gain (n + 1) := by
  obtain ⟨-, -, -, -, -, -, h⟩ := chainOK.1 n hn
  exact cast_le_of h (by norm_num) rfl

end StageFacts

/-- The line used by stage `n ≥ 1` (the own line of stage `n - 1`) is negative at
`TOP`, has slope in `(0, 2/5)`, and lies below the entry gain at `R n`. -/
theorem chain_line (n : ℕ) (h1 : 1 ≤ n) (hn : n < 176) :
    fline (a0 n : ℝ) (a1 n) (311 / 400) < 0 ∧ 0 < (a1 n : ℝ) ∧ (a1 n : ℝ) < 2 / 5 ∧
      0 < (gain n : ℝ) - fline (a0 n : ℝ) (a1 n) (R n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨⟨hT, h0, h25⟩, hg, -⟩ := chainOK.2.1 m (by omega)
  exact ⟨cast_lt_of hT (by chain_cast) (by norm_num), cast_lt_of h0 (by norm_num) rfl,
    cast_lt_of h25 rfl (by norm_num), cast_pos_of hg (by chain_cast)⟩

/-- The line used by stage `n ≥ 1` is a strict minorant (margin `pad`) of the proved
gain `Y_j - δ` at both endpoints of every earlier stage `j < n`. -/
theorem chain_minorant (n : ℕ) (h1 : 1 ≤ n) (hn : n < 176) (j : ℕ) (hj : j < n) (r : ℚ)
    (hr : r = left j ∨ r = R j) :
    0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000 - fline (a0 n : ℝ) (a1 n) r
      - 1 / 10000000 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hl, hR⟩ := (chainOK.2.1 m (by omega)).2.2 j hj
  rcases hr with rfl | rfl
  · exact cast_pos_of hl (by chain_cast)
  · exact cast_pos_of hR (by chain_cast)

/-- The outer stages 93, 96, 107, 120. -/
def OuterIndex (i : ℕ) : Prop := i = 93 ∨ i = 96 ∨ i = 107 ∨ i = 120

private theorem outerLine_of (i : ℕ) (hi : OuterIndex i) : OuterLine i := by
  obtain ⟨-, -, h93, h96, h107, h120, -⟩ := chainOK
  rcases hi with rfl | rfl | rfl | rfl <;> assumption

/-- The own line of an outer stage is negative at `TOP`, slope in `(0, 2/5)`. -/
theorem outer_line (i : ℕ) (hi : OuterIndex i) :
    fline (own0 i : ℝ) (own1 i) (311 / 400) < 0 ∧ 0 < (own1 i : ℝ) ∧ (own1 i : ℝ) < 2 / 5 := by
  obtain ⟨⟨hT, h0, h25⟩, -⟩ := outerLine_of i hi
  exact ⟨cast_lt_of hT (by chain_cast) (by norm_num), cast_lt_of h0 (by norm_num) rfl,
    cast_lt_of h25 rfl (by norm_num)⟩

/-- The own line of an outer stage is a strict minorant (margin `pad`) of the
proved gain `Y_j - δ` at both endpoints of every stage `j < 176`. -/
theorem outer_minorant (i : ℕ) (hi : OuterIndex i) (j : ℕ) (hj : j < 176) (r : ℚ)
    (hr : r = left j ∨ r = R j) :
    0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000 - fline (own0 i : ℝ) (own1 i) r
      - 1 / 10000000 := by
  obtain ⟨hl, hR⟩ := (outerLine_of i hi).2 j hj
  rcases hr with rfl | rfl
  · exact cast_pos_of hl (by chain_cast)
  · exact cast_pos_of hR (by chain_cast)

/-! ### Interval forms (each `Y_j` and each line is affine in `r`) -/

theorem affine_pos_of_endpoints {α β a b r : ℝ} (hab : a < b) (ha : a ≤ r) (hb : r ≤ b)
    (h1 : 0 < α + β * a) (h2 : 0 < α + β * b) : 0 < α + β * r := by
  have key : (α + β * r) * (b - a) = (α + β * a) * (b - r) + (α + β * b) * (r - a) := by ring
  have p2 := mul_nonneg h2.le (sub_nonneg.2 ha)
  have hpos : 0 < (α + β * r) * (b - a) := by
    rw [key]
    rcases eq_or_lt_of_le hb with h | h
    · rw [h, sub_self, mul_zero, zero_add]; exact mul_pos h2 (by linarith)
    · have := mul_pos h1 (sub_pos.2 h); linarith
  nlinarith [hpos, sub_pos.2 hab]

theorem R_pos (j : ℕ) (hj : j < 176) : (0 : ℝ) < R j := by
  have hj' : (j : ℚ) < 176 := by exact_mod_cast hj
  have : (0 : ℚ) < R j := by rw [R_eq]; linarith
  exact_mod_cast this

theorem left_lt_R (j : ℕ) : (left j : ℝ) < R j := by
  have : left j < R j := by rw [left_eq, R_eq]; linarith
  exact_mod_cast this

/-- A line that is a strict minorant (margin `pad`) of `Y_j - δ` at both endpoints of stage `j`
is one on the whole stage `[left j, R j]`. -/
theorem minorant_Icc (j : ℕ) (hj : j < 176) (b0 b1 : ℝ)
    (hl : 0 < fY (R j : ℝ) (gain j) (cut j) (left j) - 1 / 25000000 - fline b0 b1 (left j)
      - 1 / 10000000)
    (hR : 0 < fY (R j : ℝ) (gain j) (cut j) (R j) - 1 / 25000000 - fline b0 b1 (R j)
      - 1 / 10000000)
    (r : ℝ) (hr1 : (left j : ℝ) ≤ r) (hr2 : r ≤ R j) :
    0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000 - fline b0 b1 r - 1 / 10000000 := by
  have hR0 := R_pos j hj
  have aff : ∀ x : ℝ, fY (R j : ℝ) (gain j) (cut j) x - 1 / 25000000 - fline b0 b1 x
      - 1 / 10000000 = ((1 / (cut j : ℝ) - 2) / 6 - 1 / 25000000 - b0 - 1 / 10000000)
        + ((gain j : ℝ) / R j - (1 / (cut j : ℝ) - 2) / 6 / R j + b1) * x := by
    intro x; simp only [fY, fu, fline]; ring
  rw [aff] at hl hR ⊢
  exact affine_pos_of_endpoints (left_lt_R j) hr1 hr2 hl hR

/-- Every `r ∈ [LEFT, TOP]` lies in some stage. -/
theorem exists_stage (r : ℝ) (h1 : 1467 / 2000 ≤ r) (h2 : r ≤ 311 / 400) :
    ∃ j < 176, (left j : ℝ) ≤ r ∧ r ≤ R j := by
  have key : ∀ k m : ℕ, m + k = 176 → r ≤ 311 / 400 - (m : ℝ) / 4000 →
      ∃ j < 176, (left j : ℝ) ≤ r ∧ r ≤ R j := by
    intro k
    induction k with
    | zero =>
      intro m hm hr
      have hm' : m = 176 := by omega
      subst hm'
      push_cast at hr
      refine ⟨175, by norm_num, ?_, ?_⟩
      · rw [left_eq]; push_cast; linarith
      · rw [R_eq]; push_cast; linarith
    | succ k ih =>
      intro m hm hr
      by_cases hc : r ≤ 311 / 400 - ((m + 1 : ℕ) : ℝ) / 4000
      · exact ih (m + 1) (by omega) hc
      · refine ⟨m, by omega, ?_, ?_⟩
        · rw [left_eq]; push_cast at hc ⊢; linarith
        · rw [R_eq]; push_cast; linarith
  exact key 176 0 (by norm_num) (by simpa using h2)

/-- The line used by stage `n ≥ 1` is a strict minorant of the proved gain on
every earlier stage, on the whole stage interval. -/
theorem chain_minorant_Icc (n : ℕ) (h1 : 1 ≤ n) (hn : n < 176) (j : ℕ) (hj : j < n) (r : ℝ)
    (hr1 : (left j : ℝ) ≤ r) (hr2 : r ≤ R j) :
    0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000 - fline (a0 n : ℝ) (a1 n) r
      - 1 / 10000000 :=
  minorant_Icc j (by omega) _ _ (chain_minorant n h1 hn j hj _ (Or.inl rfl))
    (chain_minorant n h1 hn j hj _ (Or.inr rfl)) r hr1 hr2

/-- The outer lines on the whole chain `[LEFT, TOP]`: for every `r` there is a stage
`j` containing `r` on which the line is a strict minorant of the proved gain `Y_j(r) - δ`. -/
theorem outer_minorant_chain (i : ℕ) (hi : OuterIndex i) (r : ℝ) (h1 : 1467 / 2000 ≤ r)
    (h2 : r ≤ 311 / 400) :
    ∃ j < 176, (left j : ℝ) ≤ r ∧ r ≤ R j ∧
      0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000 - fline (own0 i : ℝ) (own1 i) r
        - 1 / 10000000 := by
  obtain ⟨j, hj, hr1, hr2⟩ := exists_stage r h1 h2
  exact ⟨j, hj, hr1, hr2, minorant_Icc j hj _ _ (outer_minorant i hi j hj _ (Or.inl rfl))
    (outer_minorant i hi j hj _ (Or.inr rfl)) r hr1 hr2⟩

/-! ### The line of the outer return

`(g0, g1) = (552429/10000000, 7227847/100000000)` (just below the own line of stage 97).
Checked like an outer line (pads `δ = 4·10^-8` and `pad = 10^-7`) against both endpoints of all
176 stages; the minimal exact value of
`Y_j(r) - δ - l(r) - pad` is `6041/10^11` (at `r = 753/1000`, stage 98). -/

theorem return_ok :
    (lineOK (552429 / 10000000) (7227847 / 100000000) &&
      (List.range 176).all fun j => minorOK (552429 / 10000000) (7227847 / 100000000) (stage j))
      = true := by
  decide +kernel

/-- A line `(b0, b1)` passing `minorOK` on all 176 stages is a strict minorant (margin `pad`) of
`Y_j - δ` at both endpoints of every stage. The line is kept symbolic here so that the cast
normalization does not fold its coefficients into large numerals. -/
theorem line_minorant {b0 b1 : ℚ} (h : ∀ j < 176, minorOK b0 b1 (stage j) = true) (j : ℕ)
    (hj : j < 176) (r : ℚ) (hr : r = left j ∨ r = R j) :
    0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000 - fline (b0 : ℝ) b1 r - 1 / 10000000 := by
  obtain ⟨hl, hR⟩ := minorOK_sound (h j hj)
  rcases hr with rfl | rfl
  · exact cast_pos_of hl (by chain_cast)
  · exact cast_pos_of hR (by chain_cast)

/-- The return line is a strict minorant (margin `pad`) of `Y_j - δ` at both endpoints of every
stage `j < 176`. -/
theorem return_minorant (j : ℕ) (hj : j < 176) (r : ℚ) (hr : r = left j ∨ r = R j) :
    0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000
      - fline (552429 / 10000000 : ℝ) (7227847 / 100000000) r - 1 / 10000000 := by
  have h := return_ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have key := line_minorant h.2 j hj r hr
  simp only [Rat.cast_div, Rat.cast_ofNat] at key
  exact key

/-- The return line is a strict minorant of the proved gain on the whole chain `[LEFT, TOP]`. -/
theorem return_line_minorant (r : ℝ) (h : 1467 / 2000 ≤ r ∧ r ≤ 311 / 400) :
    ∃ j < 176, (left j : ℝ) ≤ r ∧ r ≤ R j ∧
      0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000
        - fline (552429 / 10000000 : ℝ) (7227847 / 100000000) r - 1 / 10000000 := by
  obtain ⟨j, hj, hr1, hr2⟩ := exists_stage r h.1 h.2
  exact ⟨j, hj, hr1, hr2, minorant_Icc j hj _ _ (return_minorant j hj _ (Or.inl rfl))
    (return_minorant j hj _ (Or.inr rfl)) r hr1 hr2⟩

/-- The return line is negative at `TOP`, slope in `(0, 2/5)`. -/
theorem return_line :
    fline (552429 / 10000000 : ℝ) (7227847 / 100000000) (311 / 400) < 0 ∧
      (0 : ℝ) < 7227847 / 100000000 ∧ (7227847 / 100000000 : ℝ) < 2 / 5 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  simp only [fline]; norm_num

end Real

end Qrh.MarkedAnchor.Anchor.ChainCheck
