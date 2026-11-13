/- Copyright (c) 2026 Sil. Apache-2.0.
256-stage reparameterization copyright (c) 2026 Joseph Bebel. Apache-2.0.
Derived from PR137 at 9d81a4c0b0e8338ef458f3ba5139657ae5404fde.
All gates and earlier-source comparisons are checked by Lean's kernel from
ChainData's exact recurrence. This module supplies finite data, not an analytic estimate. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.ChainData
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.FinitePartition

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorExtension.ChainCheck
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


abbrev ChainOK : Prop :=
  (∀ n < 256, StageGates (stage n)) ∧ (∀ n < 255, ChainLine (n + 1))

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


theorem allFrom_add {p : ℕ → Bool} {lo a b : ℕ}
    (ha : allFrom p lo a = true) (hb : allFrom p (lo + a) b = true) :
    allFrom p lo (a + b) = true := by
  induction a generalizing lo with
  | zero => simpa [allFrom] using hb
  | succ a ih =>
    simp only [allFrom, Bool.and_eq_true] at ha
    simp only [Nat.succ_add, allFrom, Bool.and_eq_true]
    refine ⟨ha.1, ih ha.2 ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb

theorem stages_ok_0 : allFrom (fun n => stageOK (stage n)) 0 8 = true := by
  decide +kernel

theorem stages_ok_8 : allFrom (fun n => stageOK (stage n)) 8 8 = true := by
  decide +kernel

theorem stages_ok_16 : allFrom (fun n => stageOK (stage n)) 16 8 = true := by
  decide +kernel

theorem stages_ok_24 : allFrom (fun n => stageOK (stage n)) 24 8 = true := by
  decide +kernel

theorem stages_ok_32 : allFrom (fun n => stageOK (stage n)) 32 8 = true := by
  decide +kernel

theorem stages_ok_40 : allFrom (fun n => stageOK (stage n)) 40 8 = true := by
  decide +kernel

theorem stages_ok_48 : allFrom (fun n => stageOK (stage n)) 48 8 = true := by
  decide +kernel

theorem stages_ok_56 : allFrom (fun n => stageOK (stage n)) 56 8 = true := by
  decide +kernel

theorem stages_ok_64 : allFrom (fun n => stageOK (stage n)) 64 8 = true := by
  decide +kernel

theorem stages_ok_72 : allFrom (fun n => stageOK (stage n)) 72 8 = true := by
  decide +kernel

theorem stages_ok_80 : allFrom (fun n => stageOK (stage n)) 80 8 = true := by
  decide +kernel

theorem stages_ok_88 : allFrom (fun n => stageOK (stage n)) 88 8 = true := by
  decide +kernel

theorem stages_ok_96 : allFrom (fun n => stageOK (stage n)) 96 8 = true := by
  decide +kernel

theorem stages_ok_104 : allFrom (fun n => stageOK (stage n)) 104 8 = true := by
  decide +kernel

theorem stages_ok_112 : allFrom (fun n => stageOK (stage n)) 112 8 = true := by
  decide +kernel

theorem stages_ok_120 : allFrom (fun n => stageOK (stage n)) 120 8 = true := by
  decide +kernel

theorem stages_ok_128 : allFrom (fun n => stageOK (stage n)) 128 8 = true := by
  decide +kernel

theorem stages_ok_136 : allFrom (fun n => stageOK (stage n)) 136 8 = true := by
  decide +kernel

theorem stages_ok_144 : allFrom (fun n => stageOK (stage n)) 144 8 = true := by
  decide +kernel

theorem stages_ok_152 : allFrom (fun n => stageOK (stage n)) 152 8 = true := by
  decide +kernel

theorem stages_ok_160 : allFrom (fun n => stageOK (stage n)) 160 8 = true := by
  decide +kernel

theorem stages_ok_168 : allFrom (fun n => stageOK (stage n)) 168 8 = true := by
  decide +kernel

theorem stages_ok_176 : allFrom (fun n => stageOK (stage n)) 176 8 = true := by
  decide +kernel

theorem stages_ok_184 : allFrom (fun n => stageOK (stage n)) 184 8 = true := by
  decide +kernel

theorem stages_ok_192 : allFrom (fun n => stageOK (stage n)) 192 8 = true := by
  decide +kernel

theorem stages_ok_200 : allFrom (fun n => stageOK (stage n)) 200 8 = true := by
  decide +kernel

theorem stages_ok_208 : allFrom (fun n => stageOK (stage n)) 208 8 = true := by
  decide +kernel

theorem stages_ok_216 : allFrom (fun n => stageOK (stage n)) 216 8 = true := by
  decide +kernel

theorem stages_ok_224 : allFrom (fun n => stageOK (stage n)) 224 8 = true := by
  decide +kernel

theorem stages_ok_232 : allFrom (fun n => stageOK (stage n)) 232 8 = true := by
  decide +kernel

theorem stages_ok_240 : allFrom (fun n => stageOK (stage n)) 240 8 = true := by
  decide +kernel

theorem stages_ok_248 : allFrom (fun n => stageOK (stage n)) 248 8 = true := by
  decide +kernel

theorem stages_ok_all : allFrom (fun n => stageOK (stage n)) 0 256 = true :=
  allFrom_add stages_ok_0 (allFrom_add stages_ok_8 (allFrom_add stages_ok_16 (allFrom_add stages_ok_24 (allFrom_add stages_ok_32 (allFrom_add stages_ok_40 (allFrom_add stages_ok_48 (allFrom_add stages_ok_56 (allFrom_add stages_ok_64 (allFrom_add stages_ok_72 (allFrom_add stages_ok_80 (allFrom_add stages_ok_88 (allFrom_add stages_ok_96 (allFrom_add stages_ok_104 (allFrom_add stages_ok_112 (allFrom_add stages_ok_120 (allFrom_add stages_ok_128 (allFrom_add stages_ok_136 (allFrom_add stages_ok_144 (allFrom_add stages_ok_152 (allFrom_add stages_ok_160 (allFrom_add stages_ok_168 (allFrom_add stages_ok_176 (allFrom_add stages_ok_184 (allFrom_add stages_ok_192 (allFrom_add stages_ok_200 (allFrom_add stages_ok_208 (allFrom_add stages_ok_216 (allFrom_add stages_ok_224 (allFrom_add stages_ok_232 (allFrom_add stages_ok_240 (stages_ok_248)))))))))))))))))))))))))))))))

theorem lines_ok_1 : allFrom chainLineOK 1 4 = true := by
  decide +kernel

theorem lines_ok_5 : allFrom chainLineOK 5 4 = true := by
  decide +kernel

theorem lines_ok_9 : allFrom chainLineOK 9 4 = true := by
  decide +kernel

theorem lines_ok_13 : allFrom chainLineOK 13 4 = true := by
  decide +kernel

theorem lines_ok_17 : allFrom chainLineOK 17 4 = true := by
  decide +kernel

theorem lines_ok_21 : allFrom chainLineOK 21 4 = true := by
  decide +kernel

theorem lines_ok_25 : allFrom chainLineOK 25 4 = true := by
  decide +kernel

theorem lines_ok_29 : allFrom chainLineOK 29 4 = true := by
  decide +kernel

theorem lines_ok_33 : allFrom chainLineOK 33 4 = true := by
  decide +kernel

theorem lines_ok_37 : allFrom chainLineOK 37 4 = true := by
  decide +kernel

theorem lines_ok_41 : allFrom chainLineOK 41 4 = true := by
  decide +kernel

theorem lines_ok_45 : allFrom chainLineOK 45 4 = true := by
  decide +kernel

theorem lines_ok_49 : allFrom chainLineOK 49 4 = true := by
  decide +kernel

theorem lines_ok_53 : allFrom chainLineOK 53 4 = true := by
  decide +kernel

theorem lines_ok_57 : allFrom chainLineOK 57 4 = true := by
  decide +kernel

theorem lines_ok_61 : allFrom chainLineOK 61 4 = true := by
  decide +kernel

theorem lines_ok_65 : allFrom chainLineOK 65 4 = true := by
  decide +kernel

theorem lines_ok_69 : allFrom chainLineOK 69 4 = true := by
  decide +kernel

theorem lines_ok_73 : allFrom chainLineOK 73 4 = true := by
  decide +kernel

theorem lines_ok_77 : allFrom chainLineOK 77 4 = true := by
  decide +kernel

theorem lines_ok_81 : allFrom chainLineOK 81 4 = true := by
  decide +kernel

theorem lines_ok_85 : allFrom chainLineOK 85 4 = true := by
  decide +kernel

theorem lines_ok_89 : allFrom chainLineOK 89 4 = true := by
  decide +kernel

theorem lines_ok_93 : allFrom chainLineOK 93 4 = true := by
  decide +kernel

theorem lines_ok_97 : allFrom chainLineOK 97 4 = true := by
  decide +kernel

theorem lines_ok_101 : allFrom chainLineOK 101 4 = true := by
  decide +kernel

theorem lines_ok_105 : allFrom chainLineOK 105 4 = true := by
  decide +kernel

theorem lines_ok_109 : allFrom chainLineOK 109 4 = true := by
  decide +kernel

theorem lines_ok_113 : allFrom chainLineOK 113 4 = true := by
  decide +kernel

theorem lines_ok_117 : allFrom chainLineOK 117 4 = true := by
  decide +kernel

theorem lines_ok_121 : allFrom chainLineOK 121 4 = true := by
  decide +kernel

theorem lines_ok_125 : allFrom chainLineOK 125 4 = true := by
  decide +kernel

theorem lines_ok_129 : allFrom chainLineOK 129 4 = true := by
  decide +kernel

theorem lines_ok_133 : allFrom chainLineOK 133 4 = true := by
  decide +kernel

theorem lines_ok_137 : allFrom chainLineOK 137 4 = true := by
  decide +kernel

theorem lines_ok_141 : allFrom chainLineOK 141 4 = true := by
  decide +kernel

theorem lines_ok_145 : allFrom chainLineOK 145 4 = true := by
  decide +kernel

theorem lines_ok_149 : allFrom chainLineOK 149 4 = true := by
  decide +kernel

theorem lines_ok_153 : allFrom chainLineOK 153 4 = true := by
  decide +kernel

theorem lines_ok_157 : allFrom chainLineOK 157 4 = true := by
  decide +kernel

theorem lines_ok_161 : allFrom chainLineOK 161 4 = true := by
  decide +kernel

theorem lines_ok_165 : allFrom chainLineOK 165 4 = true := by
  decide +kernel

theorem lines_ok_169 : allFrom chainLineOK 169 4 = true := by
  decide +kernel

theorem lines_ok_173 : allFrom chainLineOK 173 4 = true := by
  decide +kernel

theorem lines_ok_177 : allFrom chainLineOK 177 4 = true := by
  decide +kernel

theorem lines_ok_181 : allFrom chainLineOK 181 4 = true := by
  decide +kernel

theorem lines_ok_185 : allFrom chainLineOK 185 4 = true := by
  decide +kernel

theorem lines_ok_189 : allFrom chainLineOK 189 4 = true := by
  decide +kernel

theorem lines_ok_193 : allFrom chainLineOK 193 4 = true := by
  decide +kernel

theorem lines_ok_197 : allFrom chainLineOK 197 4 = true := by
  decide +kernel

theorem lines_ok_201 : allFrom chainLineOK 201 4 = true := by
  decide +kernel

theorem lines_ok_205 : allFrom chainLineOK 205 4 = true := by
  decide +kernel

theorem lines_ok_209 : allFrom chainLineOK 209 4 = true := by
  decide +kernel

theorem lines_ok_213 : allFrom chainLineOK 213 4 = true := by
  decide +kernel

theorem lines_ok_217 : allFrom chainLineOK 217 4 = true := by
  decide +kernel

theorem lines_ok_221 : allFrom chainLineOK 221 4 = true := by
  decide +kernel

theorem lines_ok_225 : allFrom chainLineOK 225 4 = true := by
  decide +kernel

theorem lines_ok_229 : allFrom chainLineOK 229 4 = true := by
  decide +kernel

theorem lines_ok_233 : allFrom chainLineOK 233 4 = true := by
  decide +kernel

theorem lines_ok_237 : allFrom chainLineOK 237 4 = true := by
  decide +kernel

theorem lines_ok_241 : allFrom chainLineOK 241 4 = true := by
  decide +kernel

theorem lines_ok_245 : allFrom chainLineOK 245 4 = true := by
  decide +kernel

theorem lines_ok_249 : allFrom chainLineOK 249 4 = true := by
  decide +kernel

theorem lines_ok_253 : allFrom chainLineOK 253 3 = true := by
  decide +kernel

theorem lines_ok_all : allFrom chainLineOK 1 255 = true :=
  allFrom_add lines_ok_1 (allFrom_add lines_ok_5 (allFrom_add lines_ok_9 (allFrom_add lines_ok_13 (allFrom_add lines_ok_17 (allFrom_add lines_ok_21 (allFrom_add lines_ok_25 (allFrom_add lines_ok_29 (allFrom_add lines_ok_33 (allFrom_add lines_ok_37 (allFrom_add lines_ok_41 (allFrom_add lines_ok_45 (allFrom_add lines_ok_49 (allFrom_add lines_ok_53 (allFrom_add lines_ok_57 (allFrom_add lines_ok_61 (allFrom_add lines_ok_65 (allFrom_add lines_ok_69 (allFrom_add lines_ok_73 (allFrom_add lines_ok_77 (allFrom_add lines_ok_81 (allFrom_add lines_ok_85 (allFrom_add lines_ok_89 (allFrom_add lines_ok_93 (allFrom_add lines_ok_97 (allFrom_add lines_ok_101 (allFrom_add lines_ok_105 (allFrom_add lines_ok_109 (allFrom_add lines_ok_113 (allFrom_add lines_ok_117 (allFrom_add lines_ok_121 (allFrom_add lines_ok_125 (allFrom_add lines_ok_129 (allFrom_add lines_ok_133 (allFrom_add lines_ok_137 (allFrom_add lines_ok_141 (allFrom_add lines_ok_145 (allFrom_add lines_ok_149 (allFrom_add lines_ok_153 (allFrom_add lines_ok_157 (allFrom_add lines_ok_161 (allFrom_add lines_ok_165 (allFrom_add lines_ok_169 (allFrom_add lines_ok_173 (allFrom_add lines_ok_177 (allFrom_add lines_ok_181 (allFrom_add lines_ok_185 (allFrom_add lines_ok_189 (allFrom_add lines_ok_193 (allFrom_add lines_ok_197 (allFrom_add lines_ok_201 (allFrom_add lines_ok_205 (allFrom_add lines_ok_209 (allFrom_add lines_ok_213 (allFrom_add lines_ok_217 (allFrom_add lines_ok_221 (allFrom_add lines_ok_225 (allFrom_add lines_ok_229 (allFrom_add lines_ok_233 (allFrom_add lines_ok_237 (allFrom_add lines_ok_241 (allFrom_add lines_ok_245 (allFrom_add lines_ok_249 (lines_ok_253)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


theorem stages_all (n : ℕ) (hn : n < 256) : stageOK (stage n) = true :=
  allFrom_sound stages_ok_all n (Nat.zero_le n) hn

theorem chainLines_all (n : ℕ) (h1 : 1 ≤ n) (hn : n < 256) : chainLineOK n = true :=
  allFrom_sound lines_ok_all n h1 hn

theorem chainOK : ChainOK :=
  ⟨fun n hn => stageOK_sound (stages_all n hn),
   fun n hn => chainLineOK_sound (chainLines_all (n + 1) (by omega) (by omega))⟩

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
theorem endpoint (n : ℕ) (hn : n < 256) (r : ℚ) (hr : r = left n ∨ r = R n) :
    EndpointGates (stage n) r := by
  obtain ⟨hl, hR, -⟩ := chainOK.1 n hn
  rcases hr with rfl | rfl
  · exact hl
  · exact hR

section Gates
variable (n : ℕ) (hn : n < 256) (r : ℚ) (hr : r = left n ∨ r = R n)
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
variable (n : ℕ) (hn : n < 256)
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
theorem chain_line (n : ℕ) (h1 : 1 ≤ n) (hn : n < 256) :
    fline (a0 n : ℝ) (a1 n) (311 / 400) < 0 ∧ 0 < (a1 n : ℝ) ∧ (a1 n : ℝ) < 2 / 5 ∧
      0 < (gain n : ℝ) - fline (a0 n : ℝ) (a1 n) (R n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨⟨hT, h0, h25⟩, hg, -⟩ := chainOK.2 m (by omega)
  exact ⟨cast_lt_of hT (by chain_cast) (by norm_num), cast_lt_of h0 (by norm_num) rfl,
    cast_lt_of h25 rfl (by norm_num), cast_pos_of hg (by chain_cast)⟩

/-- The line used by stage `n ≥ 1` is a strict minorant (margin `pad`) of the proved
gain `Y_j - δ` at both endpoints of every earlier stage `j < n`. -/
theorem chain_minorant (n : ℕ) (h1 : 1 ≤ n) (hn : n < 256) (j : ℕ) (hj : j < n) (r : ℚ)
    (hr : r = left j ∨ r = R j) :
    0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000 - fline (a0 n : ℝ) (a1 n) r
      - 1 / 10000000 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hl, hR⟩ := (chainOK.2 m (by omega)).2.2 j hj
  rcases hr with rfl | rfl
  · exact cast_pos_of hl (by chain_cast)
  · exact cast_pos_of hR (by chain_cast)


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

theorem R_pos (j : ℕ) (hj : j < 256) : (0 : ℝ) < R j := by
  have hj' : (j : ℚ) < 256 := by exact_mod_cast hj
  have : (0 : ℚ) < R j := by rw [R_eq]; linarith
  exact_mod_cast this

theorem left_lt_R (j : ℕ) : (left j : ℝ) < R j := by
  have : left j < R j := by rw [left_eq, R_eq]; linarith
  exact_mod_cast this

/-- A line that is a strict minorant (margin `pad`) of `Y_j - δ` at both endpoints of stage `j`
is one on the whole stage `[left j, R j]`. -/
theorem minorant_Icc (j : ℕ) (hj : j < 256) (b0 b1 : ℝ)
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


/-- The finite-partition theorem supplies coverage independently of the
number of stages or a particular choice of equal step sizes. -/
theorem exists_stage (r : ℝ) (h1 : 1467 / 2000 ≤ r) (h2 : r ≤ 311 / 400) :
    ∃ j < 256, (left j : ℝ) ≤ r ∧ r ≤ R j := by
  have hlast : ((R 256 : ℚ) : ℝ) = 1467 / 2000 := by
    rw [R_eq]; norm_num
  have hfirst : ((R 0 : ℚ) : ℝ) = 311 / 400 := by
    rw [R_eq]; norm_num
  obtain ⟨j, hj, hl, hr⟩ := Qrh.TwoSlot.AnchorExtension.finite_partition_cover
    (fun j => ((R j : ℚ) : ℝ)) (n := 256) (by norm_num)
    (r := r) (by simpa only [hlast] using h1) (by simpa only [hfirst] using h2)
  exact ⟨j, hj, by simpa only [R_succ] using hl, hr⟩

/-- The line used by stage `n ≥ 1` is a strict minorant of the proved gain on
every earlier stage, on the whole stage interval. -/
theorem chain_minorant_Icc (n : ℕ) (h1 : 1 ≤ n) (hn : n < 256) (j : ℕ) (hj : j < n) (r : ℝ)
    (hr1 : (left j : ℝ) ≤ r) (hr2 : r ≤ R j) :
    0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000 - fline (a0 n : ℝ) (a1 n) r
      - 1 / 10000000 :=
  minorant_Icc j (by omega) _ _ (chain_minorant n h1 hn j hj _ (Or.inl rfl))
    (chain_minorant n h1 hn j hj _ (Or.inr rfl)) r hr1 hr2


/-! ### The line of the outer return

`(g0, g1) = (55755437/1000000000, 14591009/200000000)`.
Checked like an outer line (pads `δ = 4·10^-8` and `pad = 10^-7`) against both endpoints of all
256 stages; the minimal exact value of
`Y_j(r) - δ - l(r) - pad` is `767643/12800000000000`. -/

theorem return_ok :
    (lineOK (55755437 / 1000000000) (14591009 / 200000000) &&
      (List.range 256).all fun j => minorOK (55755437 / 1000000000) (14591009 / 200000000) (stage j))
      = true := by
  decide +kernel

/-- A line `(b0, b1)` passing `minorOK` on all 256 stages is a strict minorant (margin `pad`) of
`Y_j - δ` at both endpoints of every stage. The line is kept symbolic here so that the cast
normalization does not fold its coefficients into large numerals. -/
theorem line_minorant {b0 b1 : ℚ} (h : ∀ j < 256, minorOK b0 b1 (stage j) = true) (j : ℕ)
    (hj : j < 256) (r : ℚ) (hr : r = left j ∨ r = R j) :
    0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000 - fline (b0 : ℝ) b1 r - 1 / 10000000 := by
  obtain ⟨hl, hR⟩ := minorOK_sound (h j hj)
  rcases hr with rfl | rfl
  · exact cast_pos_of hl (by chain_cast)
  · exact cast_pos_of hR (by chain_cast)

/-- The return line is a strict minorant (margin `pad`) of `Y_j - δ` at both endpoints of every
stage `j < 256`. -/
theorem return_minorant (j : ℕ) (hj : j < 256) (r : ℚ) (hr : r = left j ∨ r = R j) :
    0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000
      - fline (55755437 / 1000000000 : ℝ) (14591009 / 200000000) r - 1 / 10000000 := by
  have h := return_ok
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have key := line_minorant h.2 j hj r hr
  simp only [Rat.cast_div, Rat.cast_ofNat] at key
  exact key

/-- The return line is a strict minorant of the proved gain on the whole chain `[LEFT, TOP]`. -/
theorem return_line_minorant (r : ℝ) (h : 1467 / 2000 ≤ r ∧ r ≤ 311 / 400) :
    ∃ j < 256, (left j : ℝ) ≤ r ∧ r ≤ R j ∧
      0 < fY (R j : ℝ) (gain j) (cut j) r - 1 / 25000000
        - fline (55755437 / 1000000000 : ℝ) (14591009 / 200000000) r - 1 / 10000000 := by
  obtain ⟨j, hj, hr1, hr2⟩ := exists_stage r h.1 h.2
  exact ⟨j, hj, hr1, hr2, minorant_Icc j hj _ _ (return_minorant j hj _ (Or.inl rfl))
    (return_minorant j hj _ (Or.inr rfl)) r hr1 hr2⟩

/-- The return line is negative at `TOP`, slope in `(0, 2/5)`. -/
theorem return_line :
    fline (55755437 / 1000000000 : ℝ) (14591009 / 200000000) (311 / 400) < 0 ∧
      (0 : ℝ) < 14591009 / 200000000 ∧ (14591009 / 200000000 : ℝ) < 2 / 5 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  simp only [fline]; norm_num


end Real
end Qrh.TwoSlot.AnchorExtension.ChainCheck

#print axioms Qrh.TwoSlot.AnchorExtension.ChainCheck.chainOK
#print axioms Qrh.TwoSlot.AnchorExtension.ChainCheck.return_line_minorant
