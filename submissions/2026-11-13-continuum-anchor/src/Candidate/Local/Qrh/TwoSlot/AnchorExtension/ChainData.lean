/- Copyright (c) 2026 Sil. Apache-2.0.
256-stage reparameterization copyright (c) 2026 Joseph Bebel. Apache-2.0.
Derived from PR137, head 9d81a4c0b0e8338ef458f3ba5139657ae5404fde.
The cutoff and stage width instantiate the frozen exact extension at 016fcf13. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Floor

/-!
# Anchor.ChainData

The 256-stage anchor chain on `[1467/2000, 311/400]` (stage width `11/64000`), generated from an
exact rational recursion (not from a saved table).

Constants:
* `STEP = 11/64000`, `TOP = 311/400`, `DELTA = 1/25000000`, `PAD = 1/10^7`; `LEFT = 1467/2000`.

Generic formulas (over any field `K`; used at `ℚ` for the computation and at `ℝ` in the exported
statements, so the real statements use literally the same formulas):
* `fH R r = r/R` (`H`), `fu R r = (1 - r/R)/6` (`u`),
* `fY R z k r = (r/R) z + (1/k - 2) u` (the proved gain `Y`),
* `fS = (1-r)/2 + Y` (`S`), `fs = S - u` (`s0`),
* `fwb R z a0 a1 = (R/2 + z - a0)/(1/2 - a1)` (at stage 0, `a0 = a1 = 0`, this equals `R + 2 z`),
* `fthr` (the threshold), `fF0` (`F0`),
* `fg R z k a0 a1 r ν = (r + s0 - H/2 - H a0 - u/ν)/(1/2 - a1)` (at `ν = k` and at `ν = 3/4`),
  `fw = fg/H + 10^-6` (`w_lo = fw … k`, `w_hi = fw … (3/4)`),
  `fsig = (1 - w)/2 + a0 - a1 w` at `ν = 3/4` (the argument of `max 0` in gate 13),
* `fline a0 a1 r = a0 - a1 r` (the affine minorant `l(r)`).

Roundings: `qfloor q = q.num / q.den` (`Int` Euclidean division, `= ⌊q⌋`, see
`qfloor_eq_floor`), `qceil q = -qfloor (-q)` (`= ⌈q⌉`, see `qceil_eq_ceil`).

Stages.  A `Stage` stores the inputs of one step of the recursion:
`R` (right end), `gain` (entry gain `z_R`), and the line `(a0, a1)` used by the HIGH child
(`(0, 0)` at stage 0).
* `Stage.left = R - STEP`, `Stage.wb`, `Stage.thr`,
* `Stage.cut` is the micro-rounded minimum paying `HIGH + CUT_RESERVE` at the
  smallest stage radius, or the retained lower cutoff `45457/125000`, whichever is larger.
* `Stage.F0`, `Stage.Y`,
* `Stage.own1`, `Stage.own0` (the stage's own lowered line through `Y - DELTA - 2 PAD` at both
  endpoints),
* `Stage.nextGain = ⌊(Y(left) - DELTA) 10^10⌋ / 10^10`,
* `Stage.next = (left, nextGain, own0, own1)`,
* `stage0 = (311/400, 0, 0, 0)`, `stage n = next^[n] stage0` (by recursion).
Abbreviations `R n`, `gain n`, `cut n`, `a0 n`, `a1 n`, `left n`, `wb n`, `F0 n`, `own0 n`,
`own1 n` refer to `stage n`.

Gates (checked at `r ∈ {left, R}`): `gate1 … gate14`, each in the form `0 < value`.  `gate13`
contains `max 0 (fsig …)` and is stated over a field with `Max`.  The Boolean checker and its
soundness theorems are in `Anchor.ChainCheck`.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorExtension.ChainData

/-! ### Constants -/

/-- Stage width. -/
def STEP : ℚ := 11 / 64000
/-- Right end of the chain. -/
def TOP : ℚ := 311 / 400
/-- Left end of the chain. -/
def LEFT : ℚ := 1467 / 2000
/-- Stage decrement `δ = 4·10^-8`. -/
def DELTA : ℚ := 1 / 25000000
/-- Pad `10^-7`. -/
def PAD : ℚ := 1 / 10000000

/-! ### Generic formulas -/

section Formulas
variable {K : Type*} [Field K]

/-- `H = r/R`. -/
def fH (R r : K) : K := r / R
/-- `u = (1 - H)/6`. -/
def fu (R r : K) : K := (1 - r / R) / 6
/-- `Y(r) = H z + (1/k - 2)(1 - H)/6`. -/
def fY (R z k r : K) : K := r / R * z + (1 / k - 2) * fu R r
/-- `S = (1-r)/2 + Y(r)`. -/
def fS (R z k r : K) : K := (1 - r) / 2 + fY R z k r
/-- `s0 = S - u`. -/
def fs (R z k r : K) : K := fS R z k r - fu R r
/-- `wb = (R/2 + z - a0)/(1/2 - a1)`. -/
def fwb (R z a0 a1 : K) : K := (R / 2 + z - a0) / (1 / 2 - a1)
/-- `threshold = (5 wb/4 - 5/6)/(3 wb/2 - (1+R)/2 - z)`. -/
def fthr (R z a0 a1 : K) : K :=
  (5 * fwb R z a0 a1 / 4 - 5 / 6) / (3 * fwb R z a0 a1 / 2 - (1 + R) / 2 - z)
/-- `F0 = 5/6 - (5/4 - 3k/2) wb - k(1+R)/2 - k z`. -/
def fF0 (R z k a0 a1 : K) : K :=
  5 / 6 - (5 / 4 - 3 * k / 2) * fwb R z a0 a1 - k * (1 + R) / 2 - k * z
/-- `g(ν) = (r + s0 - H/2 - H a0 - u/ν)/(1/2 - a1)` (used at `ν = k` and at `ν = 3/4`). -/
def fg (R z k a0 a1 r ν : K) : K :=
  (r + fs R z k r - fH R r / 2 - fH R r * a0 - fu R r / ν) / (1 / 2 - a1)
/-- `w(ν) = g(ν)/H + 10^-6`. -/
def fw (R z k a0 a1 r ν : K) : K := fg R z k a0 a1 r ν / fH R r + 1 / 1000000
/-- `(1 - w_hi)/2 + a0 - a1 w_hi`, `w_hi = w(3/4)` (the argument of `max 0` in gate 13). -/
def fsig (R z k a0 a1 r : K) : K :=
  (1 - fw R z k a0 a1 r (3 / 4)) / 2 + a0 - a1 * fw R z k a0 a1 r (3 / 4)
/-- The affine line `l(r) = a0 - a1 r`. -/
def fline (a0 a1 r : K) : K := a0 - a1 * r

/-! The fourteen gates, in order. -/

/-- Gate 1: `H F0 - 3/100000`. -/
def gate1 (R z k a0 a1 r : K) : K := fH R r * fF0 R z k a0 a1 - 3 / 100000
/-- Gate 2: `137/1000 - S`. -/
def gate2 (R z k r : K) : K := 137 / 1000 - fS R z k r
/-- Gate 3: `14/100 - S/H`. -/
def gate3 (R z k r : K) : K := 14 / 100 - fS R z k r / fH R r
/-- Gate 4: `9/10 - r - S - 4u`. -/
def gate4 (R z k r : K) : K := 9 / 10 - r - fS R z k r - 4 * fu R r
/-- Gate 5: `91/100 - r - S - 4u`. -/
def gate5 (R z k r : K) : K := 91 / 100 - r - fS R z k r - 4 * fu R r
/-- Gate 6: `5/6 + 21/250 - r - S - 3u - 1/100`. -/
def gate6 (R z k r : K) : K := 5 / 6 + 21 / 250 - r - fS R z k r - 3 * fu R r - 1 / 100
/-- Gate 7: `3H - 2r - 8 s0 - 1/5`. -/
def gate7 (R z k r : K) : K := 3 * fH R r - 2 * r - 8 * fs R z k r - 1 / 5
/-- Gate 8: `r - 1/2 - Y + u - 1/5`. -/
def gate8 (R z k r : K) : K := r - 1 / 2 - fY R z k r + fu R r - 1 / 5
/-- Gate 9: `r/2 - s0 - (3/2)(5/6 - k)(u/k^2)/(1/2 - a1) - 1/10` (`k^2` written `k * k`). -/
def gate9 (R z k a1 r : K) : K :=
  r / 2 - fs R z k r - 3 / 2 * (5 / 6 - k) * (fu R r / (k * k)) / (1 / 2 - a1) - 1 / 10
/-- Gate 10: `H + u - H/6 - 1/15 - (3/4) r - s0 - 3/100`. -/
def gate10 (R z k r : K) : K :=
  fH R r + fu R r - fH R r / 6 - 1 / 15 - 3 / 4 * r - fs R z k r - 3 / 100
/-- Gate 11: `w_lo - 2/3`, `w_lo = w(k)`. -/
def gate11 (R z k a0 a1 r : K) : K := fw R z k a0 a1 r k - 2 / 3
/-- Gate 12: `79/100 - w_hi`, `w_hi = w(3/4)`. -/
def gate12 (R z k a0 a1 r : K) : K := 79 / 100 - fw R z k a0 a1 r (3 / 4)
/-- Gate 13: `1 - (3/4) w_hi - (3/4) max 0 σ - 1/6`. -/
def gate13 [Max K] (R z k a0 a1 r : K) : K :=
  1 - 3 / 4 * fw R z k a0 a1 r (3 / 4) - 3 / 4 * max 0 (fsig R z k a0 a1 r) - 1 / 6
/-- Gate 14: `79/100 - r - (2 + 10^-11) u`. -/
def gate14 (R r : K) : K := 79 / 100 - r - (2 + 1 / 100000000000) * fu R r

end Formulas

/-! ### Roundings -/

/-- `⌊q⌋` by Euclidean division of the reduced numerator by the (positive) denominator. -/
def qfloor (q : ℚ) : ℤ := q.num / (q.den : ℤ)
/-- `⌈q⌉ = -⌊-q⌋`. -/
def qceil (q : ℚ) : ℤ := -qfloor (-q)

theorem qfloor_eq_floor (q : ℚ) : qfloor q = ⌊q⌋ := by
  rw [qfloor, ← Rat.floor_def]; rfl

theorem qceil_eq_ceil (q : ℚ) : qceil q = ⌈q⌉ := by
  rw [qceil, qfloor_eq_floor, Int.floor_neg, neg_neg]

/-! ### Stages -/

/-- Inputs of one step of the stage recursion. -/
structure Stage where
  /-- right end `R` -/
  R : ℚ
  /-- entry gain `z_R` (`gain`) -/
  gain : ℚ
  /-- intercept of the line used by the HIGH child -/
  a0 : ℚ
  /-- slope of the line used by the HIGH child -/
  a1 : ℚ

namespace Stage
variable (s : Stage)

/-- Left end `R - STEP`. -/
def left : ℚ := s.R - STEP
/-- `wb` of the stage. -/
def wb : ℚ := fwb s.R s.gain s.a0 s.a1
/-- Threshold of the stage. -/
def thr : ℚ := fthr s.R s.gain s.a0 s.a1
/-- The least micro-rounded cutoff paying the fixed HIGH floor and reserve,
with Sil's original lower cutoff retained. -/
def cut : ℚ := max (45457 / 125000)
  ((qceil (((5 * s.wb / 4 - 5 / 6 +
    (3 / 100000 + 1 / 10000000) / fH s.R s.left) /
    (3 * s.wb / 2 - (1 + s.R) / 2 - s.gain)) * 1000000) : ℚ) / 1000000)
/-- `F0` of the stage at `k = cut`. -/
def F0 : ℚ := fF0 s.R s.gain s.cut s.a0 s.a1
/-- The proved gain `Y(r)` of the stage at `k = cut`. -/
def Y (r : ℚ) : ℚ := fY s.R s.gain s.cut r
/-- `own1 = -(y1 - y0)/(R - left)` with `y0 = Y(left) - δ - 2 pad`, `y1 = Y(R) - δ - 2 pad`. -/
def own1 : ℚ :=
  -((s.Y s.R - DELTA - 2 * PAD) - (s.Y s.left - DELTA - 2 * PAD)) / (s.R - s.left)
/-- `own0 = y0 + own1 left`. -/
def own0 : ℚ := (s.Y s.left - DELTA - 2 * PAD) + s.own1 * s.left
/-- `next_gain = floor((Y(left) - δ) 10^10)/10^10`. -/
def nextGain : ℚ := (qfloor ((s.Y s.left - DELTA) * 10000000000) : ℚ) / 10000000000
/-- The next stage: right end `left`, entry gain `nextGain`, line `(own0, own1)`. -/
def next : Stage := ⟨s.left, s.nextGain, s.own0, s.own1⟩

end Stage

/-- The first stage: `R = 311/400`, gain `0`, line `a0 = a1 = 0`. -/
def stage0 : Stage := ⟨TOP, 0, 0, 0⟩

/-- The `n`-th stage (`n = 0, …, 255`). -/
def stage : ℕ → Stage
  | 0 => stage0
  | n + 1 => (stage n).next

/-- Right end of stage `n`. -/
abbrev R (n : ℕ) : ℚ := (stage n).R
/-- Left end of stage `n`. -/
abbrev left (n : ℕ) : ℚ := (stage n).left
/-- Entry gain of stage `n`. -/
abbrev gain (n : ℕ) : ℚ := (stage n).gain
/-- Threshold `k` of stage `n`. -/
abbrev cut (n : ℕ) : ℚ := (stage n).cut
/-- Intercept of the line used at stage `n` (`= own0 (n-1)`, `0` at `n = 0`). -/
abbrev a0 (n : ℕ) : ℚ := (stage n).a0
/-- Slope of the line used at stage `n` (`= own1 (n-1)`, `0` at `n = 0`). -/
abbrev a1 (n : ℕ) : ℚ := (stage n).a1
/-- `w_b` of stage `n`. -/
abbrev wb (n : ℕ) : ℚ := (stage n).wb
/-- `F0` of stage `n`. -/
abbrev F0 (n : ℕ) : ℚ := (stage n).F0
/-- Intercept of the own line of stage `n`. -/
abbrev own0 (n : ℕ) : ℚ := (stage n).own0
/-- Slope of the own line of stage `n`. -/
abbrev own1 (n : ℕ) : ℚ := (stage n).own1

theorem stage_succ (n : ℕ) : stage (n + 1) = (stage n).next := rfl

theorem R_succ (n : ℕ) : R (n + 1) = left n := rfl
theorem gain_succ (n : ℕ) : gain (n + 1) = (stage n).nextGain := rfl
theorem a0_succ (n : ℕ) : a0 (n + 1) = own0 n := rfl
theorem a1_succ (n : ℕ) : a1 (n + 1) = own1 n := rfl
theorem a0_zero : a0 0 = 0 := rfl
theorem a1_zero : a1 0 = 0 := rfl
theorem gain_zero : gain 0 = 0 := rfl

/-- `R_n = 311/400 - n*11/64000`. -/
theorem R_eq (n : ℕ) : R n = 311 / 400 - n * 11 / 64000 := by
  induction n with
  | zero =>
    have h : R 0 = 311 / 400 := rfl
    rw [h]; simp
  | succ n ih =>
    have h : R (n + 1) = R n - 11 / 64000 := rfl
    rw [h, ih, Nat.cast_succ]; ring

theorem left_eq (n : ℕ) : left n = 311 / 400 - (n + 1) * 11 / 64000 := by
  rw [← R_succ, R_eq, Nat.cast_succ]

/-- `gain (n+1) = ⌊(Y_n(left_n) - δ) 10^10⌋ / 10^10` with Mathlib's floor. -/
theorem gain_succ_eq (n : ℕ) :
    gain (n + 1) = (⌊((stage n).Y (left n) - DELTA) * 10000000000⌋ : ℚ) / 10000000000 := by
  rw [gain_succ, Stage.nextGain, qfloor_eq_floor]

end Qrh.TwoSlot.AnchorExtension.ChainData
