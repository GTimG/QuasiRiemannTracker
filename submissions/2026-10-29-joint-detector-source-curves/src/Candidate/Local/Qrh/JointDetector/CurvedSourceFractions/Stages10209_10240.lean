/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10209_10240
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97393052091241,97392681236919,97392310362374,97391939467607,97391568552618,97391197617407,97390826661976,97390455686324,97390084690452,97389713674361,97389342638051,97388971581523,97388600504778,97388229407815,97387858290636,97387487153241,97387115995630,97386744817804,97386373619764,97386002401510,97385631163043,97385259904363,97384888625471,97384517326367,97384146007052,97383774667526,97383403307790,97383031927844,97382660527689,97382289107326,97381917666755,97381546205977,97381174724992]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10208+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10209 := params 0
abbrev ray10209 := rays 0
def bank10209 : Fin 2 → Cell := twoBank p10209 ray10209
theorem signs10209 : ∀ j, Signs p10209 (bank10209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10210 := params 1
abbrev ray10210 := rays 1
def bank10210 : Fin 2 → Cell := twoBank p10210 ray10210
theorem signs10210 : ∀ j, Signs p10210 (bank10210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10211 := params 2
abbrev ray10211 := rays 2
def bank10211 : Fin 2 → Cell := twoBank p10211 ray10211
theorem signs10211 : ∀ j, Signs p10211 (bank10211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10212 := params 3
abbrev ray10212 := rays 3
def bank10212 : Fin 2 → Cell := twoBank p10212 ray10212
theorem signs10212 : ∀ j, Signs p10212 (bank10212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10213 := params 4
abbrev ray10213 := rays 4
def bank10213 : Fin 2 → Cell := twoBank p10213 ray10213
theorem signs10213 : ∀ j, Signs p10213 (bank10213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10214 := params 5
abbrev ray10214 := rays 5
def bank10214 : Fin 2 → Cell := twoBank p10214 ray10214
theorem signs10214 : ∀ j, Signs p10214 (bank10214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10215 := params 6
abbrev ray10215 := rays 6
def bank10215 : Fin 2 → Cell := twoBank p10215 ray10215
theorem signs10215 : ∀ j, Signs p10215 (bank10215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10216 := params 7
abbrev ray10216 := rays 7
def bank10216 : Fin 2 → Cell := twoBank p10216 ray10216
theorem signs10216 : ∀ j, Signs p10216 (bank10216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10217 := params 8
abbrev ray10217 := rays 8
def bank10217 : Fin 2 → Cell := twoBank p10217 ray10217
theorem signs10217 : ∀ j, Signs p10217 (bank10217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10218 := params 9
abbrev ray10218 := rays 9
def bank10218 : Fin 2 → Cell := twoBank p10218 ray10218
theorem signs10218 : ∀ j, Signs p10218 (bank10218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10219 := params 10
abbrev ray10219 := rays 10
def bank10219 : Fin 2 → Cell := twoBank p10219 ray10219
theorem signs10219 : ∀ j, Signs p10219 (bank10219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10220 := params 11
abbrev ray10220 := rays 11
def bank10220 : Fin 2 → Cell := twoBank p10220 ray10220
theorem signs10220 : ∀ j, Signs p10220 (bank10220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10221 := params 12
abbrev ray10221 := rays 12
def bank10221 : Fin 2 → Cell := twoBank p10221 ray10221
theorem signs10221 : ∀ j, Signs p10221 (bank10221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10222 := params 13
abbrev ray10222 := rays 13
def bank10222 : Fin 2 → Cell := twoBank p10222 ray10222
theorem signs10222 : ∀ j, Signs p10222 (bank10222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10223 := params 14
abbrev ray10223 := rays 14
def bank10223 : Fin 2 → Cell := twoBank p10223 ray10223
theorem signs10223 : ∀ j, Signs p10223 (bank10223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10224 := params 15
abbrev ray10224 := rays 15
def bank10224 : Fin 2 → Cell := twoBank p10224 ray10224
theorem signs10224 : ∀ j, Signs p10224 (bank10224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10225 := params 16
abbrev ray10225 := rays 16
def bank10225 : Fin 2 → Cell := twoBank p10225 ray10225
theorem signs10225 : ∀ j, Signs p10225 (bank10225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10226 := params 17
abbrev ray10226 := rays 17
def bank10226 : Fin 2 → Cell := twoBank p10226 ray10226
theorem signs10226 : ∀ j, Signs p10226 (bank10226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10227 := params 18
abbrev ray10227 := rays 18
def bank10227 : Fin 2 → Cell := twoBank p10227 ray10227
theorem signs10227 : ∀ j, Signs p10227 (bank10227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10228 := params 19
abbrev ray10228 := rays 19
def bank10228 : Fin 2 → Cell := twoBank p10228 ray10228
theorem signs10228 : ∀ j, Signs p10228 (bank10228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10229 := params 20
abbrev ray10229 := rays 20
def bank10229 : Fin 2 → Cell := twoBank p10229 ray10229
theorem signs10229 : ∀ j, Signs p10229 (bank10229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10230 := params 21
abbrev ray10230 := rays 21
def bank10230 : Fin 2 → Cell := twoBank p10230 ray10230
theorem signs10230 : ∀ j, Signs p10230 (bank10230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10231 := params 22
abbrev ray10231 := rays 22
def bank10231 : Fin 2 → Cell := twoBank p10231 ray10231
theorem signs10231 : ∀ j, Signs p10231 (bank10231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10232 := params 23
abbrev ray10232 := rays 23
def bank10232 : Fin 2 → Cell := twoBank p10232 ray10232
theorem signs10232 : ∀ j, Signs p10232 (bank10232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10233 := params 24
abbrev ray10233 := rays 24
def bank10233 : Fin 2 → Cell := twoBank p10233 ray10233
theorem signs10233 : ∀ j, Signs p10233 (bank10233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10234 := params 25
abbrev ray10234 := rays 25
def bank10234 : Fin 2 → Cell := twoBank p10234 ray10234
theorem signs10234 : ∀ j, Signs p10234 (bank10234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10235 := params 26
abbrev ray10235 := rays 26
def bank10235 : Fin 2 → Cell := twoBank p10235 ray10235
theorem signs10235 : ∀ j, Signs p10235 (bank10235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10236 := params 27
abbrev ray10236 := rays 27
def bank10236 : Fin 2 → Cell := twoBank p10236 ray10236
theorem signs10236 : ∀ j, Signs p10236 (bank10236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10237 := params 28
abbrev ray10237 := rays 28
def bank10237 : Fin 2 → Cell := twoBank p10237 ray10237
theorem signs10237 : ∀ j, Signs p10237 (bank10237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10238 := params 29
abbrev ray10238 := rays 29
def bank10238 : Fin 2 → Cell := twoBank p10238 ray10238
theorem signs10238 : ∀ j, Signs p10238 (bank10238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10239 := params 30
abbrev ray10239 := rays 30
def bank10239 : Fin 2 → Cell := twoBank p10239 ray10239
theorem signs10239 : ∀ j, Signs p10239 (bank10239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10240 := params 31
abbrev ray10240 := rays 31
def bank10240 : Fin 2 → Cell := twoBank p10240 ray10240
theorem signs10240 : ∀ j, Signs p10240 (bank10240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10209_10240
