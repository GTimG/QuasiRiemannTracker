/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08257_08288
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98077700940148,98077370674667,98077040387777,98076710079479,98076379749774,98076049398662,98075719026144,98075388632221,98075058216893,98074727780161,98074397322026,98074066842489,98073736341550,98073405819209,98073075275468,98072744710327,98072414123787,98072083515848,98071752886511,98071422235777,98071091563647,98070760870121,98070430155200,98070099418884,98069768661174,98069437882071,98069107081576,98068776259689,98068445416411,98068114551743,98067783665685,98067452758238,98067121829402]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8256+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8257 := params 0
abbrev ray8257 := rays 0
def bank8257 : Fin 2 → Cell := twoBank p8257 ray8257
theorem signs8257 : ∀ j, Signs p8257 (bank8257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8258 := params 1
abbrev ray8258 := rays 1
def bank8258 : Fin 2 → Cell := twoBank p8258 ray8258
theorem signs8258 : ∀ j, Signs p8258 (bank8258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8259 := params 2
abbrev ray8259 := rays 2
def bank8259 : Fin 2 → Cell := twoBank p8259 ray8259
theorem signs8259 : ∀ j, Signs p8259 (bank8259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8260 := params 3
abbrev ray8260 := rays 3
def bank8260 : Fin 2 → Cell := twoBank p8260 ray8260
theorem signs8260 : ∀ j, Signs p8260 (bank8260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8261 := params 4
abbrev ray8261 := rays 4
def bank8261 : Fin 2 → Cell := twoBank p8261 ray8261
theorem signs8261 : ∀ j, Signs p8261 (bank8261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8262 := params 5
abbrev ray8262 := rays 5
def bank8262 : Fin 2 → Cell := twoBank p8262 ray8262
theorem signs8262 : ∀ j, Signs p8262 (bank8262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8263 := params 6
abbrev ray8263 := rays 6
def bank8263 : Fin 2 → Cell := twoBank p8263 ray8263
theorem signs8263 : ∀ j, Signs p8263 (bank8263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8264 := params 7
abbrev ray8264 := rays 7
def bank8264 : Fin 2 → Cell := twoBank p8264 ray8264
theorem signs8264 : ∀ j, Signs p8264 (bank8264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8265 := params 8
abbrev ray8265 := rays 8
def bank8265 : Fin 2 → Cell := twoBank p8265 ray8265
theorem signs8265 : ∀ j, Signs p8265 (bank8265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8266 := params 9
abbrev ray8266 := rays 9
def bank8266 : Fin 2 → Cell := twoBank p8266 ray8266
theorem signs8266 : ∀ j, Signs p8266 (bank8266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8267 := params 10
abbrev ray8267 := rays 10
def bank8267 : Fin 2 → Cell := twoBank p8267 ray8267
theorem signs8267 : ∀ j, Signs p8267 (bank8267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8268 := params 11
abbrev ray8268 := rays 11
def bank8268 : Fin 2 → Cell := twoBank p8268 ray8268
theorem signs8268 : ∀ j, Signs p8268 (bank8268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8269 := params 12
abbrev ray8269 := rays 12
def bank8269 : Fin 2 → Cell := twoBank p8269 ray8269
theorem signs8269 : ∀ j, Signs p8269 (bank8269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8270 := params 13
abbrev ray8270 := rays 13
def bank8270 : Fin 2 → Cell := twoBank p8270 ray8270
theorem signs8270 : ∀ j, Signs p8270 (bank8270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8271 := params 14
abbrev ray8271 := rays 14
def bank8271 : Fin 2 → Cell := twoBank p8271 ray8271
theorem signs8271 : ∀ j, Signs p8271 (bank8271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8272 := params 15
abbrev ray8272 := rays 15
def bank8272 : Fin 2 → Cell := twoBank p8272 ray8272
theorem signs8272 : ∀ j, Signs p8272 (bank8272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8273 := params 16
abbrev ray8273 := rays 16
def bank8273 : Fin 2 → Cell := twoBank p8273 ray8273
theorem signs8273 : ∀ j, Signs p8273 (bank8273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8274 := params 17
abbrev ray8274 := rays 17
def bank8274 : Fin 2 → Cell := twoBank p8274 ray8274
theorem signs8274 : ∀ j, Signs p8274 (bank8274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8275 := params 18
abbrev ray8275 := rays 18
def bank8275 : Fin 2 → Cell := twoBank p8275 ray8275
theorem signs8275 : ∀ j, Signs p8275 (bank8275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8276 := params 19
abbrev ray8276 := rays 19
def bank8276 : Fin 2 → Cell := twoBank p8276 ray8276
theorem signs8276 : ∀ j, Signs p8276 (bank8276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8277 := params 20
abbrev ray8277 := rays 20
def bank8277 : Fin 2 → Cell := twoBank p8277 ray8277
theorem signs8277 : ∀ j, Signs p8277 (bank8277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8278 := params 21
abbrev ray8278 := rays 21
def bank8278 : Fin 2 → Cell := twoBank p8278 ray8278
theorem signs8278 : ∀ j, Signs p8278 (bank8278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8279 := params 22
abbrev ray8279 := rays 22
def bank8279 : Fin 2 → Cell := twoBank p8279 ray8279
theorem signs8279 : ∀ j, Signs p8279 (bank8279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8280 := params 23
abbrev ray8280 := rays 23
def bank8280 : Fin 2 → Cell := twoBank p8280 ray8280
theorem signs8280 : ∀ j, Signs p8280 (bank8280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8281 := params 24
abbrev ray8281 := rays 24
def bank8281 : Fin 2 → Cell := twoBank p8281 ray8281
theorem signs8281 : ∀ j, Signs p8281 (bank8281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8282 := params 25
abbrev ray8282 := rays 25
def bank8282 : Fin 2 → Cell := twoBank p8282 ray8282
theorem signs8282 : ∀ j, Signs p8282 (bank8282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8283 := params 26
abbrev ray8283 := rays 26
def bank8283 : Fin 2 → Cell := twoBank p8283 ray8283
theorem signs8283 : ∀ j, Signs p8283 (bank8283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8284 := params 27
abbrev ray8284 := rays 27
def bank8284 : Fin 2 → Cell := twoBank p8284 ray8284
theorem signs8284 : ∀ j, Signs p8284 (bank8284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8285 := params 28
abbrev ray8285 := rays 28
def bank8285 : Fin 2 → Cell := twoBank p8285 ray8285
theorem signs8285 : ∀ j, Signs p8285 (bank8285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8286 := params 29
abbrev ray8286 := rays 29
def bank8286 : Fin 2 → Cell := twoBank p8286 ray8286
theorem signs8286 : ∀ j, Signs p8286 (bank8286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8287 := params 30
abbrev ray8287 := rays 30
def bank8287 : Fin 2 → Cell := twoBank p8287 ray8287
theorem signs8287 : ∀ j, Signs p8287 (bank8287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8288 := params 31
abbrev ray8288 := rays 31
def bank8288 : Fin 2 → Cell := twoBank p8288 ray8288
theorem signs8288 : ∀ j, Signs p8288 (bank8288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08257_08288
