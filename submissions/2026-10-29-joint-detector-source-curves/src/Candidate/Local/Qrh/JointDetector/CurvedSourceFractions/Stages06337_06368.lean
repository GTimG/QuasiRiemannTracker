/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06337_06368
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98671479458629,98671191650380,98670903819259,98670615965268,98670328088407,98670040188677,98669752266079,98669464320614,98669176352283,98668888361086,98668600347025,98668312310100,98668024250312,98667736167662,98667448062151,98667159933780,98666871782549,98666583608460,98666295411513,98666007191709,98665718949049,98665430683534,98665142395164,98664854083941,98664565749865,98664277392937,98663989013158,98663700610529,98663412185051,98663123736724,98662835265550,98662546771529,98662258254662]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6336+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6337 := params 0
abbrev ray6337 := rays 0
def bank6337 : Fin 2 → Cell := twoBank p6337 ray6337
theorem signs6337 : ∀ j, Signs p6337 (bank6337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6338 := params 1
abbrev ray6338 := rays 1
def bank6338 : Fin 2 → Cell := twoBank p6338 ray6338
theorem signs6338 : ∀ j, Signs p6338 (bank6338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6339 := params 2
abbrev ray6339 := rays 2
def bank6339 : Fin 2 → Cell := twoBank p6339 ray6339
theorem signs6339 : ∀ j, Signs p6339 (bank6339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6340 := params 3
abbrev ray6340 := rays 3
def bank6340 : Fin 2 → Cell := twoBank p6340 ray6340
theorem signs6340 : ∀ j, Signs p6340 (bank6340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6341 := params 4
abbrev ray6341 := rays 4
def bank6341 : Fin 2 → Cell := twoBank p6341 ray6341
theorem signs6341 : ∀ j, Signs p6341 (bank6341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6342 := params 5
abbrev ray6342 := rays 5
def bank6342 : Fin 2 → Cell := twoBank p6342 ray6342
theorem signs6342 : ∀ j, Signs p6342 (bank6342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6343 := params 6
abbrev ray6343 := rays 6
def bank6343 : Fin 2 → Cell := twoBank p6343 ray6343
theorem signs6343 : ∀ j, Signs p6343 (bank6343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6344 := params 7
abbrev ray6344 := rays 7
def bank6344 : Fin 2 → Cell := twoBank p6344 ray6344
theorem signs6344 : ∀ j, Signs p6344 (bank6344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6345 := params 8
abbrev ray6345 := rays 8
def bank6345 : Fin 2 → Cell := twoBank p6345 ray6345
theorem signs6345 : ∀ j, Signs p6345 (bank6345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6346 := params 9
abbrev ray6346 := rays 9
def bank6346 : Fin 2 → Cell := twoBank p6346 ray6346
theorem signs6346 : ∀ j, Signs p6346 (bank6346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6347 := params 10
abbrev ray6347 := rays 10
def bank6347 : Fin 2 → Cell := twoBank p6347 ray6347
theorem signs6347 : ∀ j, Signs p6347 (bank6347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6348 := params 11
abbrev ray6348 := rays 11
def bank6348 : Fin 2 → Cell := twoBank p6348 ray6348
theorem signs6348 : ∀ j, Signs p6348 (bank6348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6349 := params 12
abbrev ray6349 := rays 12
def bank6349 : Fin 2 → Cell := twoBank p6349 ray6349
theorem signs6349 : ∀ j, Signs p6349 (bank6349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6350 := params 13
abbrev ray6350 := rays 13
def bank6350 : Fin 2 → Cell := twoBank p6350 ray6350
theorem signs6350 : ∀ j, Signs p6350 (bank6350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6351 := params 14
abbrev ray6351 := rays 14
def bank6351 : Fin 2 → Cell := twoBank p6351 ray6351
theorem signs6351 : ∀ j, Signs p6351 (bank6351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6352 := params 15
abbrev ray6352 := rays 15
def bank6352 : Fin 2 → Cell := twoBank p6352 ray6352
theorem signs6352 : ∀ j, Signs p6352 (bank6352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6353 := params 16
abbrev ray6353 := rays 16
def bank6353 : Fin 2 → Cell := twoBank p6353 ray6353
theorem signs6353 : ∀ j, Signs p6353 (bank6353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6354 := params 17
abbrev ray6354 := rays 17
def bank6354 : Fin 2 → Cell := twoBank p6354 ray6354
theorem signs6354 : ∀ j, Signs p6354 (bank6354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6355 := params 18
abbrev ray6355 := rays 18
def bank6355 : Fin 2 → Cell := twoBank p6355 ray6355
theorem signs6355 : ∀ j, Signs p6355 (bank6355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6356 := params 19
abbrev ray6356 := rays 19
def bank6356 : Fin 2 → Cell := twoBank p6356 ray6356
theorem signs6356 : ∀ j, Signs p6356 (bank6356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6357 := params 20
abbrev ray6357 := rays 20
def bank6357 : Fin 2 → Cell := twoBank p6357 ray6357
theorem signs6357 : ∀ j, Signs p6357 (bank6357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6358 := params 21
abbrev ray6358 := rays 21
def bank6358 : Fin 2 → Cell := twoBank p6358 ray6358
theorem signs6358 : ∀ j, Signs p6358 (bank6358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6359 := params 22
abbrev ray6359 := rays 22
def bank6359 : Fin 2 → Cell := twoBank p6359 ray6359
theorem signs6359 : ∀ j, Signs p6359 (bank6359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6360 := params 23
abbrev ray6360 := rays 23
def bank6360 : Fin 2 → Cell := twoBank p6360 ray6360
theorem signs6360 : ∀ j, Signs p6360 (bank6360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6361 := params 24
abbrev ray6361 := rays 24
def bank6361 : Fin 2 → Cell := twoBank p6361 ray6361
theorem signs6361 : ∀ j, Signs p6361 (bank6361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6362 := params 25
abbrev ray6362 := rays 25
def bank6362 : Fin 2 → Cell := twoBank p6362 ray6362
theorem signs6362 : ∀ j, Signs p6362 (bank6362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6363 := params 26
abbrev ray6363 := rays 26
def bank6363 : Fin 2 → Cell := twoBank p6363 ray6363
theorem signs6363 : ∀ j, Signs p6363 (bank6363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6364 := params 27
abbrev ray6364 := rays 27
def bank6364 : Fin 2 → Cell := twoBank p6364 ray6364
theorem signs6364 : ∀ j, Signs p6364 (bank6364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6365 := params 28
abbrev ray6365 := rays 28
def bank6365 : Fin 2 → Cell := twoBank p6365 ray6365
theorem signs6365 : ∀ j, Signs p6365 (bank6365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6366 := params 29
abbrev ray6366 := rays 29
def bank6366 : Fin 2 → Cell := twoBank p6366 ray6366
theorem signs6366 : ∀ j, Signs p6366 (bank6366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6367 := params 30
abbrev ray6367 := rays 30
def bank6367 : Fin 2 → Cell := twoBank p6367 ray6367
theorem signs6367 : ∀ j, Signs p6367 (bank6367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6368 := params 31
abbrev ray6368 := rays 31
def bank6368 : Fin 2 → Cell := twoBank p6368 ray6368
theorem signs6368 : ∀ j, Signs p6368 (bank6368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06337_06368
