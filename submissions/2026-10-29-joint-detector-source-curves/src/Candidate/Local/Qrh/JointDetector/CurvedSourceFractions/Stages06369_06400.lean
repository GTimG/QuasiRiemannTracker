/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06369_06400
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98662258254662,98661969714950,98661681152394,98661392566994,98661103958752,98660815327668,98660526673743,98660237996978,98659949297374,98659660574932,98659371829652,98659083061536,98658794270584,98658505456797,98658216620176,98657927760722,98657638878436,98657349973318,98657061045369,98656772094591,98656483120984,98656194124548,98655905105285,98655616063196,98655326998281,98655037910541,98654748799977,98654459666590,98654170510381,98653881331351,98653592129500,98653302904830,98653013657341]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6368+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6369 := params 0
abbrev ray6369 := rays 0
def bank6369 : Fin 2 → Cell := twoBank p6369 ray6369
theorem signs6369 : ∀ j, Signs p6369 (bank6369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6370 := params 1
abbrev ray6370 := rays 1
def bank6370 : Fin 2 → Cell := twoBank p6370 ray6370
theorem signs6370 : ∀ j, Signs p6370 (bank6370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6371 := params 2
abbrev ray6371 := rays 2
def bank6371 : Fin 2 → Cell := twoBank p6371 ray6371
theorem signs6371 : ∀ j, Signs p6371 (bank6371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6372 := params 3
abbrev ray6372 := rays 3
def bank6372 : Fin 2 → Cell := twoBank p6372 ray6372
theorem signs6372 : ∀ j, Signs p6372 (bank6372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6373 := params 4
abbrev ray6373 := rays 4
def bank6373 : Fin 2 → Cell := twoBank p6373 ray6373
theorem signs6373 : ∀ j, Signs p6373 (bank6373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6374 := params 5
abbrev ray6374 := rays 5
def bank6374 : Fin 2 → Cell := twoBank p6374 ray6374
theorem signs6374 : ∀ j, Signs p6374 (bank6374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6375 := params 6
abbrev ray6375 := rays 6
def bank6375 : Fin 2 → Cell := twoBank p6375 ray6375
theorem signs6375 : ∀ j, Signs p6375 (bank6375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6376 := params 7
abbrev ray6376 := rays 7
def bank6376 : Fin 2 → Cell := twoBank p6376 ray6376
theorem signs6376 : ∀ j, Signs p6376 (bank6376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6377 := params 8
abbrev ray6377 := rays 8
def bank6377 : Fin 2 → Cell := twoBank p6377 ray6377
theorem signs6377 : ∀ j, Signs p6377 (bank6377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6378 := params 9
abbrev ray6378 := rays 9
def bank6378 : Fin 2 → Cell := twoBank p6378 ray6378
theorem signs6378 : ∀ j, Signs p6378 (bank6378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6379 := params 10
abbrev ray6379 := rays 10
def bank6379 : Fin 2 → Cell := twoBank p6379 ray6379
theorem signs6379 : ∀ j, Signs p6379 (bank6379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6380 := params 11
abbrev ray6380 := rays 11
def bank6380 : Fin 2 → Cell := twoBank p6380 ray6380
theorem signs6380 : ∀ j, Signs p6380 (bank6380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6381 := params 12
abbrev ray6381 := rays 12
def bank6381 : Fin 2 → Cell := twoBank p6381 ray6381
theorem signs6381 : ∀ j, Signs p6381 (bank6381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6382 := params 13
abbrev ray6382 := rays 13
def bank6382 : Fin 2 → Cell := twoBank p6382 ray6382
theorem signs6382 : ∀ j, Signs p6382 (bank6382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6383 := params 14
abbrev ray6383 := rays 14
def bank6383 : Fin 2 → Cell := twoBank p6383 ray6383
theorem signs6383 : ∀ j, Signs p6383 (bank6383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6384 := params 15
abbrev ray6384 := rays 15
def bank6384 : Fin 2 → Cell := twoBank p6384 ray6384
theorem signs6384 : ∀ j, Signs p6384 (bank6384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6385 := params 16
abbrev ray6385 := rays 16
def bank6385 : Fin 2 → Cell := twoBank p6385 ray6385
theorem signs6385 : ∀ j, Signs p6385 (bank6385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6386 := params 17
abbrev ray6386 := rays 17
def bank6386 : Fin 2 → Cell := twoBank p6386 ray6386
theorem signs6386 : ∀ j, Signs p6386 (bank6386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6387 := params 18
abbrev ray6387 := rays 18
def bank6387 : Fin 2 → Cell := twoBank p6387 ray6387
theorem signs6387 : ∀ j, Signs p6387 (bank6387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6388 := params 19
abbrev ray6388 := rays 19
def bank6388 : Fin 2 → Cell := twoBank p6388 ray6388
theorem signs6388 : ∀ j, Signs p6388 (bank6388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6389 := params 20
abbrev ray6389 := rays 20
def bank6389 : Fin 2 → Cell := twoBank p6389 ray6389
theorem signs6389 : ∀ j, Signs p6389 (bank6389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6390 := params 21
abbrev ray6390 := rays 21
def bank6390 : Fin 2 → Cell := twoBank p6390 ray6390
theorem signs6390 : ∀ j, Signs p6390 (bank6390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6391 := params 22
abbrev ray6391 := rays 22
def bank6391 : Fin 2 → Cell := twoBank p6391 ray6391
theorem signs6391 : ∀ j, Signs p6391 (bank6391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6392 := params 23
abbrev ray6392 := rays 23
def bank6392 : Fin 2 → Cell := twoBank p6392 ray6392
theorem signs6392 : ∀ j, Signs p6392 (bank6392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6393 := params 24
abbrev ray6393 := rays 24
def bank6393 : Fin 2 → Cell := twoBank p6393 ray6393
theorem signs6393 : ∀ j, Signs p6393 (bank6393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6394 := params 25
abbrev ray6394 := rays 25
def bank6394 : Fin 2 → Cell := twoBank p6394 ray6394
theorem signs6394 : ∀ j, Signs p6394 (bank6394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6395 := params 26
abbrev ray6395 := rays 26
def bank6395 : Fin 2 → Cell := twoBank p6395 ray6395
theorem signs6395 : ∀ j, Signs p6395 (bank6395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6396 := params 27
abbrev ray6396 := rays 27
def bank6396 : Fin 2 → Cell := twoBank p6396 ray6396
theorem signs6396 : ∀ j, Signs p6396 (bank6396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6397 := params 28
abbrev ray6397 := rays 28
def bank6397 : Fin 2 → Cell := twoBank p6397 ray6397
theorem signs6397 : ∀ j, Signs p6397 (bank6397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6398 := params 29
abbrev ray6398 := rays 29
def bank6398 : Fin 2 → Cell := twoBank p6398 ray6398
theorem signs6398 : ∀ j, Signs p6398 (bank6398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6399 := params 30
abbrev ray6399 := rays 30
def bank6399 : Fin 2 → Cell := twoBank p6399 ray6399
theorem signs6399 : ∀ j, Signs p6399 (bank6399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6400 := params 31
abbrev ray6400 := rays 31
def bank6400 : Fin 2 → Cell := twoBank p6400 ray6400
theorem signs6400 : ∀ j, Signs p6400 (bank6400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06369_06400
