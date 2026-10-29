/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12353_12384
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96552312412272,96551899337779,96551486244079,96551073131173,96550659999061,96550246847744,96549833677222,96549420487495,96549007278564,96548594050429,96548180803091,96547767536550,96547354250807,96546940945862,96546527621715,96546114278367,96545700915818,96545287534068,96544874133118,96544460712969,96544047273620,96543633815073,96543220337327,96542806840383,96542393324242,96541979788904,96541566234369,96541152660638,96540739067711,96540325455588,96539911824270,96539498173757,96539084504050]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12352+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12353 := params 0
abbrev ray12353 := rays 0
def bank12353 : Fin 2 → Cell := twoBank p12353 ray12353
theorem signs12353 : ∀ j, Signs p12353 (bank12353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12354 := params 1
abbrev ray12354 := rays 1
def bank12354 : Fin 2 → Cell := twoBank p12354 ray12354
theorem signs12354 : ∀ j, Signs p12354 (bank12354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12355 := params 2
abbrev ray12355 := rays 2
def bank12355 : Fin 2 → Cell := twoBank p12355 ray12355
theorem signs12355 : ∀ j, Signs p12355 (bank12355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12356 := params 3
abbrev ray12356 := rays 3
def bank12356 : Fin 2 → Cell := twoBank p12356 ray12356
theorem signs12356 : ∀ j, Signs p12356 (bank12356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12357 := params 4
abbrev ray12357 := rays 4
def bank12357 : Fin 2 → Cell := twoBank p12357 ray12357
theorem signs12357 : ∀ j, Signs p12357 (bank12357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12358 := params 5
abbrev ray12358 := rays 5
def bank12358 : Fin 2 → Cell := twoBank p12358 ray12358
theorem signs12358 : ∀ j, Signs p12358 (bank12358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12359 := params 6
abbrev ray12359 := rays 6
def bank12359 : Fin 2 → Cell := twoBank p12359 ray12359
theorem signs12359 : ∀ j, Signs p12359 (bank12359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12360 := params 7
abbrev ray12360 := rays 7
def bank12360 : Fin 2 → Cell := twoBank p12360 ray12360
theorem signs12360 : ∀ j, Signs p12360 (bank12360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12361 := params 8
abbrev ray12361 := rays 8
def bank12361 : Fin 2 → Cell := twoBank p12361 ray12361
theorem signs12361 : ∀ j, Signs p12361 (bank12361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12362 := params 9
abbrev ray12362 := rays 9
def bank12362 : Fin 2 → Cell := twoBank p12362 ray12362
theorem signs12362 : ∀ j, Signs p12362 (bank12362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12363 := params 10
abbrev ray12363 := rays 10
def bank12363 : Fin 2 → Cell := twoBank p12363 ray12363
theorem signs12363 : ∀ j, Signs p12363 (bank12363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12364 := params 11
abbrev ray12364 := rays 11
def bank12364 : Fin 2 → Cell := twoBank p12364 ray12364
theorem signs12364 : ∀ j, Signs p12364 (bank12364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12365 := params 12
abbrev ray12365 := rays 12
def bank12365 : Fin 2 → Cell := twoBank p12365 ray12365
theorem signs12365 : ∀ j, Signs p12365 (bank12365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12366 := params 13
abbrev ray12366 := rays 13
def bank12366 : Fin 2 → Cell := twoBank p12366 ray12366
theorem signs12366 : ∀ j, Signs p12366 (bank12366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12367 := params 14
abbrev ray12367 := rays 14
def bank12367 : Fin 2 → Cell := twoBank p12367 ray12367
theorem signs12367 : ∀ j, Signs p12367 (bank12367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12368 := params 15
abbrev ray12368 := rays 15
def bank12368 : Fin 2 → Cell := twoBank p12368 ray12368
theorem signs12368 : ∀ j, Signs p12368 (bank12368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12369 := params 16
abbrev ray12369 := rays 16
def bank12369 : Fin 2 → Cell := twoBank p12369 ray12369
theorem signs12369 : ∀ j, Signs p12369 (bank12369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12370 := params 17
abbrev ray12370 := rays 17
def bank12370 : Fin 2 → Cell := twoBank p12370 ray12370
theorem signs12370 : ∀ j, Signs p12370 (bank12370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12371 := params 18
abbrev ray12371 := rays 18
def bank12371 : Fin 2 → Cell := twoBank p12371 ray12371
theorem signs12371 : ∀ j, Signs p12371 (bank12371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12372 := params 19
abbrev ray12372 := rays 19
def bank12372 : Fin 2 → Cell := twoBank p12372 ray12372
theorem signs12372 : ∀ j, Signs p12372 (bank12372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12373 := params 20
abbrev ray12373 := rays 20
def bank12373 : Fin 2 → Cell := twoBank p12373 ray12373
theorem signs12373 : ∀ j, Signs p12373 (bank12373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12374 := params 21
abbrev ray12374 := rays 21
def bank12374 : Fin 2 → Cell := twoBank p12374 ray12374
theorem signs12374 : ∀ j, Signs p12374 (bank12374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12375 := params 22
abbrev ray12375 := rays 22
def bank12375 : Fin 2 → Cell := twoBank p12375 ray12375
theorem signs12375 : ∀ j, Signs p12375 (bank12375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12376 := params 23
abbrev ray12376 := rays 23
def bank12376 : Fin 2 → Cell := twoBank p12376 ray12376
theorem signs12376 : ∀ j, Signs p12376 (bank12376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12377 := params 24
abbrev ray12377 := rays 24
def bank12377 : Fin 2 → Cell := twoBank p12377 ray12377
theorem signs12377 : ∀ j, Signs p12377 (bank12377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12378 := params 25
abbrev ray12378 := rays 25
def bank12378 : Fin 2 → Cell := twoBank p12378 ray12378
theorem signs12378 : ∀ j, Signs p12378 (bank12378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12379 := params 26
abbrev ray12379 := rays 26
def bank12379 : Fin 2 → Cell := twoBank p12379 ray12379
theorem signs12379 : ∀ j, Signs p12379 (bank12379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12380 := params 27
abbrev ray12380 := rays 27
def bank12380 : Fin 2 → Cell := twoBank p12380 ray12380
theorem signs12380 : ∀ j, Signs p12380 (bank12380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12381 := params 28
abbrev ray12381 := rays 28
def bank12381 : Fin 2 → Cell := twoBank p12381 ray12381
theorem signs12381 : ∀ j, Signs p12381 (bank12381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12382 := params 29
abbrev ray12382 := rays 29
def bank12382 : Fin 2 → Cell := twoBank p12382 ray12382
theorem signs12382 : ∀ j, Signs p12382 (bank12382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12383 := params 30
abbrev ray12383 := rays 30
def bank12383 : Fin 2 → Cell := twoBank p12383 ray12383
theorem signs12383 : ∀ j, Signs p12383 (bank12383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12384 := params 31
abbrev ray12384 := rays 31
def bank12384 : Fin 2 → Cell := twoBank p12384 ray12384
theorem signs12384 : ∀ j, Signs p12384 (bank12384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12353_12384
