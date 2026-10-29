/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10369_10400
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97333458522488,97333084439301,97332710335976,97332336212514,97331962068916,97331587905182,97331213721313,97330839517309,97330465293170,97330091048898,97329716784492,97329342499954,97328968195283,97328593870481,97328219525547,97327845160483,97327470775289,97327096369965,97326721944512,97326347498931,97325973033222,97325598547385,97325224041421,97324849515331,97324474969115,97324100402774,97323725816308,97323351209717,97322976583003,97322601936165,97322227269205,97321852582123,97321477874919]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10368+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10369 := params 0
abbrev ray10369 := rays 0
def bank10369 : Fin 2 → Cell := twoBank p10369 ray10369
theorem signs10369 : ∀ j, Signs p10369 (bank10369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10370 := params 1
abbrev ray10370 := rays 1
def bank10370 : Fin 2 → Cell := twoBank p10370 ray10370
theorem signs10370 : ∀ j, Signs p10370 (bank10370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10371 := params 2
abbrev ray10371 := rays 2
def bank10371 : Fin 2 → Cell := twoBank p10371 ray10371
theorem signs10371 : ∀ j, Signs p10371 (bank10371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10372 := params 3
abbrev ray10372 := rays 3
def bank10372 : Fin 2 → Cell := twoBank p10372 ray10372
theorem signs10372 : ∀ j, Signs p10372 (bank10372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10373 := params 4
abbrev ray10373 := rays 4
def bank10373 : Fin 2 → Cell := twoBank p10373 ray10373
theorem signs10373 : ∀ j, Signs p10373 (bank10373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10374 := params 5
abbrev ray10374 := rays 5
def bank10374 : Fin 2 → Cell := twoBank p10374 ray10374
theorem signs10374 : ∀ j, Signs p10374 (bank10374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10375 := params 6
abbrev ray10375 := rays 6
def bank10375 : Fin 2 → Cell := twoBank p10375 ray10375
theorem signs10375 : ∀ j, Signs p10375 (bank10375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10376 := params 7
abbrev ray10376 := rays 7
def bank10376 : Fin 2 → Cell := twoBank p10376 ray10376
theorem signs10376 : ∀ j, Signs p10376 (bank10376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10377 := params 8
abbrev ray10377 := rays 8
def bank10377 : Fin 2 → Cell := twoBank p10377 ray10377
theorem signs10377 : ∀ j, Signs p10377 (bank10377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10378 := params 9
abbrev ray10378 := rays 9
def bank10378 : Fin 2 → Cell := twoBank p10378 ray10378
theorem signs10378 : ∀ j, Signs p10378 (bank10378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10379 := params 10
abbrev ray10379 := rays 10
def bank10379 : Fin 2 → Cell := twoBank p10379 ray10379
theorem signs10379 : ∀ j, Signs p10379 (bank10379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10380 := params 11
abbrev ray10380 := rays 11
def bank10380 : Fin 2 → Cell := twoBank p10380 ray10380
theorem signs10380 : ∀ j, Signs p10380 (bank10380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10381 := params 12
abbrev ray10381 := rays 12
def bank10381 : Fin 2 → Cell := twoBank p10381 ray10381
theorem signs10381 : ∀ j, Signs p10381 (bank10381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10382 := params 13
abbrev ray10382 := rays 13
def bank10382 : Fin 2 → Cell := twoBank p10382 ray10382
theorem signs10382 : ∀ j, Signs p10382 (bank10382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10383 := params 14
abbrev ray10383 := rays 14
def bank10383 : Fin 2 → Cell := twoBank p10383 ray10383
theorem signs10383 : ∀ j, Signs p10383 (bank10383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10384 := params 15
abbrev ray10384 := rays 15
def bank10384 : Fin 2 → Cell := twoBank p10384 ray10384
theorem signs10384 : ∀ j, Signs p10384 (bank10384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10385 := params 16
abbrev ray10385 := rays 16
def bank10385 : Fin 2 → Cell := twoBank p10385 ray10385
theorem signs10385 : ∀ j, Signs p10385 (bank10385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10386 := params 17
abbrev ray10386 := rays 17
def bank10386 : Fin 2 → Cell := twoBank p10386 ray10386
theorem signs10386 : ∀ j, Signs p10386 (bank10386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10387 := params 18
abbrev ray10387 := rays 18
def bank10387 : Fin 2 → Cell := twoBank p10387 ray10387
theorem signs10387 : ∀ j, Signs p10387 (bank10387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10388 := params 19
abbrev ray10388 := rays 19
def bank10388 : Fin 2 → Cell := twoBank p10388 ray10388
theorem signs10388 : ∀ j, Signs p10388 (bank10388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10389 := params 20
abbrev ray10389 := rays 20
def bank10389 : Fin 2 → Cell := twoBank p10389 ray10389
theorem signs10389 : ∀ j, Signs p10389 (bank10389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10390 := params 21
abbrev ray10390 := rays 21
def bank10390 : Fin 2 → Cell := twoBank p10390 ray10390
theorem signs10390 : ∀ j, Signs p10390 (bank10390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10391 := params 22
abbrev ray10391 := rays 22
def bank10391 : Fin 2 → Cell := twoBank p10391 ray10391
theorem signs10391 : ∀ j, Signs p10391 (bank10391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10392 := params 23
abbrev ray10392 := rays 23
def bank10392 : Fin 2 → Cell := twoBank p10392 ray10392
theorem signs10392 : ∀ j, Signs p10392 (bank10392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10393 := params 24
abbrev ray10393 := rays 24
def bank10393 : Fin 2 → Cell := twoBank p10393 ray10393
theorem signs10393 : ∀ j, Signs p10393 (bank10393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10394 := params 25
abbrev ray10394 := rays 25
def bank10394 : Fin 2 → Cell := twoBank p10394 ray10394
theorem signs10394 : ∀ j, Signs p10394 (bank10394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10395 := params 26
abbrev ray10395 := rays 26
def bank10395 : Fin 2 → Cell := twoBank p10395 ray10395
theorem signs10395 : ∀ j, Signs p10395 (bank10395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10396 := params 27
abbrev ray10396 := rays 27
def bank10396 : Fin 2 → Cell := twoBank p10396 ray10396
theorem signs10396 : ∀ j, Signs p10396 (bank10396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10397 := params 28
abbrev ray10397 := rays 28
def bank10397 : Fin 2 → Cell := twoBank p10397 ray10397
theorem signs10397 : ∀ j, Signs p10397 (bank10397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10398 := params 29
abbrev ray10398 := rays 29
def bank10398 : Fin 2 → Cell := twoBank p10398 ray10398
theorem signs10398 : ∀ j, Signs p10398 (bank10398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10399 := params 30
abbrev ray10399 := rays 30
def bank10399 : Fin 2 → Cell := twoBank p10399 ray10399
theorem signs10399 : ∀ j, Signs p10399 (bank10399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10400 := params 31
abbrev ray10400 := rays 31
def bank10400 : Fin 2 → Cell := twoBank p10400 ray10400
theorem signs10400 : ∀ j, Signs p10400 (bank10400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10369_10400
