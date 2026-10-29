/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08481_08512
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98003188016257,98002852972051,98002517906587,98002182819865,98001847711886,98001512582650,98001177432159,98000842260413,98000507067412,98000171853157,97999836617649,97999501360889,97999166082877,97998830783614,97998495463100,97998160121336,97997824758323,97997489374062,97997153968553,97996818541797,97996483093794,97996147624545,97995812134051,97995476622312,97995141089329,97994805535103,97994469959635,97994134362925,97993798744973,97993463105781,97993127445349,97992791763678,97992456060768]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8480+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8481 := params 0
abbrev ray8481 := rays 0
def bank8481 : Fin 2 → Cell := twoBank p8481 ray8481
theorem signs8481 : ∀ j, Signs p8481 (bank8481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8482 := params 1
abbrev ray8482 := rays 1
def bank8482 : Fin 2 → Cell := twoBank p8482 ray8482
theorem signs8482 : ∀ j, Signs p8482 (bank8482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8483 := params 2
abbrev ray8483 := rays 2
def bank8483 : Fin 2 → Cell := twoBank p8483 ray8483
theorem signs8483 : ∀ j, Signs p8483 (bank8483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8484 := params 3
abbrev ray8484 := rays 3
def bank8484 : Fin 2 → Cell := twoBank p8484 ray8484
theorem signs8484 : ∀ j, Signs p8484 (bank8484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8485 := params 4
abbrev ray8485 := rays 4
def bank8485 : Fin 2 → Cell := twoBank p8485 ray8485
theorem signs8485 : ∀ j, Signs p8485 (bank8485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8486 := params 5
abbrev ray8486 := rays 5
def bank8486 : Fin 2 → Cell := twoBank p8486 ray8486
theorem signs8486 : ∀ j, Signs p8486 (bank8486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8487 := params 6
abbrev ray8487 := rays 6
def bank8487 : Fin 2 → Cell := twoBank p8487 ray8487
theorem signs8487 : ∀ j, Signs p8487 (bank8487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8488 := params 7
abbrev ray8488 := rays 7
def bank8488 : Fin 2 → Cell := twoBank p8488 ray8488
theorem signs8488 : ∀ j, Signs p8488 (bank8488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8489 := params 8
abbrev ray8489 := rays 8
def bank8489 : Fin 2 → Cell := twoBank p8489 ray8489
theorem signs8489 : ∀ j, Signs p8489 (bank8489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8490 := params 9
abbrev ray8490 := rays 9
def bank8490 : Fin 2 → Cell := twoBank p8490 ray8490
theorem signs8490 : ∀ j, Signs p8490 (bank8490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8491 := params 10
abbrev ray8491 := rays 10
def bank8491 : Fin 2 → Cell := twoBank p8491 ray8491
theorem signs8491 : ∀ j, Signs p8491 (bank8491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8492 := params 11
abbrev ray8492 := rays 11
def bank8492 : Fin 2 → Cell := twoBank p8492 ray8492
theorem signs8492 : ∀ j, Signs p8492 (bank8492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8493 := params 12
abbrev ray8493 := rays 12
def bank8493 : Fin 2 → Cell := twoBank p8493 ray8493
theorem signs8493 : ∀ j, Signs p8493 (bank8493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8494 := params 13
abbrev ray8494 := rays 13
def bank8494 : Fin 2 → Cell := twoBank p8494 ray8494
theorem signs8494 : ∀ j, Signs p8494 (bank8494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8495 := params 14
abbrev ray8495 := rays 14
def bank8495 : Fin 2 → Cell := twoBank p8495 ray8495
theorem signs8495 : ∀ j, Signs p8495 (bank8495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8496 := params 15
abbrev ray8496 := rays 15
def bank8496 : Fin 2 → Cell := twoBank p8496 ray8496
theorem signs8496 : ∀ j, Signs p8496 (bank8496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8497 := params 16
abbrev ray8497 := rays 16
def bank8497 : Fin 2 → Cell := twoBank p8497 ray8497
theorem signs8497 : ∀ j, Signs p8497 (bank8497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8498 := params 17
abbrev ray8498 := rays 17
def bank8498 : Fin 2 → Cell := twoBank p8498 ray8498
theorem signs8498 : ∀ j, Signs p8498 (bank8498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8499 := params 18
abbrev ray8499 := rays 18
def bank8499 : Fin 2 → Cell := twoBank p8499 ray8499
theorem signs8499 : ∀ j, Signs p8499 (bank8499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8500 := params 19
abbrev ray8500 := rays 19
def bank8500 : Fin 2 → Cell := twoBank p8500 ray8500
theorem signs8500 : ∀ j, Signs p8500 (bank8500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8501 := params 20
abbrev ray8501 := rays 20
def bank8501 : Fin 2 → Cell := twoBank p8501 ray8501
theorem signs8501 : ∀ j, Signs p8501 (bank8501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8502 := params 21
abbrev ray8502 := rays 21
def bank8502 : Fin 2 → Cell := twoBank p8502 ray8502
theorem signs8502 : ∀ j, Signs p8502 (bank8502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8503 := params 22
abbrev ray8503 := rays 22
def bank8503 : Fin 2 → Cell := twoBank p8503 ray8503
theorem signs8503 : ∀ j, Signs p8503 (bank8503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8504 := params 23
abbrev ray8504 := rays 23
def bank8504 : Fin 2 → Cell := twoBank p8504 ray8504
theorem signs8504 : ∀ j, Signs p8504 (bank8504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8505 := params 24
abbrev ray8505 := rays 24
def bank8505 : Fin 2 → Cell := twoBank p8505 ray8505
theorem signs8505 : ∀ j, Signs p8505 (bank8505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8506 := params 25
abbrev ray8506 := rays 25
def bank8506 : Fin 2 → Cell := twoBank p8506 ray8506
theorem signs8506 : ∀ j, Signs p8506 (bank8506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8507 := params 26
abbrev ray8507 := rays 26
def bank8507 : Fin 2 → Cell := twoBank p8507 ray8507
theorem signs8507 : ∀ j, Signs p8507 (bank8507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8508 := params 27
abbrev ray8508 := rays 27
def bank8508 : Fin 2 → Cell := twoBank p8508 ray8508
theorem signs8508 : ∀ j, Signs p8508 (bank8508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8509 := params 28
abbrev ray8509 := rays 28
def bank8509 : Fin 2 → Cell := twoBank p8509 ray8509
theorem signs8509 : ∀ j, Signs p8509 (bank8509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8510 := params 29
abbrev ray8510 := rays 29
def bank8510 : Fin 2 → Cell := twoBank p8510 ray8510
theorem signs8510 : ∀ j, Signs p8510 (bank8510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8511 := params 30
abbrev ray8511 := rays 30
def bank8511 : Fin 2 → Cell := twoBank p8511 ray8511
theorem signs8511 : ∀ j, Signs p8511 (bank8511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8512 := params 31
abbrev ray8512 := rays 31
def bank8512 : Fin 2 → Cell := twoBank p8512 ray8512
theorem signs8512 : ∀ j, Signs p8512 (bank8512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08481_08512
