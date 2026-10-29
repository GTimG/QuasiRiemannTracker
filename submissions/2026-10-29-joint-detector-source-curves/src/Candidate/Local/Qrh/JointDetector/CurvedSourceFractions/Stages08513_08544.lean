/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08513_08544
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97992456060768,97992120336620,97991784591235,97991448824613,97991113036755,97990777227662,97990441397334,97990105545772,97989769672977,97989433778949,97989097863689,97988761927198,97988425969476,97988089990524,97987753990343,97987417968933,97987081926295,97986745862429,97986409777337,97986073671019,97985737543475,97985401394706,97985065224713,97984729033497,97984392821058,97984056587397,97983720332514,97983384056410,97983047759086,97982711440543,97982375100781,97982038739801,97981702357603]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8512+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8513 := params 0
abbrev ray8513 := rays 0
def bank8513 : Fin 2 → Cell := twoBank p8513 ray8513
theorem signs8513 : ∀ j, Signs p8513 (bank8513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8514 := params 1
abbrev ray8514 := rays 1
def bank8514 : Fin 2 → Cell := twoBank p8514 ray8514
theorem signs8514 : ∀ j, Signs p8514 (bank8514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8515 := params 2
abbrev ray8515 := rays 2
def bank8515 : Fin 2 → Cell := twoBank p8515 ray8515
theorem signs8515 : ∀ j, Signs p8515 (bank8515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8516 := params 3
abbrev ray8516 := rays 3
def bank8516 : Fin 2 → Cell := twoBank p8516 ray8516
theorem signs8516 : ∀ j, Signs p8516 (bank8516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8517 := params 4
abbrev ray8517 := rays 4
def bank8517 : Fin 2 → Cell := twoBank p8517 ray8517
theorem signs8517 : ∀ j, Signs p8517 (bank8517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8518 := params 5
abbrev ray8518 := rays 5
def bank8518 : Fin 2 → Cell := twoBank p8518 ray8518
theorem signs8518 : ∀ j, Signs p8518 (bank8518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8519 := params 6
abbrev ray8519 := rays 6
def bank8519 : Fin 2 → Cell := twoBank p8519 ray8519
theorem signs8519 : ∀ j, Signs p8519 (bank8519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8520 := params 7
abbrev ray8520 := rays 7
def bank8520 : Fin 2 → Cell := twoBank p8520 ray8520
theorem signs8520 : ∀ j, Signs p8520 (bank8520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8521 := params 8
abbrev ray8521 := rays 8
def bank8521 : Fin 2 → Cell := twoBank p8521 ray8521
theorem signs8521 : ∀ j, Signs p8521 (bank8521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8522 := params 9
abbrev ray8522 := rays 9
def bank8522 : Fin 2 → Cell := twoBank p8522 ray8522
theorem signs8522 : ∀ j, Signs p8522 (bank8522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8523 := params 10
abbrev ray8523 := rays 10
def bank8523 : Fin 2 → Cell := twoBank p8523 ray8523
theorem signs8523 : ∀ j, Signs p8523 (bank8523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8524 := params 11
abbrev ray8524 := rays 11
def bank8524 : Fin 2 → Cell := twoBank p8524 ray8524
theorem signs8524 : ∀ j, Signs p8524 (bank8524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8525 := params 12
abbrev ray8525 := rays 12
def bank8525 : Fin 2 → Cell := twoBank p8525 ray8525
theorem signs8525 : ∀ j, Signs p8525 (bank8525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8526 := params 13
abbrev ray8526 := rays 13
def bank8526 : Fin 2 → Cell := twoBank p8526 ray8526
theorem signs8526 : ∀ j, Signs p8526 (bank8526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8527 := params 14
abbrev ray8527 := rays 14
def bank8527 : Fin 2 → Cell := twoBank p8527 ray8527
theorem signs8527 : ∀ j, Signs p8527 (bank8527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8528 := params 15
abbrev ray8528 := rays 15
def bank8528 : Fin 2 → Cell := twoBank p8528 ray8528
theorem signs8528 : ∀ j, Signs p8528 (bank8528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8529 := params 16
abbrev ray8529 := rays 16
def bank8529 : Fin 2 → Cell := twoBank p8529 ray8529
theorem signs8529 : ∀ j, Signs p8529 (bank8529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8530 := params 17
abbrev ray8530 := rays 17
def bank8530 : Fin 2 → Cell := twoBank p8530 ray8530
theorem signs8530 : ∀ j, Signs p8530 (bank8530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8531 := params 18
abbrev ray8531 := rays 18
def bank8531 : Fin 2 → Cell := twoBank p8531 ray8531
theorem signs8531 : ∀ j, Signs p8531 (bank8531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8532 := params 19
abbrev ray8532 := rays 19
def bank8532 : Fin 2 → Cell := twoBank p8532 ray8532
theorem signs8532 : ∀ j, Signs p8532 (bank8532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8533 := params 20
abbrev ray8533 := rays 20
def bank8533 : Fin 2 → Cell := twoBank p8533 ray8533
theorem signs8533 : ∀ j, Signs p8533 (bank8533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8534 := params 21
abbrev ray8534 := rays 21
def bank8534 : Fin 2 → Cell := twoBank p8534 ray8534
theorem signs8534 : ∀ j, Signs p8534 (bank8534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8535 := params 22
abbrev ray8535 := rays 22
def bank8535 : Fin 2 → Cell := twoBank p8535 ray8535
theorem signs8535 : ∀ j, Signs p8535 (bank8535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8536 := params 23
abbrev ray8536 := rays 23
def bank8536 : Fin 2 → Cell := twoBank p8536 ray8536
theorem signs8536 : ∀ j, Signs p8536 (bank8536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8537 := params 24
abbrev ray8537 := rays 24
def bank8537 : Fin 2 → Cell := twoBank p8537 ray8537
theorem signs8537 : ∀ j, Signs p8537 (bank8537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8538 := params 25
abbrev ray8538 := rays 25
def bank8538 : Fin 2 → Cell := twoBank p8538 ray8538
theorem signs8538 : ∀ j, Signs p8538 (bank8538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8539 := params 26
abbrev ray8539 := rays 26
def bank8539 : Fin 2 → Cell := twoBank p8539 ray8539
theorem signs8539 : ∀ j, Signs p8539 (bank8539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8540 := params 27
abbrev ray8540 := rays 27
def bank8540 : Fin 2 → Cell := twoBank p8540 ray8540
theorem signs8540 : ∀ j, Signs p8540 (bank8540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8541 := params 28
abbrev ray8541 := rays 28
def bank8541 : Fin 2 → Cell := twoBank p8541 ray8541
theorem signs8541 : ∀ j, Signs p8541 (bank8541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8542 := params 29
abbrev ray8542 := rays 29
def bank8542 : Fin 2 → Cell := twoBank p8542 ray8542
theorem signs8542 : ∀ j, Signs p8542 (bank8542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8543 := params 30
abbrev ray8543 := rays 30
def bank8543 : Fin 2 → Cell := twoBank p8543 ray8543
theorem signs8543 : ∀ j, Signs p8543 (bank8543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8544 := params 31
abbrev ray8544 := rays 31
def bank8544 : Fin 2 → Cell := twoBank p8544 ray8544
theorem signs8544 : ∀ j, Signs p8544 (bank8544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08513_08544
