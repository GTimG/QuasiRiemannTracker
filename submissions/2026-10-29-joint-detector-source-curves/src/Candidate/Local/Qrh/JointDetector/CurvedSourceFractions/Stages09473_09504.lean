/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09473_09504
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97660479233227,97660123413871,97659767573877,97659411713245,97659055831976,97658699930070,97658344007528,97657988064351,97657632100539,97657276116093,97656920111013,97656564085300,97656208038955,97655851971978,97655495884370,97655139776131,97654783647262,97654427497763,97654071327636,97653715136880,97653358925496,97653002693485,97652646440848,97652290167585,97651933873696,97651577559183,97651221224045,97650864868284,97650508491900,97650152094893,97649795677264,97649439239014,97649082780143]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9472+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9473 := params 0
abbrev ray9473 := rays 0
def bank9473 : Fin 2 → Cell := twoBank p9473 ray9473
theorem signs9473 : ∀ j, Signs p9473 (bank9473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9474 := params 1
abbrev ray9474 := rays 1
def bank9474 : Fin 2 → Cell := twoBank p9474 ray9474
theorem signs9474 : ∀ j, Signs p9474 (bank9474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9475 := params 2
abbrev ray9475 := rays 2
def bank9475 : Fin 2 → Cell := twoBank p9475 ray9475
theorem signs9475 : ∀ j, Signs p9475 (bank9475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9476 := params 3
abbrev ray9476 := rays 3
def bank9476 : Fin 2 → Cell := twoBank p9476 ray9476
theorem signs9476 : ∀ j, Signs p9476 (bank9476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9477 := params 4
abbrev ray9477 := rays 4
def bank9477 : Fin 2 → Cell := twoBank p9477 ray9477
theorem signs9477 : ∀ j, Signs p9477 (bank9477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9478 := params 5
abbrev ray9478 := rays 5
def bank9478 : Fin 2 → Cell := twoBank p9478 ray9478
theorem signs9478 : ∀ j, Signs p9478 (bank9478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9479 := params 6
abbrev ray9479 := rays 6
def bank9479 : Fin 2 → Cell := twoBank p9479 ray9479
theorem signs9479 : ∀ j, Signs p9479 (bank9479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9480 := params 7
abbrev ray9480 := rays 7
def bank9480 : Fin 2 → Cell := twoBank p9480 ray9480
theorem signs9480 : ∀ j, Signs p9480 (bank9480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9481 := params 8
abbrev ray9481 := rays 8
def bank9481 : Fin 2 → Cell := twoBank p9481 ray9481
theorem signs9481 : ∀ j, Signs p9481 (bank9481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9482 := params 9
abbrev ray9482 := rays 9
def bank9482 : Fin 2 → Cell := twoBank p9482 ray9482
theorem signs9482 : ∀ j, Signs p9482 (bank9482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9483 := params 10
abbrev ray9483 := rays 10
def bank9483 : Fin 2 → Cell := twoBank p9483 ray9483
theorem signs9483 : ∀ j, Signs p9483 (bank9483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9484 := params 11
abbrev ray9484 := rays 11
def bank9484 : Fin 2 → Cell := twoBank p9484 ray9484
theorem signs9484 : ∀ j, Signs p9484 (bank9484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9485 := params 12
abbrev ray9485 := rays 12
def bank9485 : Fin 2 → Cell := twoBank p9485 ray9485
theorem signs9485 : ∀ j, Signs p9485 (bank9485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9486 := params 13
abbrev ray9486 := rays 13
def bank9486 : Fin 2 → Cell := twoBank p9486 ray9486
theorem signs9486 : ∀ j, Signs p9486 (bank9486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9487 := params 14
abbrev ray9487 := rays 14
def bank9487 : Fin 2 → Cell := twoBank p9487 ray9487
theorem signs9487 : ∀ j, Signs p9487 (bank9487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9488 := params 15
abbrev ray9488 := rays 15
def bank9488 : Fin 2 → Cell := twoBank p9488 ray9488
theorem signs9488 : ∀ j, Signs p9488 (bank9488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9489 := params 16
abbrev ray9489 := rays 16
def bank9489 : Fin 2 → Cell := twoBank p9489 ray9489
theorem signs9489 : ∀ j, Signs p9489 (bank9489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9490 := params 17
abbrev ray9490 := rays 17
def bank9490 : Fin 2 → Cell := twoBank p9490 ray9490
theorem signs9490 : ∀ j, Signs p9490 (bank9490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9491 := params 18
abbrev ray9491 := rays 18
def bank9491 : Fin 2 → Cell := twoBank p9491 ray9491
theorem signs9491 : ∀ j, Signs p9491 (bank9491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9492 := params 19
abbrev ray9492 := rays 19
def bank9492 : Fin 2 → Cell := twoBank p9492 ray9492
theorem signs9492 : ∀ j, Signs p9492 (bank9492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9493 := params 20
abbrev ray9493 := rays 20
def bank9493 : Fin 2 → Cell := twoBank p9493 ray9493
theorem signs9493 : ∀ j, Signs p9493 (bank9493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9494 := params 21
abbrev ray9494 := rays 21
def bank9494 : Fin 2 → Cell := twoBank p9494 ray9494
theorem signs9494 : ∀ j, Signs p9494 (bank9494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9495 := params 22
abbrev ray9495 := rays 22
def bank9495 : Fin 2 → Cell := twoBank p9495 ray9495
theorem signs9495 : ∀ j, Signs p9495 (bank9495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9496 := params 23
abbrev ray9496 := rays 23
def bank9496 : Fin 2 → Cell := twoBank p9496 ray9496
theorem signs9496 : ∀ j, Signs p9496 (bank9496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9497 := params 24
abbrev ray9497 := rays 24
def bank9497 : Fin 2 → Cell := twoBank p9497 ray9497
theorem signs9497 : ∀ j, Signs p9497 (bank9497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9498 := params 25
abbrev ray9498 := rays 25
def bank9498 : Fin 2 → Cell := twoBank p9498 ray9498
theorem signs9498 : ∀ j, Signs p9498 (bank9498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9499 := params 26
abbrev ray9499 := rays 26
def bank9499 : Fin 2 → Cell := twoBank p9499 ray9499
theorem signs9499 : ∀ j, Signs p9499 (bank9499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9500 := params 27
abbrev ray9500 := rays 27
def bank9500 : Fin 2 → Cell := twoBank p9500 ray9500
theorem signs9500 : ∀ j, Signs p9500 (bank9500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9501 := params 28
abbrev ray9501 := rays 28
def bank9501 : Fin 2 → Cell := twoBank p9501 ray9501
theorem signs9501 : ∀ j, Signs p9501 (bank9501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9502 := params 29
abbrev ray9502 := rays 29
def bank9502 : Fin 2 → Cell := twoBank p9502 ray9502
theorem signs9502 : ∀ j, Signs p9502 (bank9502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9503 := params 30
abbrev ray9503 := rays 30
def bank9503 : Fin 2 → Cell := twoBank p9503 ray9503
theorem signs9503 : ∀ j, Signs p9503 (bank9503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9504 := params 31
abbrev ray9504 := rays 31
def bank9504 : Fin 2 → Cell := twoBank p9504 ray9504
theorem signs9504 : ∀ j, Signs p9504 (bank9504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09473_09504
