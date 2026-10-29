/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12481_12512
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96499282905796,96498867376185,96498451827420,96498036259501,96497620672428,96497205066202,96496789440823,96496373796292,96495958132609,96495542449774,96495126747788,96494711026652,96494295286365,96493879526928,96493463748342,96493047950607,96492632133723,96492216297691,96491800442511,96491384568183,96490968674708,96490552762087,96490136830319,96489720879406,96489304909347,96488888920143,96488472911794,96488056884301,96487640837664,96487224771884,96486808686961,96486392582895,96485976459687]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12480+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12481 := params 0
abbrev ray12481 := rays 0
def bank12481 : Fin 2 → Cell := twoBank p12481 ray12481
theorem signs12481 : ∀ j, Signs p12481 (bank12481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12482 := params 1
abbrev ray12482 := rays 1
def bank12482 : Fin 2 → Cell := twoBank p12482 ray12482
theorem signs12482 : ∀ j, Signs p12482 (bank12482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12483 := params 2
abbrev ray12483 := rays 2
def bank12483 : Fin 2 → Cell := twoBank p12483 ray12483
theorem signs12483 : ∀ j, Signs p12483 (bank12483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12484 := params 3
abbrev ray12484 := rays 3
def bank12484 : Fin 2 → Cell := twoBank p12484 ray12484
theorem signs12484 : ∀ j, Signs p12484 (bank12484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12485 := params 4
abbrev ray12485 := rays 4
def bank12485 : Fin 2 → Cell := twoBank p12485 ray12485
theorem signs12485 : ∀ j, Signs p12485 (bank12485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12486 := params 5
abbrev ray12486 := rays 5
def bank12486 : Fin 2 → Cell := twoBank p12486 ray12486
theorem signs12486 : ∀ j, Signs p12486 (bank12486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12487 := params 6
abbrev ray12487 := rays 6
def bank12487 : Fin 2 → Cell := twoBank p12487 ray12487
theorem signs12487 : ∀ j, Signs p12487 (bank12487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12488 := params 7
abbrev ray12488 := rays 7
def bank12488 : Fin 2 → Cell := twoBank p12488 ray12488
theorem signs12488 : ∀ j, Signs p12488 (bank12488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12489 := params 8
abbrev ray12489 := rays 8
def bank12489 : Fin 2 → Cell := twoBank p12489 ray12489
theorem signs12489 : ∀ j, Signs p12489 (bank12489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12490 := params 9
abbrev ray12490 := rays 9
def bank12490 : Fin 2 → Cell := twoBank p12490 ray12490
theorem signs12490 : ∀ j, Signs p12490 (bank12490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12491 := params 10
abbrev ray12491 := rays 10
def bank12491 : Fin 2 → Cell := twoBank p12491 ray12491
theorem signs12491 : ∀ j, Signs p12491 (bank12491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12492 := params 11
abbrev ray12492 := rays 11
def bank12492 : Fin 2 → Cell := twoBank p12492 ray12492
theorem signs12492 : ∀ j, Signs p12492 (bank12492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12493 := params 12
abbrev ray12493 := rays 12
def bank12493 : Fin 2 → Cell := twoBank p12493 ray12493
theorem signs12493 : ∀ j, Signs p12493 (bank12493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12494 := params 13
abbrev ray12494 := rays 13
def bank12494 : Fin 2 → Cell := twoBank p12494 ray12494
theorem signs12494 : ∀ j, Signs p12494 (bank12494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12495 := params 14
abbrev ray12495 := rays 14
def bank12495 : Fin 2 → Cell := twoBank p12495 ray12495
theorem signs12495 : ∀ j, Signs p12495 (bank12495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12496 := params 15
abbrev ray12496 := rays 15
def bank12496 : Fin 2 → Cell := twoBank p12496 ray12496
theorem signs12496 : ∀ j, Signs p12496 (bank12496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12497 := params 16
abbrev ray12497 := rays 16
def bank12497 : Fin 2 → Cell := twoBank p12497 ray12497
theorem signs12497 : ∀ j, Signs p12497 (bank12497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12498 := params 17
abbrev ray12498 := rays 17
def bank12498 : Fin 2 → Cell := twoBank p12498 ray12498
theorem signs12498 : ∀ j, Signs p12498 (bank12498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12499 := params 18
abbrev ray12499 := rays 18
def bank12499 : Fin 2 → Cell := twoBank p12499 ray12499
theorem signs12499 : ∀ j, Signs p12499 (bank12499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12500 := params 19
abbrev ray12500 := rays 19
def bank12500 : Fin 2 → Cell := twoBank p12500 ray12500
theorem signs12500 : ∀ j, Signs p12500 (bank12500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12501 := params 20
abbrev ray12501 := rays 20
def bank12501 : Fin 2 → Cell := twoBank p12501 ray12501
theorem signs12501 : ∀ j, Signs p12501 (bank12501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12502 := params 21
abbrev ray12502 := rays 21
def bank12502 : Fin 2 → Cell := twoBank p12502 ray12502
theorem signs12502 : ∀ j, Signs p12502 (bank12502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12503 := params 22
abbrev ray12503 := rays 22
def bank12503 : Fin 2 → Cell := twoBank p12503 ray12503
theorem signs12503 : ∀ j, Signs p12503 (bank12503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12504 := params 23
abbrev ray12504 := rays 23
def bank12504 : Fin 2 → Cell := twoBank p12504 ray12504
theorem signs12504 : ∀ j, Signs p12504 (bank12504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12505 := params 24
abbrev ray12505 := rays 24
def bank12505 : Fin 2 → Cell := twoBank p12505 ray12505
theorem signs12505 : ∀ j, Signs p12505 (bank12505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12506 := params 25
abbrev ray12506 := rays 25
def bank12506 : Fin 2 → Cell := twoBank p12506 ray12506
theorem signs12506 : ∀ j, Signs p12506 (bank12506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12507 := params 26
abbrev ray12507 := rays 26
def bank12507 : Fin 2 → Cell := twoBank p12507 ray12507
theorem signs12507 : ∀ j, Signs p12507 (bank12507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12508 := params 27
abbrev ray12508 := rays 27
def bank12508 : Fin 2 → Cell := twoBank p12508 ray12508
theorem signs12508 : ∀ j, Signs p12508 (bank12508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12509 := params 28
abbrev ray12509 := rays 28
def bank12509 : Fin 2 → Cell := twoBank p12509 ray12509
theorem signs12509 : ∀ j, Signs p12509 (bank12509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12510 := params 29
abbrev ray12510 := rays 29
def bank12510 : Fin 2 → Cell := twoBank p12510 ray12510
theorem signs12510 : ∀ j, Signs p12510 (bank12510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12511 := params 30
abbrev ray12511 := rays 30
def bank12511 : Fin 2 → Cell := twoBank p12511 ray12511
theorem signs12511 : ∀ j, Signs p12511 (bank12511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12512 := params 31
abbrev ray12512 := rays 31
def bank12512 : Fin 2 → Cell := twoBank p12512 ray12512
theorem signs12512 : ∀ j, Signs p12512 (bank12512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12481_12512
