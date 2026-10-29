/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10465_10496
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97297454784899,97297078770916,97296702736846,97296326682689,97295950608446,97295574514118,97295198399705,97294822265208,97294446110627,97294069935963,97293693741216,97293317526387,97292941291476,97292565036484,97292188761411,97291812466258,97291436151025,97291059815713,97290683460322,97290307084853,97289930689307,97289554273684,97289177837984,97288801382208,97288424906357,97288048410431,97287671894430,97287295358355,97286918802207,97286542225986,97286165629693,97285789013328,97285412376892]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10464+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10465 := params 0
abbrev ray10465 := rays 0
def bank10465 : Fin 2 → Cell := twoBank p10465 ray10465
theorem signs10465 : ∀ j, Signs p10465 (bank10465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10466 := params 1
abbrev ray10466 := rays 1
def bank10466 : Fin 2 → Cell := twoBank p10466 ray10466
theorem signs10466 : ∀ j, Signs p10466 (bank10466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10467 := params 2
abbrev ray10467 := rays 2
def bank10467 : Fin 2 → Cell := twoBank p10467 ray10467
theorem signs10467 : ∀ j, Signs p10467 (bank10467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10468 := params 3
abbrev ray10468 := rays 3
def bank10468 : Fin 2 → Cell := twoBank p10468 ray10468
theorem signs10468 : ∀ j, Signs p10468 (bank10468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10469 := params 4
abbrev ray10469 := rays 4
def bank10469 : Fin 2 → Cell := twoBank p10469 ray10469
theorem signs10469 : ∀ j, Signs p10469 (bank10469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10470 := params 5
abbrev ray10470 := rays 5
def bank10470 : Fin 2 → Cell := twoBank p10470 ray10470
theorem signs10470 : ∀ j, Signs p10470 (bank10470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10471 := params 6
abbrev ray10471 := rays 6
def bank10471 : Fin 2 → Cell := twoBank p10471 ray10471
theorem signs10471 : ∀ j, Signs p10471 (bank10471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10472 := params 7
abbrev ray10472 := rays 7
def bank10472 : Fin 2 → Cell := twoBank p10472 ray10472
theorem signs10472 : ∀ j, Signs p10472 (bank10472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10473 := params 8
abbrev ray10473 := rays 8
def bank10473 : Fin 2 → Cell := twoBank p10473 ray10473
theorem signs10473 : ∀ j, Signs p10473 (bank10473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10474 := params 9
abbrev ray10474 := rays 9
def bank10474 : Fin 2 → Cell := twoBank p10474 ray10474
theorem signs10474 : ∀ j, Signs p10474 (bank10474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10475 := params 10
abbrev ray10475 := rays 10
def bank10475 : Fin 2 → Cell := twoBank p10475 ray10475
theorem signs10475 : ∀ j, Signs p10475 (bank10475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10476 := params 11
abbrev ray10476 := rays 11
def bank10476 : Fin 2 → Cell := twoBank p10476 ray10476
theorem signs10476 : ∀ j, Signs p10476 (bank10476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10477 := params 12
abbrev ray10477 := rays 12
def bank10477 : Fin 2 → Cell := twoBank p10477 ray10477
theorem signs10477 : ∀ j, Signs p10477 (bank10477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10478 := params 13
abbrev ray10478 := rays 13
def bank10478 : Fin 2 → Cell := twoBank p10478 ray10478
theorem signs10478 : ∀ j, Signs p10478 (bank10478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10479 := params 14
abbrev ray10479 := rays 14
def bank10479 : Fin 2 → Cell := twoBank p10479 ray10479
theorem signs10479 : ∀ j, Signs p10479 (bank10479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10480 := params 15
abbrev ray10480 := rays 15
def bank10480 : Fin 2 → Cell := twoBank p10480 ray10480
theorem signs10480 : ∀ j, Signs p10480 (bank10480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10481 := params 16
abbrev ray10481 := rays 16
def bank10481 : Fin 2 → Cell := twoBank p10481 ray10481
theorem signs10481 : ∀ j, Signs p10481 (bank10481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10482 := params 17
abbrev ray10482 := rays 17
def bank10482 : Fin 2 → Cell := twoBank p10482 ray10482
theorem signs10482 : ∀ j, Signs p10482 (bank10482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10483 := params 18
abbrev ray10483 := rays 18
def bank10483 : Fin 2 → Cell := twoBank p10483 ray10483
theorem signs10483 : ∀ j, Signs p10483 (bank10483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10484 := params 19
abbrev ray10484 := rays 19
def bank10484 : Fin 2 → Cell := twoBank p10484 ray10484
theorem signs10484 : ∀ j, Signs p10484 (bank10484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10485 := params 20
abbrev ray10485 := rays 20
def bank10485 : Fin 2 → Cell := twoBank p10485 ray10485
theorem signs10485 : ∀ j, Signs p10485 (bank10485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10486 := params 21
abbrev ray10486 := rays 21
def bank10486 : Fin 2 → Cell := twoBank p10486 ray10486
theorem signs10486 : ∀ j, Signs p10486 (bank10486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10487 := params 22
abbrev ray10487 := rays 22
def bank10487 : Fin 2 → Cell := twoBank p10487 ray10487
theorem signs10487 : ∀ j, Signs p10487 (bank10487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10488 := params 23
abbrev ray10488 := rays 23
def bank10488 : Fin 2 → Cell := twoBank p10488 ray10488
theorem signs10488 : ∀ j, Signs p10488 (bank10488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10489 := params 24
abbrev ray10489 := rays 24
def bank10489 : Fin 2 → Cell := twoBank p10489 ray10489
theorem signs10489 : ∀ j, Signs p10489 (bank10489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10490 := params 25
abbrev ray10490 := rays 25
def bank10490 : Fin 2 → Cell := twoBank p10490 ray10490
theorem signs10490 : ∀ j, Signs p10490 (bank10490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10491 := params 26
abbrev ray10491 := rays 26
def bank10491 : Fin 2 → Cell := twoBank p10491 ray10491
theorem signs10491 : ∀ j, Signs p10491 (bank10491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10492 := params 27
abbrev ray10492 := rays 27
def bank10492 : Fin 2 → Cell := twoBank p10492 ray10492
theorem signs10492 : ∀ j, Signs p10492 (bank10492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10493 := params 28
abbrev ray10493 := rays 28
def bank10493 : Fin 2 → Cell := twoBank p10493 ray10493
theorem signs10493 : ∀ j, Signs p10493 (bank10493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10494 := params 29
abbrev ray10494 := rays 29
def bank10494 : Fin 2 → Cell := twoBank p10494 ray10494
theorem signs10494 : ∀ j, Signs p10494 (bank10494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10495 := params 30
abbrev ray10495 := rays 30
def bank10495 : Fin 2 → Cell := twoBank p10495 ray10495
theorem signs10495 : ∀ j, Signs p10495 (bank10495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10496 := params 31
abbrev ray10496 := rays 31
def bank10496 : Fin 2 → Cell := twoBank p10496 ray10496
theorem signs10496 : ∀ j, Signs p10496 (bank10496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10465_10496
