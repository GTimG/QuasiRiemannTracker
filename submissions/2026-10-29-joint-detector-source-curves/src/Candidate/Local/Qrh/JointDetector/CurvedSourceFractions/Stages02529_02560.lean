/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02529_02560
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99592774686363,99592581192279,99592387671216,99592194123176,99592000548159,99591806946168,99591613317203,99591419661266,99591225978358,99591032268481,99590838531636,99590644767824,99590450977046,99590257159304,99590063314600,99589869442934,99589675544308,99589481618724,99589287666182,99589093686685,99588899680233,99588705646828,99588511586471,99588317499163,99588123384906,99587929243701,99587735075550,99587540880454,99587346658414,99587152409431,99586958133507,99586763830644,99586569500842]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2528+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2529 := params 0
abbrev ray2529 := rays 0
def bank2529 : Fin 2 → Cell := twoBank p2529 ray2529
theorem signs2529 : ∀ j, Signs p2529 (bank2529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2530 := params 1
abbrev ray2530 := rays 1
def bank2530 : Fin 2 → Cell := twoBank p2530 ray2530
theorem signs2530 : ∀ j, Signs p2530 (bank2530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2531 := params 2
abbrev ray2531 := rays 2
def bank2531 : Fin 2 → Cell := twoBank p2531 ray2531
theorem signs2531 : ∀ j, Signs p2531 (bank2531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2532 := params 3
abbrev ray2532 := rays 3
def bank2532 : Fin 2 → Cell := twoBank p2532 ray2532
theorem signs2532 : ∀ j, Signs p2532 (bank2532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2533 := params 4
abbrev ray2533 := rays 4
def bank2533 : Fin 2 → Cell := twoBank p2533 ray2533
theorem signs2533 : ∀ j, Signs p2533 (bank2533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2534 := params 5
abbrev ray2534 := rays 5
def bank2534 : Fin 2 → Cell := twoBank p2534 ray2534
theorem signs2534 : ∀ j, Signs p2534 (bank2534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2535 := params 6
abbrev ray2535 := rays 6
def bank2535 : Fin 2 → Cell := twoBank p2535 ray2535
theorem signs2535 : ∀ j, Signs p2535 (bank2535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2536 := params 7
abbrev ray2536 := rays 7
def bank2536 : Fin 2 → Cell := twoBank p2536 ray2536
theorem signs2536 : ∀ j, Signs p2536 (bank2536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2537 := params 8
abbrev ray2537 := rays 8
def bank2537 : Fin 2 → Cell := twoBank p2537 ray2537
theorem signs2537 : ∀ j, Signs p2537 (bank2537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2538 := params 9
abbrev ray2538 := rays 9
def bank2538 : Fin 2 → Cell := twoBank p2538 ray2538
theorem signs2538 : ∀ j, Signs p2538 (bank2538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2539 := params 10
abbrev ray2539 := rays 10
def bank2539 : Fin 2 → Cell := twoBank p2539 ray2539
theorem signs2539 : ∀ j, Signs p2539 (bank2539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2540 := params 11
abbrev ray2540 := rays 11
def bank2540 : Fin 2 → Cell := twoBank p2540 ray2540
theorem signs2540 : ∀ j, Signs p2540 (bank2540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2541 := params 12
abbrev ray2541 := rays 12
def bank2541 : Fin 2 → Cell := twoBank p2541 ray2541
theorem signs2541 : ∀ j, Signs p2541 (bank2541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2542 := params 13
abbrev ray2542 := rays 13
def bank2542 : Fin 2 → Cell := twoBank p2542 ray2542
theorem signs2542 : ∀ j, Signs p2542 (bank2542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2543 := params 14
abbrev ray2543 := rays 14
def bank2543 : Fin 2 → Cell := twoBank p2543 ray2543
theorem signs2543 : ∀ j, Signs p2543 (bank2543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2544 := params 15
abbrev ray2544 := rays 15
def bank2544 : Fin 2 → Cell := twoBank p2544 ray2544
theorem signs2544 : ∀ j, Signs p2544 (bank2544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2545 := params 16
abbrev ray2545 := rays 16
def bank2545 : Fin 2 → Cell := twoBank p2545 ray2545
theorem signs2545 : ∀ j, Signs p2545 (bank2545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2546 := params 17
abbrev ray2546 := rays 17
def bank2546 : Fin 2 → Cell := twoBank p2546 ray2546
theorem signs2546 : ∀ j, Signs p2546 (bank2546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2547 := params 18
abbrev ray2547 := rays 18
def bank2547 : Fin 2 → Cell := twoBank p2547 ray2547
theorem signs2547 : ∀ j, Signs p2547 (bank2547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2548 := params 19
abbrev ray2548 := rays 19
def bank2548 : Fin 2 → Cell := twoBank p2548 ray2548
theorem signs2548 : ∀ j, Signs p2548 (bank2548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2549 := params 20
abbrev ray2549 := rays 20
def bank2549 : Fin 2 → Cell := twoBank p2549 ray2549
theorem signs2549 : ∀ j, Signs p2549 (bank2549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2550 := params 21
abbrev ray2550 := rays 21
def bank2550 : Fin 2 → Cell := twoBank p2550 ray2550
theorem signs2550 : ∀ j, Signs p2550 (bank2550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2551 := params 22
abbrev ray2551 := rays 22
def bank2551 : Fin 2 → Cell := twoBank p2551 ray2551
theorem signs2551 : ∀ j, Signs p2551 (bank2551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2552 := params 23
abbrev ray2552 := rays 23
def bank2552 : Fin 2 → Cell := twoBank p2552 ray2552
theorem signs2552 : ∀ j, Signs p2552 (bank2552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2553 := params 24
abbrev ray2553 := rays 24
def bank2553 : Fin 2 → Cell := twoBank p2553 ray2553
theorem signs2553 : ∀ j, Signs p2553 (bank2553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2554 := params 25
abbrev ray2554 := rays 25
def bank2554 : Fin 2 → Cell := twoBank p2554 ray2554
theorem signs2554 : ∀ j, Signs p2554 (bank2554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2555 := params 26
abbrev ray2555 := rays 26
def bank2555 : Fin 2 → Cell := twoBank p2555 ray2555
theorem signs2555 : ∀ j, Signs p2555 (bank2555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2556 := params 27
abbrev ray2556 := rays 27
def bank2556 : Fin 2 → Cell := twoBank p2556 ray2556
theorem signs2556 : ∀ j, Signs p2556 (bank2556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2557 := params 28
abbrev ray2557 := rays 28
def bank2557 : Fin 2 → Cell := twoBank p2557 ray2557
theorem signs2557 : ∀ j, Signs p2557 (bank2557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2558 := params 29
abbrev ray2558 := rays 29
def bank2558 : Fin 2 → Cell := twoBank p2558 ray2558
theorem signs2558 : ∀ j, Signs p2558 (bank2558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2559 := params 30
abbrev ray2559 := rays 30
def bank2559 : Fin 2 → Cell := twoBank p2559 ray2559
theorem signs2559 : ∀ j, Signs p2559 (bank2559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2560 := params 31
abbrev ray2560 := rays 31
def bank2560 : Fin 2 → Cell := twoBank p2560 ray2560
theorem signs2560 : ∀ j, Signs p2560 (bank2560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02529_02560
