/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12545_12576
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96472650412345,96472233657669,96471816883865,96471400090933,96470983278873,96470566447685,96470149597371,96469732727930,96469315839363,96468898931670,96468482004852,96468065058909,96467648093841,96467231109649,96466814106333,96466397083894,96465980042332,96465562981648,96465145901841,96464728802913,96464311684863,96463894547692,96463477391401,96463060215990,96462643021459,96462225807809,96461808575040,96461391323152,96460974052146,96460556762022,96460139452781,96459722124423,96459304776948]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12544+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12545 := params 0
abbrev ray12545 := rays 0
def bank12545 : Fin 2 → Cell := twoBank p12545 ray12545
theorem signs12545 : ∀ j, Signs p12545 (bank12545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12546 := params 1
abbrev ray12546 := rays 1
def bank12546 : Fin 2 → Cell := twoBank p12546 ray12546
theorem signs12546 : ∀ j, Signs p12546 (bank12546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12547 := params 2
abbrev ray12547 := rays 2
def bank12547 : Fin 2 → Cell := twoBank p12547 ray12547
theorem signs12547 : ∀ j, Signs p12547 (bank12547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12548 := params 3
abbrev ray12548 := rays 3
def bank12548 : Fin 2 → Cell := twoBank p12548 ray12548
theorem signs12548 : ∀ j, Signs p12548 (bank12548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12549 := params 4
abbrev ray12549 := rays 4
def bank12549 : Fin 2 → Cell := twoBank p12549 ray12549
theorem signs12549 : ∀ j, Signs p12549 (bank12549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12550 := params 5
abbrev ray12550 := rays 5
def bank12550 : Fin 2 → Cell := twoBank p12550 ray12550
theorem signs12550 : ∀ j, Signs p12550 (bank12550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12551 := params 6
abbrev ray12551 := rays 6
def bank12551 : Fin 2 → Cell := twoBank p12551 ray12551
theorem signs12551 : ∀ j, Signs p12551 (bank12551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12552 := params 7
abbrev ray12552 := rays 7
def bank12552 : Fin 2 → Cell := twoBank p12552 ray12552
theorem signs12552 : ∀ j, Signs p12552 (bank12552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12553 := params 8
abbrev ray12553 := rays 8
def bank12553 : Fin 2 → Cell := twoBank p12553 ray12553
theorem signs12553 : ∀ j, Signs p12553 (bank12553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12554 := params 9
abbrev ray12554 := rays 9
def bank12554 : Fin 2 → Cell := twoBank p12554 ray12554
theorem signs12554 : ∀ j, Signs p12554 (bank12554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12555 := params 10
abbrev ray12555 := rays 10
def bank12555 : Fin 2 → Cell := twoBank p12555 ray12555
theorem signs12555 : ∀ j, Signs p12555 (bank12555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12556 := params 11
abbrev ray12556 := rays 11
def bank12556 : Fin 2 → Cell := twoBank p12556 ray12556
theorem signs12556 : ∀ j, Signs p12556 (bank12556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12557 := params 12
abbrev ray12557 := rays 12
def bank12557 : Fin 2 → Cell := twoBank p12557 ray12557
theorem signs12557 : ∀ j, Signs p12557 (bank12557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12558 := params 13
abbrev ray12558 := rays 13
def bank12558 : Fin 2 → Cell := twoBank p12558 ray12558
theorem signs12558 : ∀ j, Signs p12558 (bank12558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12559 := params 14
abbrev ray12559 := rays 14
def bank12559 : Fin 2 → Cell := twoBank p12559 ray12559
theorem signs12559 : ∀ j, Signs p12559 (bank12559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12560 := params 15
abbrev ray12560 := rays 15
def bank12560 : Fin 2 → Cell := twoBank p12560 ray12560
theorem signs12560 : ∀ j, Signs p12560 (bank12560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12561 := params 16
abbrev ray12561 := rays 16
def bank12561 : Fin 2 → Cell := twoBank p12561 ray12561
theorem signs12561 : ∀ j, Signs p12561 (bank12561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12562 := params 17
abbrev ray12562 := rays 17
def bank12562 : Fin 2 → Cell := twoBank p12562 ray12562
theorem signs12562 : ∀ j, Signs p12562 (bank12562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12563 := params 18
abbrev ray12563 := rays 18
def bank12563 : Fin 2 → Cell := twoBank p12563 ray12563
theorem signs12563 : ∀ j, Signs p12563 (bank12563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12564 := params 19
abbrev ray12564 := rays 19
def bank12564 : Fin 2 → Cell := twoBank p12564 ray12564
theorem signs12564 : ∀ j, Signs p12564 (bank12564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12565 := params 20
abbrev ray12565 := rays 20
def bank12565 : Fin 2 → Cell := twoBank p12565 ray12565
theorem signs12565 : ∀ j, Signs p12565 (bank12565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12566 := params 21
abbrev ray12566 := rays 21
def bank12566 : Fin 2 → Cell := twoBank p12566 ray12566
theorem signs12566 : ∀ j, Signs p12566 (bank12566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12567 := params 22
abbrev ray12567 := rays 22
def bank12567 : Fin 2 → Cell := twoBank p12567 ray12567
theorem signs12567 : ∀ j, Signs p12567 (bank12567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12568 := params 23
abbrev ray12568 := rays 23
def bank12568 : Fin 2 → Cell := twoBank p12568 ray12568
theorem signs12568 : ∀ j, Signs p12568 (bank12568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12569 := params 24
abbrev ray12569 := rays 24
def bank12569 : Fin 2 → Cell := twoBank p12569 ray12569
theorem signs12569 : ∀ j, Signs p12569 (bank12569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12570 := params 25
abbrev ray12570 := rays 25
def bank12570 : Fin 2 → Cell := twoBank p12570 ray12570
theorem signs12570 : ∀ j, Signs p12570 (bank12570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12571 := params 26
abbrev ray12571 := rays 26
def bank12571 : Fin 2 → Cell := twoBank p12571 ray12571
theorem signs12571 : ∀ j, Signs p12571 (bank12571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12572 := params 27
abbrev ray12572 := rays 27
def bank12572 : Fin 2 → Cell := twoBank p12572 ray12572
theorem signs12572 : ∀ j, Signs p12572 (bank12572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12573 := params 28
abbrev ray12573 := rays 28
def bank12573 : Fin 2 → Cell := twoBank p12573 ray12573
theorem signs12573 : ∀ j, Signs p12573 (bank12573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12574 := params 29
abbrev ray12574 := rays 29
def bank12574 : Fin 2 → Cell := twoBank p12574 ray12574
theorem signs12574 : ∀ j, Signs p12574 (bank12574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12575 := params 30
abbrev ray12575 := rays 30
def bank12575 : Fin 2 → Cell := twoBank p12575 ray12575
theorem signs12575 : ∀ j, Signs p12575 (bank12575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12576 := params 31
abbrev ray12576 := rays 31
def bank12576 : Fin 2 → Cell := twoBank p12576 ray12576
theorem signs12576 : ∀ j, Signs p12576 (bank12576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12545_12576
