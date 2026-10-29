/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15553_15584
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95143427312506,95142961105444,95142494882366,95142028643272,95141562388162,95141096117037,95140629829896,95140163526739,95139697207567,95139230872380,95138764521177,95138298153959,95137831770726,95137365371477,95136898956213,95136432524934,95135966077640,95135499614332,95135033135009,95134566639671,95134100128318,95133633600951,95133167057569,95132700498173,95132233922762,95131767331337,95131300723898,95130834100444,95130367460976,95129900805494,95129434133998,95128967446488,95128500742965]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15552+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15553 := params 0
abbrev ray15553 := rays 0
def bank15553 : Fin 1 → Cell := oneBank p15553 ray15553
theorem signs15553 : ∀ j, Signs p15553 (bank15553 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15554 := params 1
abbrev ray15554 := rays 1
def bank15554 : Fin 1 → Cell := oneBank p15554 ray15554
theorem signs15554 : ∀ j, Signs p15554 (bank15554 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15555 := params 2
abbrev ray15555 := rays 2
def bank15555 : Fin 1 → Cell := oneBank p15555 ray15555
theorem signs15555 : ∀ j, Signs p15555 (bank15555 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15556 := params 3
abbrev ray15556 := rays 3
def bank15556 : Fin 1 → Cell := oneBank p15556 ray15556
theorem signs15556 : ∀ j, Signs p15556 (bank15556 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15557 := params 4
abbrev ray15557 := rays 4
def bank15557 : Fin 1 → Cell := oneBank p15557 ray15557
theorem signs15557 : ∀ j, Signs p15557 (bank15557 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15558 := params 5
abbrev ray15558 := rays 5
def bank15558 : Fin 1 → Cell := oneBank p15558 ray15558
theorem signs15558 : ∀ j, Signs p15558 (bank15558 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15559 := params 6
abbrev ray15559 := rays 6
def bank15559 : Fin 1 → Cell := oneBank p15559 ray15559
theorem signs15559 : ∀ j, Signs p15559 (bank15559 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15560 := params 7
abbrev ray15560 := rays 7
def bank15560 : Fin 1 → Cell := oneBank p15560 ray15560
theorem signs15560 : ∀ j, Signs p15560 (bank15560 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15561 := params 8
abbrev ray15561 := rays 8
def bank15561 : Fin 1 → Cell := oneBank p15561 ray15561
theorem signs15561 : ∀ j, Signs p15561 (bank15561 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15562 := params 9
abbrev ray15562 := rays 9
def bank15562 : Fin 1 → Cell := oneBank p15562 ray15562
theorem signs15562 : ∀ j, Signs p15562 (bank15562 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15563 := params 10
abbrev ray15563 := rays 10
def bank15563 : Fin 1 → Cell := oneBank p15563 ray15563
theorem signs15563 : ∀ j, Signs p15563 (bank15563 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15564 := params 11
abbrev ray15564 := rays 11
def bank15564 : Fin 1 → Cell := oneBank p15564 ray15564
theorem signs15564 : ∀ j, Signs p15564 (bank15564 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15565 := params 12
abbrev ray15565 := rays 12
def bank15565 : Fin 1 → Cell := oneBank p15565 ray15565
theorem signs15565 : ∀ j, Signs p15565 (bank15565 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15566 := params 13
abbrev ray15566 := rays 13
def bank15566 : Fin 1 → Cell := oneBank p15566 ray15566
theorem signs15566 : ∀ j, Signs p15566 (bank15566 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15567 := params 14
abbrev ray15567 := rays 14
def bank15567 : Fin 1 → Cell := oneBank p15567 ray15567
theorem signs15567 : ∀ j, Signs p15567 (bank15567 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15568 := params 15
abbrev ray15568 := rays 15
def bank15568 : Fin 1 → Cell := oneBank p15568 ray15568
theorem signs15568 : ∀ j, Signs p15568 (bank15568 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15569 := params 16
abbrev ray15569 := rays 16
def bank15569 : Fin 1 → Cell := oneBank p15569 ray15569
theorem signs15569 : ∀ j, Signs p15569 (bank15569 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15570 := params 17
abbrev ray15570 := rays 17
def bank15570 : Fin 1 → Cell := oneBank p15570 ray15570
theorem signs15570 : ∀ j, Signs p15570 (bank15570 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15571 := params 18
abbrev ray15571 := rays 18
def bank15571 : Fin 1 → Cell := oneBank p15571 ray15571
theorem signs15571 : ∀ j, Signs p15571 (bank15571 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15572 := params 19
abbrev ray15572 := rays 19
def bank15572 : Fin 1 → Cell := oneBank p15572 ray15572
theorem signs15572 : ∀ j, Signs p15572 (bank15572 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15573 := params 20
abbrev ray15573 := rays 20
def bank15573 : Fin 1 → Cell := oneBank p15573 ray15573
theorem signs15573 : ∀ j, Signs p15573 (bank15573 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15574 := params 21
abbrev ray15574 := rays 21
def bank15574 : Fin 1 → Cell := oneBank p15574 ray15574
theorem signs15574 : ∀ j, Signs p15574 (bank15574 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15575 := params 22
abbrev ray15575 := rays 22
def bank15575 : Fin 1 → Cell := oneBank p15575 ray15575
theorem signs15575 : ∀ j, Signs p15575 (bank15575 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15576 := params 23
abbrev ray15576 := rays 23
def bank15576 : Fin 1 → Cell := oneBank p15576 ray15576
theorem signs15576 : ∀ j, Signs p15576 (bank15576 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15577 := params 24
abbrev ray15577 := rays 24
def bank15577 : Fin 1 → Cell := oneBank p15577 ray15577
theorem signs15577 : ∀ j, Signs p15577 (bank15577 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15578 := params 25
abbrev ray15578 := rays 25
def bank15578 : Fin 1 → Cell := oneBank p15578 ray15578
theorem signs15578 : ∀ j, Signs p15578 (bank15578 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15579 := params 26
abbrev ray15579 := rays 26
def bank15579 : Fin 1 → Cell := oneBank p15579 ray15579
theorem signs15579 : ∀ j, Signs p15579 (bank15579 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15580 := params 27
abbrev ray15580 := rays 27
def bank15580 : Fin 1 → Cell := oneBank p15580 ray15580
theorem signs15580 : ∀ j, Signs p15580 (bank15580 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15581 := params 28
abbrev ray15581 := rays 28
def bank15581 : Fin 1 → Cell := oneBank p15581 ray15581
theorem signs15581 : ∀ j, Signs p15581 (bank15581 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15582 := params 29
abbrev ray15582 := rays 29
def bank15582 : Fin 1 → Cell := oneBank p15582 ray15582
theorem signs15582 : ∀ j, Signs p15582 (bank15582 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15583 := params 30
abbrev ray15583 := rays 30
def bank15583 : Fin 1 → Cell := oneBank p15583 ray15583
theorem signs15583 : ∀ j, Signs p15583 (bank15583 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15584 := params 31
abbrev ray15584 := rays 31
def bank15584 : Fin 1 → Cell := oneBank p15584 ray15584
theorem signs15584 : ∀ j, Signs p15584 (bank15584 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15553_15584
