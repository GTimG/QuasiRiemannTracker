/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11585_11616
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96863849960067,96863451762098,96863053544590,96862655307543,96862257050957,96861858774833,96861460479172,96861062163973,96860663829238,96860265474966,96859867101159,96859468707816,96859070294938,96858671862526,96858273410580,96857874939100,96857476448087,96857077937541,96856679407463,96856280857854,96855882288713,96855483700041,96855085091839,96854686464107,96854287816846,96853889150056,96853490463737,96853091757890,96852693032515,96852294287613,96851895523184,96851496739229,96851097935748]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11584+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11585 := params 0
abbrev ray11585 := rays 0
def bank11585 : Fin 2 → Cell := twoBank p11585 ray11585
theorem signs11585 : ∀ j, Signs p11585 (bank11585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11586 := params 1
abbrev ray11586 := rays 1
def bank11586 : Fin 2 → Cell := twoBank p11586 ray11586
theorem signs11586 : ∀ j, Signs p11586 (bank11586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11587 := params 2
abbrev ray11587 := rays 2
def bank11587 : Fin 2 → Cell := twoBank p11587 ray11587
theorem signs11587 : ∀ j, Signs p11587 (bank11587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11588 := params 3
abbrev ray11588 := rays 3
def bank11588 : Fin 2 → Cell := twoBank p11588 ray11588
theorem signs11588 : ∀ j, Signs p11588 (bank11588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11589 := params 4
abbrev ray11589 := rays 4
def bank11589 : Fin 2 → Cell := twoBank p11589 ray11589
theorem signs11589 : ∀ j, Signs p11589 (bank11589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11590 := params 5
abbrev ray11590 := rays 5
def bank11590 : Fin 2 → Cell := twoBank p11590 ray11590
theorem signs11590 : ∀ j, Signs p11590 (bank11590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11591 := params 6
abbrev ray11591 := rays 6
def bank11591 : Fin 2 → Cell := twoBank p11591 ray11591
theorem signs11591 : ∀ j, Signs p11591 (bank11591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11592 := params 7
abbrev ray11592 := rays 7
def bank11592 : Fin 2 → Cell := twoBank p11592 ray11592
theorem signs11592 : ∀ j, Signs p11592 (bank11592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11593 := params 8
abbrev ray11593 := rays 8
def bank11593 : Fin 2 → Cell := twoBank p11593 ray11593
theorem signs11593 : ∀ j, Signs p11593 (bank11593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11594 := params 9
abbrev ray11594 := rays 9
def bank11594 : Fin 2 → Cell := twoBank p11594 ray11594
theorem signs11594 : ∀ j, Signs p11594 (bank11594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11595 := params 10
abbrev ray11595 := rays 10
def bank11595 : Fin 2 → Cell := twoBank p11595 ray11595
theorem signs11595 : ∀ j, Signs p11595 (bank11595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11596 := params 11
abbrev ray11596 := rays 11
def bank11596 : Fin 2 → Cell := twoBank p11596 ray11596
theorem signs11596 : ∀ j, Signs p11596 (bank11596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11597 := params 12
abbrev ray11597 := rays 12
def bank11597 : Fin 2 → Cell := twoBank p11597 ray11597
theorem signs11597 : ∀ j, Signs p11597 (bank11597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11598 := params 13
abbrev ray11598 := rays 13
def bank11598 : Fin 2 → Cell := twoBank p11598 ray11598
theorem signs11598 : ∀ j, Signs p11598 (bank11598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11599 := params 14
abbrev ray11599 := rays 14
def bank11599 : Fin 2 → Cell := twoBank p11599 ray11599
theorem signs11599 : ∀ j, Signs p11599 (bank11599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11600 := params 15
abbrev ray11600 := rays 15
def bank11600 : Fin 2 → Cell := twoBank p11600 ray11600
theorem signs11600 : ∀ j, Signs p11600 (bank11600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11601 := params 16
abbrev ray11601 := rays 16
def bank11601 : Fin 2 → Cell := twoBank p11601 ray11601
theorem signs11601 : ∀ j, Signs p11601 (bank11601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11602 := params 17
abbrev ray11602 := rays 17
def bank11602 : Fin 2 → Cell := twoBank p11602 ray11602
theorem signs11602 : ∀ j, Signs p11602 (bank11602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11603 := params 18
abbrev ray11603 := rays 18
def bank11603 : Fin 2 → Cell := twoBank p11603 ray11603
theorem signs11603 : ∀ j, Signs p11603 (bank11603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11604 := params 19
abbrev ray11604 := rays 19
def bank11604 : Fin 2 → Cell := twoBank p11604 ray11604
theorem signs11604 : ∀ j, Signs p11604 (bank11604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11605 := params 20
abbrev ray11605 := rays 20
def bank11605 : Fin 2 → Cell := twoBank p11605 ray11605
theorem signs11605 : ∀ j, Signs p11605 (bank11605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11606 := params 21
abbrev ray11606 := rays 21
def bank11606 : Fin 2 → Cell := twoBank p11606 ray11606
theorem signs11606 : ∀ j, Signs p11606 (bank11606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11607 := params 22
abbrev ray11607 := rays 22
def bank11607 : Fin 2 → Cell := twoBank p11607 ray11607
theorem signs11607 : ∀ j, Signs p11607 (bank11607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11608 := params 23
abbrev ray11608 := rays 23
def bank11608 : Fin 2 → Cell := twoBank p11608 ray11608
theorem signs11608 : ∀ j, Signs p11608 (bank11608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11609 := params 24
abbrev ray11609 := rays 24
def bank11609 : Fin 2 → Cell := twoBank p11609 ray11609
theorem signs11609 : ∀ j, Signs p11609 (bank11609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11610 := params 25
abbrev ray11610 := rays 25
def bank11610 : Fin 2 → Cell := twoBank p11610 ray11610
theorem signs11610 : ∀ j, Signs p11610 (bank11610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11611 := params 26
abbrev ray11611 := rays 26
def bank11611 : Fin 2 → Cell := twoBank p11611 ray11611
theorem signs11611 : ∀ j, Signs p11611 (bank11611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11612 := params 27
abbrev ray11612 := rays 27
def bank11612 : Fin 2 → Cell := twoBank p11612 ray11612
theorem signs11612 : ∀ j, Signs p11612 (bank11612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11613 := params 28
abbrev ray11613 := rays 28
def bank11613 : Fin 2 → Cell := twoBank p11613 ray11613
theorem signs11613 : ∀ j, Signs p11613 (bank11613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11614 := params 29
abbrev ray11614 := rays 29
def bank11614 : Fin 2 → Cell := twoBank p11614 ray11614
theorem signs11614 : ∀ j, Signs p11614 (bank11614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11615 := params 30
abbrev ray11615 := rays 30
def bank11615 : Fin 2 → Cell := twoBank p11615 ray11615
theorem signs11615 : ∀ j, Signs p11615 (bank11615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11616 := params 31
abbrev ray11616 := rays 31
def bank11616 : Fin 2 → Cell := twoBank p11616 ray11616
theorem signs11616 : ∀ j, Signs p11616 (bank11616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11585_11616
