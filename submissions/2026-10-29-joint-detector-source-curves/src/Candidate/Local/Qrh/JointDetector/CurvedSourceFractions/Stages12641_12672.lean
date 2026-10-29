/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12641_12672
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96432554794415,96432136205220,96431717596935,96431298969560,96430880323095,96430461657541,96430042972898,96429624269167,96429205546348,96428786804442,96428368043449,96427949263369,96427530464202,96427111645950,96426692808612,96426273952189,96425855076681,96425436182089,96425017268413,96424598335653,96424179383810,96423760412884,96423341422876,96422922413786,96422503385614,96422084338361,96421665272027,96421246186613,96420827082119,96420407958545,96419988815892,96419569654160,96419150473350]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12640+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12641 := params 0
abbrev ray12641 := rays 0
def bank12641 : Fin 2 → Cell := twoBank p12641 ray12641
theorem signs12641 : ∀ j, Signs p12641 (bank12641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12642 := params 1
abbrev ray12642 := rays 1
def bank12642 : Fin 2 → Cell := twoBank p12642 ray12642
theorem signs12642 : ∀ j, Signs p12642 (bank12642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12643 := params 2
abbrev ray12643 := rays 2
def bank12643 : Fin 2 → Cell := twoBank p12643 ray12643
theorem signs12643 : ∀ j, Signs p12643 (bank12643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12644 := params 3
abbrev ray12644 := rays 3
def bank12644 : Fin 2 → Cell := twoBank p12644 ray12644
theorem signs12644 : ∀ j, Signs p12644 (bank12644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12645 := params 4
abbrev ray12645 := rays 4
def bank12645 : Fin 2 → Cell := twoBank p12645 ray12645
theorem signs12645 : ∀ j, Signs p12645 (bank12645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12646 := params 5
abbrev ray12646 := rays 5
def bank12646 : Fin 2 → Cell := twoBank p12646 ray12646
theorem signs12646 : ∀ j, Signs p12646 (bank12646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12647 := params 6
abbrev ray12647 := rays 6
def bank12647 : Fin 2 → Cell := twoBank p12647 ray12647
theorem signs12647 : ∀ j, Signs p12647 (bank12647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12648 := params 7
abbrev ray12648 := rays 7
def bank12648 : Fin 2 → Cell := twoBank p12648 ray12648
theorem signs12648 : ∀ j, Signs p12648 (bank12648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12649 := params 8
abbrev ray12649 := rays 8
def bank12649 : Fin 2 → Cell := twoBank p12649 ray12649
theorem signs12649 : ∀ j, Signs p12649 (bank12649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12650 := params 9
abbrev ray12650 := rays 9
def bank12650 : Fin 2 → Cell := twoBank p12650 ray12650
theorem signs12650 : ∀ j, Signs p12650 (bank12650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12651 := params 10
abbrev ray12651 := rays 10
def bank12651 : Fin 2 → Cell := twoBank p12651 ray12651
theorem signs12651 : ∀ j, Signs p12651 (bank12651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12652 := params 11
abbrev ray12652 := rays 11
def bank12652 : Fin 2 → Cell := twoBank p12652 ray12652
theorem signs12652 : ∀ j, Signs p12652 (bank12652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12653 := params 12
abbrev ray12653 := rays 12
def bank12653 : Fin 2 → Cell := twoBank p12653 ray12653
theorem signs12653 : ∀ j, Signs p12653 (bank12653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12654 := params 13
abbrev ray12654 := rays 13
def bank12654 : Fin 2 → Cell := twoBank p12654 ray12654
theorem signs12654 : ∀ j, Signs p12654 (bank12654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12655 := params 14
abbrev ray12655 := rays 14
def bank12655 : Fin 2 → Cell := twoBank p12655 ray12655
theorem signs12655 : ∀ j, Signs p12655 (bank12655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12656 := params 15
abbrev ray12656 := rays 15
def bank12656 : Fin 2 → Cell := twoBank p12656 ray12656
theorem signs12656 : ∀ j, Signs p12656 (bank12656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12657 := params 16
abbrev ray12657 := rays 16
def bank12657 : Fin 2 → Cell := twoBank p12657 ray12657
theorem signs12657 : ∀ j, Signs p12657 (bank12657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12658 := params 17
abbrev ray12658 := rays 17
def bank12658 : Fin 2 → Cell := twoBank p12658 ray12658
theorem signs12658 : ∀ j, Signs p12658 (bank12658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12659 := params 18
abbrev ray12659 := rays 18
def bank12659 : Fin 2 → Cell := twoBank p12659 ray12659
theorem signs12659 : ∀ j, Signs p12659 (bank12659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12660 := params 19
abbrev ray12660 := rays 19
def bank12660 : Fin 2 → Cell := twoBank p12660 ray12660
theorem signs12660 : ∀ j, Signs p12660 (bank12660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12661 := params 20
abbrev ray12661 := rays 20
def bank12661 : Fin 2 → Cell := twoBank p12661 ray12661
theorem signs12661 : ∀ j, Signs p12661 (bank12661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12662 := params 21
abbrev ray12662 := rays 21
def bank12662 : Fin 2 → Cell := twoBank p12662 ray12662
theorem signs12662 : ∀ j, Signs p12662 (bank12662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12663 := params 22
abbrev ray12663 := rays 22
def bank12663 : Fin 2 → Cell := twoBank p12663 ray12663
theorem signs12663 : ∀ j, Signs p12663 (bank12663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12664 := params 23
abbrev ray12664 := rays 23
def bank12664 : Fin 2 → Cell := twoBank p12664 ray12664
theorem signs12664 : ∀ j, Signs p12664 (bank12664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12665 := params 24
abbrev ray12665 := rays 24
def bank12665 : Fin 2 → Cell := twoBank p12665 ray12665
theorem signs12665 : ∀ j, Signs p12665 (bank12665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12666 := params 25
abbrev ray12666 := rays 25
def bank12666 : Fin 2 → Cell := twoBank p12666 ray12666
theorem signs12666 : ∀ j, Signs p12666 (bank12666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12667 := params 26
abbrev ray12667 := rays 26
def bank12667 : Fin 2 → Cell := twoBank p12667 ray12667
theorem signs12667 : ∀ j, Signs p12667 (bank12667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12668 := params 27
abbrev ray12668 := rays 27
def bank12668 : Fin 2 → Cell := twoBank p12668 ray12668
theorem signs12668 : ∀ j, Signs p12668 (bank12668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12669 := params 28
abbrev ray12669 := rays 28
def bank12669 : Fin 2 → Cell := twoBank p12669 ray12669
theorem signs12669 : ∀ j, Signs p12669 (bank12669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12670 := params 29
abbrev ray12670 := rays 29
def bank12670 : Fin 2 → Cell := twoBank p12670 ray12670
theorem signs12670 : ∀ j, Signs p12670 (bank12670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12671 := params 30
abbrev ray12671 := rays 30
def bank12671 : Fin 2 → Cell := twoBank p12671 ray12671
theorem signs12671 : ∀ j, Signs p12671 (bank12671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12672 := params 31
abbrev ray12672 := rays 31
def bank12672 : Fin 2 → Cell := twoBank p12672 ray12672
theorem signs12672 : ∀ j, Signs p12672 (bank12672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12641_12672
