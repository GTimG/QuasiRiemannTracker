/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13665_13696
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95994948565661,95994512804526,95994077027111,95993641233416,95993205423441,95992769597186,95992333754652,95991897895839,95991462020747,95991026129376,95990590221727,95990154297799,95989718357593,95989282401109,95988846428348,95988410439309,95987974433993,95987538412400,95987102374530,95986666320384,95986230249961,95985794163262,95985358060287,95984921941036,95984485805510,95984049653708,95983613485631,95983177301279,95982741100652,95982304883751,95981868650576,95981432401126,95980996135402]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13664+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13665 := params 0
abbrev ray13665 := rays 0
def bank13665 : Fin 1 → Cell := oneBank p13665 ray13665
theorem signs13665 : ∀ j, Signs p13665 (bank13665 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13666 := params 1
abbrev ray13666 := rays 1
def bank13666 : Fin 1 → Cell := oneBank p13666 ray13666
theorem signs13666 : ∀ j, Signs p13666 (bank13666 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13667 := params 2
abbrev ray13667 := rays 2
def bank13667 : Fin 1 → Cell := oneBank p13667 ray13667
theorem signs13667 : ∀ j, Signs p13667 (bank13667 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13668 := params 3
abbrev ray13668 := rays 3
def bank13668 : Fin 1 → Cell := oneBank p13668 ray13668
theorem signs13668 : ∀ j, Signs p13668 (bank13668 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13669 := params 4
abbrev ray13669 := rays 4
def bank13669 : Fin 1 → Cell := oneBank p13669 ray13669
theorem signs13669 : ∀ j, Signs p13669 (bank13669 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13670 := params 5
abbrev ray13670 := rays 5
def bank13670 : Fin 1 → Cell := oneBank p13670 ray13670
theorem signs13670 : ∀ j, Signs p13670 (bank13670 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13671 := params 6
abbrev ray13671 := rays 6
def bank13671 : Fin 1 → Cell := oneBank p13671 ray13671
theorem signs13671 : ∀ j, Signs p13671 (bank13671 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13672 := params 7
abbrev ray13672 := rays 7
def bank13672 : Fin 1 → Cell := oneBank p13672 ray13672
theorem signs13672 : ∀ j, Signs p13672 (bank13672 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13673 := params 8
abbrev ray13673 := rays 8
def bank13673 : Fin 1 → Cell := oneBank p13673 ray13673
theorem signs13673 : ∀ j, Signs p13673 (bank13673 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13674 := params 9
abbrev ray13674 := rays 9
def bank13674 : Fin 1 → Cell := oneBank p13674 ray13674
theorem signs13674 : ∀ j, Signs p13674 (bank13674 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13675 := params 10
abbrev ray13675 := rays 10
def bank13675 : Fin 1 → Cell := oneBank p13675 ray13675
theorem signs13675 : ∀ j, Signs p13675 (bank13675 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13676 := params 11
abbrev ray13676 := rays 11
def bank13676 : Fin 1 → Cell := oneBank p13676 ray13676
theorem signs13676 : ∀ j, Signs p13676 (bank13676 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13677 := params 12
abbrev ray13677 := rays 12
def bank13677 : Fin 1 → Cell := oneBank p13677 ray13677
theorem signs13677 : ∀ j, Signs p13677 (bank13677 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13678 := params 13
abbrev ray13678 := rays 13
def bank13678 : Fin 1 → Cell := oneBank p13678 ray13678
theorem signs13678 : ∀ j, Signs p13678 (bank13678 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13679 := params 14
abbrev ray13679 := rays 14
def bank13679 : Fin 1 → Cell := oneBank p13679 ray13679
theorem signs13679 : ∀ j, Signs p13679 (bank13679 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13680 := params 15
abbrev ray13680 := rays 15
def bank13680 : Fin 1 → Cell := oneBank p13680 ray13680
theorem signs13680 : ∀ j, Signs p13680 (bank13680 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13681 := params 16
abbrev ray13681 := rays 16
def bank13681 : Fin 1 → Cell := oneBank p13681 ray13681
theorem signs13681 : ∀ j, Signs p13681 (bank13681 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13682 := params 17
abbrev ray13682 := rays 17
def bank13682 : Fin 1 → Cell := oneBank p13682 ray13682
theorem signs13682 : ∀ j, Signs p13682 (bank13682 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13683 := params 18
abbrev ray13683 := rays 18
def bank13683 : Fin 1 → Cell := oneBank p13683 ray13683
theorem signs13683 : ∀ j, Signs p13683 (bank13683 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13684 := params 19
abbrev ray13684 := rays 19
def bank13684 : Fin 1 → Cell := oneBank p13684 ray13684
theorem signs13684 : ∀ j, Signs p13684 (bank13684 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13685 := params 20
abbrev ray13685 := rays 20
def bank13685 : Fin 1 → Cell := oneBank p13685 ray13685
theorem signs13685 : ∀ j, Signs p13685 (bank13685 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13686 := params 21
abbrev ray13686 := rays 21
def bank13686 : Fin 1 → Cell := oneBank p13686 ray13686
theorem signs13686 : ∀ j, Signs p13686 (bank13686 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13687 := params 22
abbrev ray13687 := rays 22
def bank13687 : Fin 1 → Cell := oneBank p13687 ray13687
theorem signs13687 : ∀ j, Signs p13687 (bank13687 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13688 := params 23
abbrev ray13688 := rays 23
def bank13688 : Fin 1 → Cell := oneBank p13688 ray13688
theorem signs13688 : ∀ j, Signs p13688 (bank13688 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13689 := params 24
abbrev ray13689 := rays 24
def bank13689 : Fin 1 → Cell := oneBank p13689 ray13689
theorem signs13689 : ∀ j, Signs p13689 (bank13689 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13690 := params 25
abbrev ray13690 := rays 25
def bank13690 : Fin 1 → Cell := oneBank p13690 ray13690
theorem signs13690 : ∀ j, Signs p13690 (bank13690 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13691 := params 26
abbrev ray13691 := rays 26
def bank13691 : Fin 1 → Cell := oneBank p13691 ray13691
theorem signs13691 : ∀ j, Signs p13691 (bank13691 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13692 := params 27
abbrev ray13692 := rays 27
def bank13692 : Fin 1 → Cell := oneBank p13692 ray13692
theorem signs13692 : ∀ j, Signs p13692 (bank13692 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13693 := params 28
abbrev ray13693 := rays 28
def bank13693 : Fin 1 → Cell := oneBank p13693 ray13693
theorem signs13693 : ∀ j, Signs p13693 (bank13693 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13694 := params 29
abbrev ray13694 := rays 29
def bank13694 : Fin 1 → Cell := oneBank p13694 ray13694
theorem signs13694 : ∀ j, Signs p13694 (bank13694 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13695 := params 30
abbrev ray13695 := rays 30
def bank13695 : Fin 1 → Cell := oneBank p13695 ray13695
theorem signs13695 : ∀ j, Signs p13695 (bank13695 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13696 := params 31
abbrev ray13696 := rays 31
def bank13696 : Fin 1 → Cell := oneBank p13696 ray13696
theorem signs13696 : ∀ j, Signs p13696 (bank13696 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13665_13696
