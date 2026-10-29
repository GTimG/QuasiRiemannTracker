/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11713_11744
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96812721958051,96812321262711,96811920547889,96811519813586,96811119059802,96810718286538,96810317493794,96809916681570,96809515849867,96809114998686,96808714128027,96808313237890,96807912328276,96807511399185,96807110450618,96806709482575,96806308495057,96805907488064,96805506461596,96805105415654,96804704350239,96804303265350,96803902160989,96803501037155,96803099893850,96802698731073,96802297548825,96801896347107,96801495125919,96801093885261,96800692625134,96800291345538,96799890046474]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11712+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11713 := params 0
abbrev ray11713 := rays 0
def bank11713 : Fin 2 → Cell := twoBank p11713 ray11713
theorem signs11713 : ∀ j, Signs p11713 (bank11713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11714 := params 1
abbrev ray11714 := rays 1
def bank11714 : Fin 2 → Cell := twoBank p11714 ray11714
theorem signs11714 : ∀ j, Signs p11714 (bank11714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11715 := params 2
abbrev ray11715 := rays 2
def bank11715 : Fin 2 → Cell := twoBank p11715 ray11715
theorem signs11715 : ∀ j, Signs p11715 (bank11715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11716 := params 3
abbrev ray11716 := rays 3
def bank11716 : Fin 2 → Cell := twoBank p11716 ray11716
theorem signs11716 : ∀ j, Signs p11716 (bank11716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11717 := params 4
abbrev ray11717 := rays 4
def bank11717 : Fin 2 → Cell := twoBank p11717 ray11717
theorem signs11717 : ∀ j, Signs p11717 (bank11717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11718 := params 5
abbrev ray11718 := rays 5
def bank11718 : Fin 2 → Cell := twoBank p11718 ray11718
theorem signs11718 : ∀ j, Signs p11718 (bank11718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11719 := params 6
abbrev ray11719 := rays 6
def bank11719 : Fin 2 → Cell := twoBank p11719 ray11719
theorem signs11719 : ∀ j, Signs p11719 (bank11719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11720 := params 7
abbrev ray11720 := rays 7
def bank11720 : Fin 2 → Cell := twoBank p11720 ray11720
theorem signs11720 : ∀ j, Signs p11720 (bank11720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11721 := params 8
abbrev ray11721 := rays 8
def bank11721 : Fin 2 → Cell := twoBank p11721 ray11721
theorem signs11721 : ∀ j, Signs p11721 (bank11721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11722 := params 9
abbrev ray11722 := rays 9
def bank11722 : Fin 2 → Cell := twoBank p11722 ray11722
theorem signs11722 : ∀ j, Signs p11722 (bank11722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11723 := params 10
abbrev ray11723 := rays 10
def bank11723 : Fin 2 → Cell := twoBank p11723 ray11723
theorem signs11723 : ∀ j, Signs p11723 (bank11723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11724 := params 11
abbrev ray11724 := rays 11
def bank11724 : Fin 2 → Cell := twoBank p11724 ray11724
theorem signs11724 : ∀ j, Signs p11724 (bank11724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11725 := params 12
abbrev ray11725 := rays 12
def bank11725 : Fin 2 → Cell := twoBank p11725 ray11725
theorem signs11725 : ∀ j, Signs p11725 (bank11725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11726 := params 13
abbrev ray11726 := rays 13
def bank11726 : Fin 2 → Cell := twoBank p11726 ray11726
theorem signs11726 : ∀ j, Signs p11726 (bank11726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11727 := params 14
abbrev ray11727 := rays 14
def bank11727 : Fin 2 → Cell := twoBank p11727 ray11727
theorem signs11727 : ∀ j, Signs p11727 (bank11727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11728 := params 15
abbrev ray11728 := rays 15
def bank11728 : Fin 2 → Cell := twoBank p11728 ray11728
theorem signs11728 : ∀ j, Signs p11728 (bank11728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11729 := params 16
abbrev ray11729 := rays 16
def bank11729 : Fin 2 → Cell := twoBank p11729 ray11729
theorem signs11729 : ∀ j, Signs p11729 (bank11729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11730 := params 17
abbrev ray11730 := rays 17
def bank11730 : Fin 2 → Cell := twoBank p11730 ray11730
theorem signs11730 : ∀ j, Signs p11730 (bank11730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11731 := params 18
abbrev ray11731 := rays 18
def bank11731 : Fin 2 → Cell := twoBank p11731 ray11731
theorem signs11731 : ∀ j, Signs p11731 (bank11731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11732 := params 19
abbrev ray11732 := rays 19
def bank11732 : Fin 2 → Cell := twoBank p11732 ray11732
theorem signs11732 : ∀ j, Signs p11732 (bank11732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11733 := params 20
abbrev ray11733 := rays 20
def bank11733 : Fin 2 → Cell := twoBank p11733 ray11733
theorem signs11733 : ∀ j, Signs p11733 (bank11733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11734 := params 21
abbrev ray11734 := rays 21
def bank11734 : Fin 2 → Cell := twoBank p11734 ray11734
theorem signs11734 : ∀ j, Signs p11734 (bank11734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11735 := params 22
abbrev ray11735 := rays 22
def bank11735 : Fin 2 → Cell := twoBank p11735 ray11735
theorem signs11735 : ∀ j, Signs p11735 (bank11735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11736 := params 23
abbrev ray11736 := rays 23
def bank11736 : Fin 2 → Cell := twoBank p11736 ray11736
theorem signs11736 : ∀ j, Signs p11736 (bank11736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11737 := params 24
abbrev ray11737 := rays 24
def bank11737 : Fin 2 → Cell := twoBank p11737 ray11737
theorem signs11737 : ∀ j, Signs p11737 (bank11737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11738 := params 25
abbrev ray11738 := rays 25
def bank11738 : Fin 2 → Cell := twoBank p11738 ray11738
theorem signs11738 : ∀ j, Signs p11738 (bank11738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11739 := params 26
abbrev ray11739 := rays 26
def bank11739 : Fin 2 → Cell := twoBank p11739 ray11739
theorem signs11739 : ∀ j, Signs p11739 (bank11739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11740 := params 27
abbrev ray11740 := rays 27
def bank11740 : Fin 2 → Cell := twoBank p11740 ray11740
theorem signs11740 : ∀ j, Signs p11740 (bank11740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11741 := params 28
abbrev ray11741 := rays 28
def bank11741 : Fin 2 → Cell := twoBank p11741 ray11741
theorem signs11741 : ∀ j, Signs p11741 (bank11741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11742 := params 29
abbrev ray11742 := rays 29
def bank11742 : Fin 2 → Cell := twoBank p11742 ray11742
theorem signs11742 : ∀ j, Signs p11742 (bank11742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11743 := params 30
abbrev ray11743 := rays 30
def bank11743 : Fin 2 → Cell := twoBank p11743 ray11743
theorem signs11743 : ∀ j, Signs p11743 (bank11743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11744 := params 31
abbrev ray11744 := rays 31
def bank11744 : Fin 2 → Cell := twoBank p11744 ray11744
theorem signs11744 : ∀ j, Signs p11744 (bank11744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11713_11744
