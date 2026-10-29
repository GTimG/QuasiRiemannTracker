/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12673_12704
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96419150473350,96418731273462,96418312054496,96417892816453,96417473559333,96417054283137,96416634987865,96416215673517,96415796340094,96415376987596,96414957616023,96414538225376,96414118815655,96413699386861,96413279938994,96412860472055,96412440986044,96412021480961,96411601956807,96411182413582,96410762851286,96410343269920,96409923669484,96409504049979,96409084411405,96408664753762,96408245077051,96407825381272,96407405666426,96406985932513,96406566179533,96406146407487,96405726616375]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12672+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12673 := params 0
abbrev ray12673 := rays 0
def bank12673 : Fin 2 → Cell := twoBank p12673 ray12673
theorem signs12673 : ∀ j, Signs p12673 (bank12673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12674 := params 1
abbrev ray12674 := rays 1
def bank12674 : Fin 2 → Cell := twoBank p12674 ray12674
theorem signs12674 : ∀ j, Signs p12674 (bank12674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12675 := params 2
abbrev ray12675 := rays 2
def bank12675 : Fin 2 → Cell := twoBank p12675 ray12675
theorem signs12675 : ∀ j, Signs p12675 (bank12675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12676 := params 3
abbrev ray12676 := rays 3
def bank12676 : Fin 2 → Cell := twoBank p12676 ray12676
theorem signs12676 : ∀ j, Signs p12676 (bank12676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12677 := params 4
abbrev ray12677 := rays 4
def bank12677 : Fin 2 → Cell := twoBank p12677 ray12677
theorem signs12677 : ∀ j, Signs p12677 (bank12677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12678 := params 5
abbrev ray12678 := rays 5
def bank12678 : Fin 2 → Cell := twoBank p12678 ray12678
theorem signs12678 : ∀ j, Signs p12678 (bank12678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12679 := params 6
abbrev ray12679 := rays 6
def bank12679 : Fin 2 → Cell := twoBank p12679 ray12679
theorem signs12679 : ∀ j, Signs p12679 (bank12679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12680 := params 7
abbrev ray12680 := rays 7
def bank12680 : Fin 2 → Cell := twoBank p12680 ray12680
theorem signs12680 : ∀ j, Signs p12680 (bank12680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12681 := params 8
abbrev ray12681 := rays 8
def bank12681 : Fin 2 → Cell := twoBank p12681 ray12681
theorem signs12681 : ∀ j, Signs p12681 (bank12681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12682 := params 9
abbrev ray12682 := rays 9
def bank12682 : Fin 2 → Cell := twoBank p12682 ray12682
theorem signs12682 : ∀ j, Signs p12682 (bank12682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12683 := params 10
abbrev ray12683 := rays 10
def bank12683 : Fin 2 → Cell := twoBank p12683 ray12683
theorem signs12683 : ∀ j, Signs p12683 (bank12683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12684 := params 11
abbrev ray12684 := rays 11
def bank12684 : Fin 2 → Cell := twoBank p12684 ray12684
theorem signs12684 : ∀ j, Signs p12684 (bank12684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12685 := params 12
abbrev ray12685 := rays 12
def bank12685 : Fin 2 → Cell := twoBank p12685 ray12685
theorem signs12685 : ∀ j, Signs p12685 (bank12685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12686 := params 13
abbrev ray12686 := rays 13
def bank12686 : Fin 2 → Cell := twoBank p12686 ray12686
theorem signs12686 : ∀ j, Signs p12686 (bank12686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12687 := params 14
abbrev ray12687 := rays 14
def bank12687 : Fin 2 → Cell := twoBank p12687 ray12687
theorem signs12687 : ∀ j, Signs p12687 (bank12687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12688 := params 15
abbrev ray12688 := rays 15
def bank12688 : Fin 2 → Cell := twoBank p12688 ray12688
theorem signs12688 : ∀ j, Signs p12688 (bank12688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12689 := params 16
abbrev ray12689 := rays 16
def bank12689 : Fin 2 → Cell := twoBank p12689 ray12689
theorem signs12689 : ∀ j, Signs p12689 (bank12689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12690 := params 17
abbrev ray12690 := rays 17
def bank12690 : Fin 2 → Cell := twoBank p12690 ray12690
theorem signs12690 : ∀ j, Signs p12690 (bank12690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12691 := params 18
abbrev ray12691 := rays 18
def bank12691 : Fin 2 → Cell := twoBank p12691 ray12691
theorem signs12691 : ∀ j, Signs p12691 (bank12691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12692 := params 19
abbrev ray12692 := rays 19
def bank12692 : Fin 2 → Cell := twoBank p12692 ray12692
theorem signs12692 : ∀ j, Signs p12692 (bank12692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12693 := params 20
abbrev ray12693 := rays 20
def bank12693 : Fin 2 → Cell := twoBank p12693 ray12693
theorem signs12693 : ∀ j, Signs p12693 (bank12693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12694 := params 21
abbrev ray12694 := rays 21
def bank12694 : Fin 2 → Cell := twoBank p12694 ray12694
theorem signs12694 : ∀ j, Signs p12694 (bank12694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12695 := params 22
abbrev ray12695 := rays 22
def bank12695 : Fin 2 → Cell := twoBank p12695 ray12695
theorem signs12695 : ∀ j, Signs p12695 (bank12695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12696 := params 23
abbrev ray12696 := rays 23
def bank12696 : Fin 2 → Cell := twoBank p12696 ray12696
theorem signs12696 : ∀ j, Signs p12696 (bank12696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12697 := params 24
abbrev ray12697 := rays 24
def bank12697 : Fin 2 → Cell := twoBank p12697 ray12697
theorem signs12697 : ∀ j, Signs p12697 (bank12697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12698 := params 25
abbrev ray12698 := rays 25
def bank12698 : Fin 2 → Cell := twoBank p12698 ray12698
theorem signs12698 : ∀ j, Signs p12698 (bank12698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12699 := params 26
abbrev ray12699 := rays 26
def bank12699 : Fin 2 → Cell := twoBank p12699 ray12699
theorem signs12699 : ∀ j, Signs p12699 (bank12699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12700 := params 27
abbrev ray12700 := rays 27
def bank12700 : Fin 2 → Cell := twoBank p12700 ray12700
theorem signs12700 : ∀ j, Signs p12700 (bank12700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12701 := params 28
abbrev ray12701 := rays 28
def bank12701 : Fin 2 → Cell := twoBank p12701 ray12701
theorem signs12701 : ∀ j, Signs p12701 (bank12701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12702 := params 29
abbrev ray12702 := rays 29
def bank12702 : Fin 2 → Cell := twoBank p12702 ray12702
theorem signs12702 : ∀ j, Signs p12702 (bank12702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12703 := params 30
abbrev ray12703 := rays 30
def bank12703 : Fin 2 → Cell := twoBank p12703 ray12703
theorem signs12703 : ∀ j, Signs p12703 (bank12703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12704 := params 31
abbrev ray12704 := rays 31
def bank12704 : Fin 2 → Cell := twoBank p12704 ray12704
theorem signs12704 : ∀ j, Signs p12704 (bank12704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12673_12704
