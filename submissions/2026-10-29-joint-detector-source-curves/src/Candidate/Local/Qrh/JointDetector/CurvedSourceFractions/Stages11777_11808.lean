/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11777_11808
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96787038199861,96786636258595,96786234297876,96785832317704,96785430318080,96785028299004,96784626260477,96784224202499,96783822125070,96783420028191,96783017911863,96782615776086,96782213620860,96781811446186,96781409252064,96781007038495,96780604805479,96780202553016,96779800281107,96779397989753,96778995678953,96778593348709,96778190999021,96777788629889,96777386241313,96776983833295,96776581405834,96776178958931,96775776492586,96775374006800,96774971501574,96774568976907,96774166432801]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11776+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11777 := params 0
abbrev ray11777 := rays 0
def bank11777 : Fin 2 → Cell := twoBank p11777 ray11777
theorem signs11777 : ∀ j, Signs p11777 (bank11777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11778 := params 1
abbrev ray11778 := rays 1
def bank11778 : Fin 2 → Cell := twoBank p11778 ray11778
theorem signs11778 : ∀ j, Signs p11778 (bank11778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11779 := params 2
abbrev ray11779 := rays 2
def bank11779 : Fin 2 → Cell := twoBank p11779 ray11779
theorem signs11779 : ∀ j, Signs p11779 (bank11779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11780 := params 3
abbrev ray11780 := rays 3
def bank11780 : Fin 2 → Cell := twoBank p11780 ray11780
theorem signs11780 : ∀ j, Signs p11780 (bank11780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11781 := params 4
abbrev ray11781 := rays 4
def bank11781 : Fin 2 → Cell := twoBank p11781 ray11781
theorem signs11781 : ∀ j, Signs p11781 (bank11781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11782 := params 5
abbrev ray11782 := rays 5
def bank11782 : Fin 2 → Cell := twoBank p11782 ray11782
theorem signs11782 : ∀ j, Signs p11782 (bank11782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11783 := params 6
abbrev ray11783 := rays 6
def bank11783 : Fin 2 → Cell := twoBank p11783 ray11783
theorem signs11783 : ∀ j, Signs p11783 (bank11783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11784 := params 7
abbrev ray11784 := rays 7
def bank11784 : Fin 2 → Cell := twoBank p11784 ray11784
theorem signs11784 : ∀ j, Signs p11784 (bank11784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11785 := params 8
abbrev ray11785 := rays 8
def bank11785 : Fin 2 → Cell := twoBank p11785 ray11785
theorem signs11785 : ∀ j, Signs p11785 (bank11785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11786 := params 9
abbrev ray11786 := rays 9
def bank11786 : Fin 2 → Cell := twoBank p11786 ray11786
theorem signs11786 : ∀ j, Signs p11786 (bank11786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11787 := params 10
abbrev ray11787 := rays 10
def bank11787 : Fin 2 → Cell := twoBank p11787 ray11787
theorem signs11787 : ∀ j, Signs p11787 (bank11787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11788 := params 11
abbrev ray11788 := rays 11
def bank11788 : Fin 2 → Cell := twoBank p11788 ray11788
theorem signs11788 : ∀ j, Signs p11788 (bank11788 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11789 := params 12
abbrev ray11789 := rays 12
def bank11789 : Fin 2 → Cell := twoBank p11789 ray11789
theorem signs11789 : ∀ j, Signs p11789 (bank11789 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11790 := params 13
abbrev ray11790 := rays 13
def bank11790 : Fin 2 → Cell := twoBank p11790 ray11790
theorem signs11790 : ∀ j, Signs p11790 (bank11790 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11791 := params 14
abbrev ray11791 := rays 14
def bank11791 : Fin 2 → Cell := twoBank p11791 ray11791
theorem signs11791 : ∀ j, Signs p11791 (bank11791 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11792 := params 15
abbrev ray11792 := rays 15
def bank11792 : Fin 2 → Cell := twoBank p11792 ray11792
theorem signs11792 : ∀ j, Signs p11792 (bank11792 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11793 := params 16
abbrev ray11793 := rays 16
def bank11793 : Fin 2 → Cell := twoBank p11793 ray11793
theorem signs11793 : ∀ j, Signs p11793 (bank11793 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11794 := params 17
abbrev ray11794 := rays 17
def bank11794 : Fin 2 → Cell := twoBank p11794 ray11794
theorem signs11794 : ∀ j, Signs p11794 (bank11794 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11795 := params 18
abbrev ray11795 := rays 18
def bank11795 : Fin 2 → Cell := twoBank p11795 ray11795
theorem signs11795 : ∀ j, Signs p11795 (bank11795 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11796 := params 19
abbrev ray11796 := rays 19
def bank11796 : Fin 2 → Cell := twoBank p11796 ray11796
theorem signs11796 : ∀ j, Signs p11796 (bank11796 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11797 := params 20
abbrev ray11797 := rays 20
def bank11797 : Fin 2 → Cell := twoBank p11797 ray11797
theorem signs11797 : ∀ j, Signs p11797 (bank11797 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11798 := params 21
abbrev ray11798 := rays 21
def bank11798 : Fin 2 → Cell := twoBank p11798 ray11798
theorem signs11798 : ∀ j, Signs p11798 (bank11798 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11799 := params 22
abbrev ray11799 := rays 22
def bank11799 : Fin 2 → Cell := twoBank p11799 ray11799
theorem signs11799 : ∀ j, Signs p11799 (bank11799 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11800 := params 23
abbrev ray11800 := rays 23
def bank11800 : Fin 2 → Cell := twoBank p11800 ray11800
theorem signs11800 : ∀ j, Signs p11800 (bank11800 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11801 := params 24
abbrev ray11801 := rays 24
def bank11801 : Fin 2 → Cell := twoBank p11801 ray11801
theorem signs11801 : ∀ j, Signs p11801 (bank11801 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11802 := params 25
abbrev ray11802 := rays 25
def bank11802 : Fin 2 → Cell := twoBank p11802 ray11802
theorem signs11802 : ∀ j, Signs p11802 (bank11802 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11803 := params 26
abbrev ray11803 := rays 26
def bank11803 : Fin 2 → Cell := twoBank p11803 ray11803
theorem signs11803 : ∀ j, Signs p11803 (bank11803 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11804 := params 27
abbrev ray11804 := rays 27
def bank11804 : Fin 2 → Cell := twoBank p11804 ray11804
theorem signs11804 : ∀ j, Signs p11804 (bank11804 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11805 := params 28
abbrev ray11805 := rays 28
def bank11805 : Fin 2 → Cell := twoBank p11805 ray11805
theorem signs11805 : ∀ j, Signs p11805 (bank11805 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11806 := params 29
abbrev ray11806 := rays 29
def bank11806 : Fin 2 → Cell := twoBank p11806 ray11806
theorem signs11806 : ∀ j, Signs p11806 (bank11806 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11807 := params 30
abbrev ray11807 := rays 30
def bank11807 : Fin 2 → Cell := twoBank p11807 ray11807
theorem signs11807 : ∀ j, Signs p11807 (bank11807 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11808 := params 31
abbrev ray11808 := rays 31
def bank11808 : Fin 2 → Cell := twoBank p11808 ray11808
theorem signs11808 : ∀ j, Signs p11808 (bank11808 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11777_11808
