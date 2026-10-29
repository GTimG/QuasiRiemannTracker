/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10785_10816
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97176107875031,97175725459583,97175343024212,97174960568919,97174578093704,97174195598568,97173813083511,97173430548534,97173047993637,97172665418821,97172282824086,97171900209433,97171517574862,97171134920374,97170752245970,97170369551649,97169986837413,97169604103261,97169221349195,97168838575215,97168455781321,97168072967514,97167690133794,97167307280162,97166924406618,97166541513163,97166158599797,97165775666521,97165392713336,97165009740241,97164626747238,97164243734327,97163860701508]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10784+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10785 := params 0
abbrev ray10785 := rays 0
def bank10785 : Fin 2 → Cell := twoBank p10785 ray10785
theorem signs10785 : ∀ j, Signs p10785 (bank10785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10786 := params 1
abbrev ray10786 := rays 1
def bank10786 : Fin 2 → Cell := twoBank p10786 ray10786
theorem signs10786 : ∀ j, Signs p10786 (bank10786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10787 := params 2
abbrev ray10787 := rays 2
def bank10787 : Fin 2 → Cell := twoBank p10787 ray10787
theorem signs10787 : ∀ j, Signs p10787 (bank10787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10788 := params 3
abbrev ray10788 := rays 3
def bank10788 : Fin 2 → Cell := twoBank p10788 ray10788
theorem signs10788 : ∀ j, Signs p10788 (bank10788 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10789 := params 4
abbrev ray10789 := rays 4
def bank10789 : Fin 2 → Cell := twoBank p10789 ray10789
theorem signs10789 : ∀ j, Signs p10789 (bank10789 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10790 := params 5
abbrev ray10790 := rays 5
def bank10790 : Fin 2 → Cell := twoBank p10790 ray10790
theorem signs10790 : ∀ j, Signs p10790 (bank10790 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10791 := params 6
abbrev ray10791 := rays 6
def bank10791 : Fin 2 → Cell := twoBank p10791 ray10791
theorem signs10791 : ∀ j, Signs p10791 (bank10791 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10792 := params 7
abbrev ray10792 := rays 7
def bank10792 : Fin 2 → Cell := twoBank p10792 ray10792
theorem signs10792 : ∀ j, Signs p10792 (bank10792 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10793 := params 8
abbrev ray10793 := rays 8
def bank10793 : Fin 2 → Cell := twoBank p10793 ray10793
theorem signs10793 : ∀ j, Signs p10793 (bank10793 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10794 := params 9
abbrev ray10794 := rays 9
def bank10794 : Fin 2 → Cell := twoBank p10794 ray10794
theorem signs10794 : ∀ j, Signs p10794 (bank10794 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10795 := params 10
abbrev ray10795 := rays 10
def bank10795 : Fin 2 → Cell := twoBank p10795 ray10795
theorem signs10795 : ∀ j, Signs p10795 (bank10795 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10796 := params 11
abbrev ray10796 := rays 11
def bank10796 : Fin 2 → Cell := twoBank p10796 ray10796
theorem signs10796 : ∀ j, Signs p10796 (bank10796 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10797 := params 12
abbrev ray10797 := rays 12
def bank10797 : Fin 2 → Cell := twoBank p10797 ray10797
theorem signs10797 : ∀ j, Signs p10797 (bank10797 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10798 := params 13
abbrev ray10798 := rays 13
def bank10798 : Fin 2 → Cell := twoBank p10798 ray10798
theorem signs10798 : ∀ j, Signs p10798 (bank10798 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10799 := params 14
abbrev ray10799 := rays 14
def bank10799 : Fin 2 → Cell := twoBank p10799 ray10799
theorem signs10799 : ∀ j, Signs p10799 (bank10799 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10800 := params 15
abbrev ray10800 := rays 15
def bank10800 : Fin 2 → Cell := twoBank p10800 ray10800
theorem signs10800 : ∀ j, Signs p10800 (bank10800 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10801 := params 16
abbrev ray10801 := rays 16
def bank10801 : Fin 2 → Cell := twoBank p10801 ray10801
theorem signs10801 : ∀ j, Signs p10801 (bank10801 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10802 := params 17
abbrev ray10802 := rays 17
def bank10802 : Fin 2 → Cell := twoBank p10802 ray10802
theorem signs10802 : ∀ j, Signs p10802 (bank10802 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10803 := params 18
abbrev ray10803 := rays 18
def bank10803 : Fin 2 → Cell := twoBank p10803 ray10803
theorem signs10803 : ∀ j, Signs p10803 (bank10803 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10804 := params 19
abbrev ray10804 := rays 19
def bank10804 : Fin 2 → Cell := twoBank p10804 ray10804
theorem signs10804 : ∀ j, Signs p10804 (bank10804 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10805 := params 20
abbrev ray10805 := rays 20
def bank10805 : Fin 2 → Cell := twoBank p10805 ray10805
theorem signs10805 : ∀ j, Signs p10805 (bank10805 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10806 := params 21
abbrev ray10806 := rays 21
def bank10806 : Fin 2 → Cell := twoBank p10806 ray10806
theorem signs10806 : ∀ j, Signs p10806 (bank10806 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10807 := params 22
abbrev ray10807 := rays 22
def bank10807 : Fin 2 → Cell := twoBank p10807 ray10807
theorem signs10807 : ∀ j, Signs p10807 (bank10807 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10808 := params 23
abbrev ray10808 := rays 23
def bank10808 : Fin 2 → Cell := twoBank p10808 ray10808
theorem signs10808 : ∀ j, Signs p10808 (bank10808 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10809 := params 24
abbrev ray10809 := rays 24
def bank10809 : Fin 2 → Cell := twoBank p10809 ray10809
theorem signs10809 : ∀ j, Signs p10809 (bank10809 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10810 := params 25
abbrev ray10810 := rays 25
def bank10810 : Fin 2 → Cell := twoBank p10810 ray10810
theorem signs10810 : ∀ j, Signs p10810 (bank10810 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10811 := params 26
abbrev ray10811 := rays 26
def bank10811 : Fin 2 → Cell := twoBank p10811 ray10811
theorem signs10811 : ∀ j, Signs p10811 (bank10811 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10812 := params 27
abbrev ray10812 := rays 27
def bank10812 : Fin 2 → Cell := twoBank p10812 ray10812
theorem signs10812 : ∀ j, Signs p10812 (bank10812 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10813 := params 28
abbrev ray10813 := rays 28
def bank10813 : Fin 2 → Cell := twoBank p10813 ray10813
theorem signs10813 : ∀ j, Signs p10813 (bank10813 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10814 := params 29
abbrev ray10814 := rays 29
def bank10814 : Fin 2 → Cell := twoBank p10814 ray10814
theorem signs10814 : ∀ j, Signs p10814 (bank10814 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10815 := params 30
abbrev ray10815 := rays 30
def bank10815 : Fin 2 → Cell := twoBank p10815 ray10815
theorem signs10815 : ∀ j, Signs p10815 (bank10815 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10816 := params 31
abbrev ray10816 := rays 31
def bank10816 : Fin 2 → Cell := twoBank p10816 ray10816
theorem signs10816 : ∀ j, Signs p10816 (bank10816 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10785_10816
