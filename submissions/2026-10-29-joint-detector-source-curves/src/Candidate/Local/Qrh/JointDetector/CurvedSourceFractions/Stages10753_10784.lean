/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10753_10784
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97188334647154,97187952869499,97187571071906,97187189254374,97186807416904,97186425559497,97186043682153,97185661784873,97185279867657,97184897930506,97184515973420,97184133996399,97183751999445,97183369982557,97182987945737,97182605888984,97182223812299,97181841715683,97181459599136,97181077462659,97180695306252,97180313129916,97179930933651,97179548717458,97179166481337,97178784225289,97178401949314,97178019653413,97177637337586,97177255001834,97176872646157,97176490270556,97176107875031]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10752+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10753 := params 0
abbrev ray10753 := rays 0
def bank10753 : Fin 2 → Cell := twoBank p10753 ray10753
theorem signs10753 : ∀ j, Signs p10753 (bank10753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10754 := params 1
abbrev ray10754 := rays 1
def bank10754 : Fin 2 → Cell := twoBank p10754 ray10754
theorem signs10754 : ∀ j, Signs p10754 (bank10754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10755 := params 2
abbrev ray10755 := rays 2
def bank10755 : Fin 2 → Cell := twoBank p10755 ray10755
theorem signs10755 : ∀ j, Signs p10755 (bank10755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10756 := params 3
abbrev ray10756 := rays 3
def bank10756 : Fin 2 → Cell := twoBank p10756 ray10756
theorem signs10756 : ∀ j, Signs p10756 (bank10756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10757 := params 4
abbrev ray10757 := rays 4
def bank10757 : Fin 2 → Cell := twoBank p10757 ray10757
theorem signs10757 : ∀ j, Signs p10757 (bank10757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10758 := params 5
abbrev ray10758 := rays 5
def bank10758 : Fin 2 → Cell := twoBank p10758 ray10758
theorem signs10758 : ∀ j, Signs p10758 (bank10758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10759 := params 6
abbrev ray10759 := rays 6
def bank10759 : Fin 2 → Cell := twoBank p10759 ray10759
theorem signs10759 : ∀ j, Signs p10759 (bank10759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10760 := params 7
abbrev ray10760 := rays 7
def bank10760 : Fin 2 → Cell := twoBank p10760 ray10760
theorem signs10760 : ∀ j, Signs p10760 (bank10760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10761 := params 8
abbrev ray10761 := rays 8
def bank10761 : Fin 2 → Cell := twoBank p10761 ray10761
theorem signs10761 : ∀ j, Signs p10761 (bank10761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10762 := params 9
abbrev ray10762 := rays 9
def bank10762 : Fin 2 → Cell := twoBank p10762 ray10762
theorem signs10762 : ∀ j, Signs p10762 (bank10762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10763 := params 10
abbrev ray10763 := rays 10
def bank10763 : Fin 2 → Cell := twoBank p10763 ray10763
theorem signs10763 : ∀ j, Signs p10763 (bank10763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10764 := params 11
abbrev ray10764 := rays 11
def bank10764 : Fin 2 → Cell := twoBank p10764 ray10764
theorem signs10764 : ∀ j, Signs p10764 (bank10764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10765 := params 12
abbrev ray10765 := rays 12
def bank10765 : Fin 2 → Cell := twoBank p10765 ray10765
theorem signs10765 : ∀ j, Signs p10765 (bank10765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10766 := params 13
abbrev ray10766 := rays 13
def bank10766 : Fin 2 → Cell := twoBank p10766 ray10766
theorem signs10766 : ∀ j, Signs p10766 (bank10766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10767 := params 14
abbrev ray10767 := rays 14
def bank10767 : Fin 2 → Cell := twoBank p10767 ray10767
theorem signs10767 : ∀ j, Signs p10767 (bank10767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10768 := params 15
abbrev ray10768 := rays 15
def bank10768 : Fin 2 → Cell := twoBank p10768 ray10768
theorem signs10768 : ∀ j, Signs p10768 (bank10768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10769 := params 16
abbrev ray10769 := rays 16
def bank10769 : Fin 2 → Cell := twoBank p10769 ray10769
theorem signs10769 : ∀ j, Signs p10769 (bank10769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10770 := params 17
abbrev ray10770 := rays 17
def bank10770 : Fin 2 → Cell := twoBank p10770 ray10770
theorem signs10770 : ∀ j, Signs p10770 (bank10770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10771 := params 18
abbrev ray10771 := rays 18
def bank10771 : Fin 2 → Cell := twoBank p10771 ray10771
theorem signs10771 : ∀ j, Signs p10771 (bank10771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10772 := params 19
abbrev ray10772 := rays 19
def bank10772 : Fin 2 → Cell := twoBank p10772 ray10772
theorem signs10772 : ∀ j, Signs p10772 (bank10772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10773 := params 20
abbrev ray10773 := rays 20
def bank10773 : Fin 2 → Cell := twoBank p10773 ray10773
theorem signs10773 : ∀ j, Signs p10773 (bank10773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10774 := params 21
abbrev ray10774 := rays 21
def bank10774 : Fin 2 → Cell := twoBank p10774 ray10774
theorem signs10774 : ∀ j, Signs p10774 (bank10774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10775 := params 22
abbrev ray10775 := rays 22
def bank10775 : Fin 2 → Cell := twoBank p10775 ray10775
theorem signs10775 : ∀ j, Signs p10775 (bank10775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10776 := params 23
abbrev ray10776 := rays 23
def bank10776 : Fin 2 → Cell := twoBank p10776 ray10776
theorem signs10776 : ∀ j, Signs p10776 (bank10776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10777 := params 24
abbrev ray10777 := rays 24
def bank10777 : Fin 2 → Cell := twoBank p10777 ray10777
theorem signs10777 : ∀ j, Signs p10777 (bank10777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10778 := params 25
abbrev ray10778 := rays 25
def bank10778 : Fin 2 → Cell := twoBank p10778 ray10778
theorem signs10778 : ∀ j, Signs p10778 (bank10778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10779 := params 26
abbrev ray10779 := rays 26
def bank10779 : Fin 2 → Cell := twoBank p10779 ray10779
theorem signs10779 : ∀ j, Signs p10779 (bank10779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10780 := params 27
abbrev ray10780 := rays 27
def bank10780 : Fin 2 → Cell := twoBank p10780 ray10780
theorem signs10780 : ∀ j, Signs p10780 (bank10780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10781 := params 28
abbrev ray10781 := rays 28
def bank10781 : Fin 2 → Cell := twoBank p10781 ray10781
theorem signs10781 : ∀ j, Signs p10781 (bank10781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10782 := params 29
abbrev ray10782 := rays 29
def bank10782 : Fin 2 → Cell := twoBank p10782 ray10782
theorem signs10782 : ∀ j, Signs p10782 (bank10782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10783 := params 30
abbrev ray10783 := rays 30
def bank10783 : Fin 2 → Cell := twoBank p10783 ray10783
theorem signs10783 : ∀ j, Signs p10783 (bank10783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10784 := params 31
abbrev ray10784 := rays 31
def bank10784 : Fin 2 → Cell := twoBank p10784 ray10784
theorem signs10784 : ∀ j, Signs p10784 (bank10784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10753_10784
