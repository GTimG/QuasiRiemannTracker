/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09761_09792
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97557152619478,97556790880360,97556429120770,97556067340709,97555705540178,97555343719177,97554981877707,97554620015768,97554258133361,97553896230487,97553534307146,97553172363338,97552810399065,97552448414326,97552086409123,97551724383456,97551362337325,97551000270731,97550638183675,97550276076157,97549913948178,97549551799738,97549189630838,97548827441478,97548465231659,97548103001382,97547740750647,97547378479455,97547016187806,97546653875701,97546291543140,97545929190124,97545566816654]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9760+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9761 := params 0
abbrev ray9761 := rays 0
def bank9761 : Fin 2 → Cell := twoBank p9761 ray9761
theorem signs9761 : ∀ j, Signs p9761 (bank9761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9762 := params 1
abbrev ray9762 := rays 1
def bank9762 : Fin 2 → Cell := twoBank p9762 ray9762
theorem signs9762 : ∀ j, Signs p9762 (bank9762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9763 := params 2
abbrev ray9763 := rays 2
def bank9763 : Fin 2 → Cell := twoBank p9763 ray9763
theorem signs9763 : ∀ j, Signs p9763 (bank9763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9764 := params 3
abbrev ray9764 := rays 3
def bank9764 : Fin 2 → Cell := twoBank p9764 ray9764
theorem signs9764 : ∀ j, Signs p9764 (bank9764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9765 := params 4
abbrev ray9765 := rays 4
def bank9765 : Fin 2 → Cell := twoBank p9765 ray9765
theorem signs9765 : ∀ j, Signs p9765 (bank9765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9766 := params 5
abbrev ray9766 := rays 5
def bank9766 : Fin 2 → Cell := twoBank p9766 ray9766
theorem signs9766 : ∀ j, Signs p9766 (bank9766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9767 := params 6
abbrev ray9767 := rays 6
def bank9767 : Fin 2 → Cell := twoBank p9767 ray9767
theorem signs9767 : ∀ j, Signs p9767 (bank9767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9768 := params 7
abbrev ray9768 := rays 7
def bank9768 : Fin 2 → Cell := twoBank p9768 ray9768
theorem signs9768 : ∀ j, Signs p9768 (bank9768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9769 := params 8
abbrev ray9769 := rays 8
def bank9769 : Fin 2 → Cell := twoBank p9769 ray9769
theorem signs9769 : ∀ j, Signs p9769 (bank9769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9770 := params 9
abbrev ray9770 := rays 9
def bank9770 : Fin 2 → Cell := twoBank p9770 ray9770
theorem signs9770 : ∀ j, Signs p9770 (bank9770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9771 := params 10
abbrev ray9771 := rays 10
def bank9771 : Fin 2 → Cell := twoBank p9771 ray9771
theorem signs9771 : ∀ j, Signs p9771 (bank9771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9772 := params 11
abbrev ray9772 := rays 11
def bank9772 : Fin 2 → Cell := twoBank p9772 ray9772
theorem signs9772 : ∀ j, Signs p9772 (bank9772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9773 := params 12
abbrev ray9773 := rays 12
def bank9773 : Fin 2 → Cell := twoBank p9773 ray9773
theorem signs9773 : ∀ j, Signs p9773 (bank9773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9774 := params 13
abbrev ray9774 := rays 13
def bank9774 : Fin 2 → Cell := twoBank p9774 ray9774
theorem signs9774 : ∀ j, Signs p9774 (bank9774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9775 := params 14
abbrev ray9775 := rays 14
def bank9775 : Fin 2 → Cell := twoBank p9775 ray9775
theorem signs9775 : ∀ j, Signs p9775 (bank9775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9776 := params 15
abbrev ray9776 := rays 15
def bank9776 : Fin 2 → Cell := twoBank p9776 ray9776
theorem signs9776 : ∀ j, Signs p9776 (bank9776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9777 := params 16
abbrev ray9777 := rays 16
def bank9777 : Fin 2 → Cell := twoBank p9777 ray9777
theorem signs9777 : ∀ j, Signs p9777 (bank9777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9778 := params 17
abbrev ray9778 := rays 17
def bank9778 : Fin 2 → Cell := twoBank p9778 ray9778
theorem signs9778 : ∀ j, Signs p9778 (bank9778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9779 := params 18
abbrev ray9779 := rays 18
def bank9779 : Fin 2 → Cell := twoBank p9779 ray9779
theorem signs9779 : ∀ j, Signs p9779 (bank9779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9780 := params 19
abbrev ray9780 := rays 19
def bank9780 : Fin 2 → Cell := twoBank p9780 ray9780
theorem signs9780 : ∀ j, Signs p9780 (bank9780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9781 := params 20
abbrev ray9781 := rays 20
def bank9781 : Fin 2 → Cell := twoBank p9781 ray9781
theorem signs9781 : ∀ j, Signs p9781 (bank9781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9782 := params 21
abbrev ray9782 := rays 21
def bank9782 : Fin 2 → Cell := twoBank p9782 ray9782
theorem signs9782 : ∀ j, Signs p9782 (bank9782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9783 := params 22
abbrev ray9783 := rays 22
def bank9783 : Fin 2 → Cell := twoBank p9783 ray9783
theorem signs9783 : ∀ j, Signs p9783 (bank9783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9784 := params 23
abbrev ray9784 := rays 23
def bank9784 : Fin 2 → Cell := twoBank p9784 ray9784
theorem signs9784 : ∀ j, Signs p9784 (bank9784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9785 := params 24
abbrev ray9785 := rays 24
def bank9785 : Fin 2 → Cell := twoBank p9785 ray9785
theorem signs9785 : ∀ j, Signs p9785 (bank9785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9786 := params 25
abbrev ray9786 := rays 25
def bank9786 : Fin 2 → Cell := twoBank p9786 ray9786
theorem signs9786 : ∀ j, Signs p9786 (bank9786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9787 := params 26
abbrev ray9787 := rays 26
def bank9787 : Fin 2 → Cell := twoBank p9787 ray9787
theorem signs9787 : ∀ j, Signs p9787 (bank9787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9788 := params 27
abbrev ray9788 := rays 27
def bank9788 : Fin 2 → Cell := twoBank p9788 ray9788
theorem signs9788 : ∀ j, Signs p9788 (bank9788 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9789 := params 28
abbrev ray9789 := rays 28
def bank9789 : Fin 2 → Cell := twoBank p9789 ray9789
theorem signs9789 : ∀ j, Signs p9789 (bank9789 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9790 := params 29
abbrev ray9790 := rays 29
def bank9790 : Fin 2 → Cell := twoBank p9790 ray9790
theorem signs9790 : ∀ j, Signs p9790 (bank9790 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9791 := params 30
abbrev ray9791 := rays 30
def bank9791 : Fin 2 → Cell := twoBank p9791 ray9791
theorem signs9791 : ∀ j, Signs p9791 (bank9791 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9792 := params 31
abbrev ray9792 := rays 31
def bank9792 : Fin 2 → Cell := twoBank p9792 ray9792
theorem signs9792 : ∀ j, Signs p9792 (bank9792 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09761_09792
