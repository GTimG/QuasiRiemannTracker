/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10081_10112
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97440354289044,97439986027752,97439617746168,97439249444291,97438881122123,97438512779664,97438144416914,97437776033874,97437407630545,97437039206927,97436670763021,97436302298827,97435933814346,97435565309578,97435196784524,97434828239185,97434459673561,97434091087652,97433722481459,97433353854983,97432985208224,97432616541183,97432247853860,97431879146256,97431510418371,97431141670206,97430772901762,97430404113039,97430035304037,97429666474757,97429297625200,97428928755366,97428559865256]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10080+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10081 := params 0
abbrev ray10081 := rays 0
def bank10081 : Fin 2 → Cell := twoBank p10081 ray10081
theorem signs10081 : ∀ j, Signs p10081 (bank10081 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10082 := params 1
abbrev ray10082 := rays 1
def bank10082 : Fin 2 → Cell := twoBank p10082 ray10082
theorem signs10082 : ∀ j, Signs p10082 (bank10082 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10083 := params 2
abbrev ray10083 := rays 2
def bank10083 : Fin 2 → Cell := twoBank p10083 ray10083
theorem signs10083 : ∀ j, Signs p10083 (bank10083 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10084 := params 3
abbrev ray10084 := rays 3
def bank10084 : Fin 2 → Cell := twoBank p10084 ray10084
theorem signs10084 : ∀ j, Signs p10084 (bank10084 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10085 := params 4
abbrev ray10085 := rays 4
def bank10085 : Fin 2 → Cell := twoBank p10085 ray10085
theorem signs10085 : ∀ j, Signs p10085 (bank10085 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10086 := params 5
abbrev ray10086 := rays 5
def bank10086 : Fin 2 → Cell := twoBank p10086 ray10086
theorem signs10086 : ∀ j, Signs p10086 (bank10086 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10087 := params 6
abbrev ray10087 := rays 6
def bank10087 : Fin 2 → Cell := twoBank p10087 ray10087
theorem signs10087 : ∀ j, Signs p10087 (bank10087 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10088 := params 7
abbrev ray10088 := rays 7
def bank10088 : Fin 2 → Cell := twoBank p10088 ray10088
theorem signs10088 : ∀ j, Signs p10088 (bank10088 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10089 := params 8
abbrev ray10089 := rays 8
def bank10089 : Fin 2 → Cell := twoBank p10089 ray10089
theorem signs10089 : ∀ j, Signs p10089 (bank10089 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10090 := params 9
abbrev ray10090 := rays 9
def bank10090 : Fin 2 → Cell := twoBank p10090 ray10090
theorem signs10090 : ∀ j, Signs p10090 (bank10090 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10091 := params 10
abbrev ray10091 := rays 10
def bank10091 : Fin 2 → Cell := twoBank p10091 ray10091
theorem signs10091 : ∀ j, Signs p10091 (bank10091 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10092 := params 11
abbrev ray10092 := rays 11
def bank10092 : Fin 2 → Cell := twoBank p10092 ray10092
theorem signs10092 : ∀ j, Signs p10092 (bank10092 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10093 := params 12
abbrev ray10093 := rays 12
def bank10093 : Fin 2 → Cell := twoBank p10093 ray10093
theorem signs10093 : ∀ j, Signs p10093 (bank10093 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10094 := params 13
abbrev ray10094 := rays 13
def bank10094 : Fin 2 → Cell := twoBank p10094 ray10094
theorem signs10094 : ∀ j, Signs p10094 (bank10094 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10095 := params 14
abbrev ray10095 := rays 14
def bank10095 : Fin 2 → Cell := twoBank p10095 ray10095
theorem signs10095 : ∀ j, Signs p10095 (bank10095 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10096 := params 15
abbrev ray10096 := rays 15
def bank10096 : Fin 2 → Cell := twoBank p10096 ray10096
theorem signs10096 : ∀ j, Signs p10096 (bank10096 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10097 := params 16
abbrev ray10097 := rays 16
def bank10097 : Fin 2 → Cell := twoBank p10097 ray10097
theorem signs10097 : ∀ j, Signs p10097 (bank10097 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10098 := params 17
abbrev ray10098 := rays 17
def bank10098 : Fin 2 → Cell := twoBank p10098 ray10098
theorem signs10098 : ∀ j, Signs p10098 (bank10098 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10099 := params 18
abbrev ray10099 := rays 18
def bank10099 : Fin 2 → Cell := twoBank p10099 ray10099
theorem signs10099 : ∀ j, Signs p10099 (bank10099 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10100 := params 19
abbrev ray10100 := rays 19
def bank10100 : Fin 2 → Cell := twoBank p10100 ray10100
theorem signs10100 : ∀ j, Signs p10100 (bank10100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10101 := params 20
abbrev ray10101 := rays 20
def bank10101 : Fin 2 → Cell := twoBank p10101 ray10101
theorem signs10101 : ∀ j, Signs p10101 (bank10101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10102 := params 21
abbrev ray10102 := rays 21
def bank10102 : Fin 2 → Cell := twoBank p10102 ray10102
theorem signs10102 : ∀ j, Signs p10102 (bank10102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10103 := params 22
abbrev ray10103 := rays 22
def bank10103 : Fin 2 → Cell := twoBank p10103 ray10103
theorem signs10103 : ∀ j, Signs p10103 (bank10103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10104 := params 23
abbrev ray10104 := rays 23
def bank10104 : Fin 2 → Cell := twoBank p10104 ray10104
theorem signs10104 : ∀ j, Signs p10104 (bank10104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10105 := params 24
abbrev ray10105 := rays 24
def bank10105 : Fin 2 → Cell := twoBank p10105 ray10105
theorem signs10105 : ∀ j, Signs p10105 (bank10105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10106 := params 25
abbrev ray10106 := rays 25
def bank10106 : Fin 2 → Cell := twoBank p10106 ray10106
theorem signs10106 : ∀ j, Signs p10106 (bank10106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10107 := params 26
abbrev ray10107 := rays 26
def bank10107 : Fin 2 → Cell := twoBank p10107 ray10107
theorem signs10107 : ∀ j, Signs p10107 (bank10107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10108 := params 27
abbrev ray10108 := rays 27
def bank10108 : Fin 2 → Cell := twoBank p10108 ray10108
theorem signs10108 : ∀ j, Signs p10108 (bank10108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10109 := params 28
abbrev ray10109 := rays 28
def bank10109 : Fin 2 → Cell := twoBank p10109 ray10109
theorem signs10109 : ∀ j, Signs p10109 (bank10109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10110 := params 29
abbrev ray10110 := rays 29
def bank10110 : Fin 2 → Cell := twoBank p10110 ray10110
theorem signs10110 : ∀ j, Signs p10110 (bank10110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10111 := params 30
abbrev ray10111 := rays 30
def bank10111 : Fin 2 → Cell := twoBank p10111 ray10111
theorem signs10111 : ∀ j, Signs p10111 (bank10111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10112 := params 31
abbrev ray10112 := rays 31
def bank10112 : Fin 2 → Cell := twoBank p10112 ray10112
theorem signs10112 : ∀ j, Signs p10112 (bank10112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10081_10112
