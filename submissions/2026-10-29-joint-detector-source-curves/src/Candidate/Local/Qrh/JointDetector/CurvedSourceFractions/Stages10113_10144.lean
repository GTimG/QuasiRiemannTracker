/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10113_10144
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97428559865256,97428190954870,97427822024209,97427453073273,97427084102063,97426715110580,97426346098824,97425977066795,97425608014494,97425238941922,97424869849079,97424500735966,97424131602583,97423762448931,97423393275011,97423024080822,97422654866366,97422285631643,97421916376654,97421547101399,97421177805878,97420808490092,97420439154042,97420069797728,97419700421151,97419331024312,97418961607211,97418592169848,97418222712224,97417853234340,97417483736196,97417114217792,97416744679130]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10112+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10113 := params 0
abbrev ray10113 := rays 0
def bank10113 : Fin 2 → Cell := twoBank p10113 ray10113
theorem signs10113 : ∀ j, Signs p10113 (bank10113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10114 := params 1
abbrev ray10114 := rays 1
def bank10114 : Fin 2 → Cell := twoBank p10114 ray10114
theorem signs10114 : ∀ j, Signs p10114 (bank10114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10115 := params 2
abbrev ray10115 := rays 2
def bank10115 : Fin 2 → Cell := twoBank p10115 ray10115
theorem signs10115 : ∀ j, Signs p10115 (bank10115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10116 := params 3
abbrev ray10116 := rays 3
def bank10116 : Fin 2 → Cell := twoBank p10116 ray10116
theorem signs10116 : ∀ j, Signs p10116 (bank10116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10117 := params 4
abbrev ray10117 := rays 4
def bank10117 : Fin 2 → Cell := twoBank p10117 ray10117
theorem signs10117 : ∀ j, Signs p10117 (bank10117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10118 := params 5
abbrev ray10118 := rays 5
def bank10118 : Fin 2 → Cell := twoBank p10118 ray10118
theorem signs10118 : ∀ j, Signs p10118 (bank10118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10119 := params 6
abbrev ray10119 := rays 6
def bank10119 : Fin 2 → Cell := twoBank p10119 ray10119
theorem signs10119 : ∀ j, Signs p10119 (bank10119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10120 := params 7
abbrev ray10120 := rays 7
def bank10120 : Fin 2 → Cell := twoBank p10120 ray10120
theorem signs10120 : ∀ j, Signs p10120 (bank10120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10121 := params 8
abbrev ray10121 := rays 8
def bank10121 : Fin 2 → Cell := twoBank p10121 ray10121
theorem signs10121 : ∀ j, Signs p10121 (bank10121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10122 := params 9
abbrev ray10122 := rays 9
def bank10122 : Fin 2 → Cell := twoBank p10122 ray10122
theorem signs10122 : ∀ j, Signs p10122 (bank10122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10123 := params 10
abbrev ray10123 := rays 10
def bank10123 : Fin 2 → Cell := twoBank p10123 ray10123
theorem signs10123 : ∀ j, Signs p10123 (bank10123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10124 := params 11
abbrev ray10124 := rays 11
def bank10124 : Fin 2 → Cell := twoBank p10124 ray10124
theorem signs10124 : ∀ j, Signs p10124 (bank10124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10125 := params 12
abbrev ray10125 := rays 12
def bank10125 : Fin 2 → Cell := twoBank p10125 ray10125
theorem signs10125 : ∀ j, Signs p10125 (bank10125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10126 := params 13
abbrev ray10126 := rays 13
def bank10126 : Fin 2 → Cell := twoBank p10126 ray10126
theorem signs10126 : ∀ j, Signs p10126 (bank10126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10127 := params 14
abbrev ray10127 := rays 14
def bank10127 : Fin 2 → Cell := twoBank p10127 ray10127
theorem signs10127 : ∀ j, Signs p10127 (bank10127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10128 := params 15
abbrev ray10128 := rays 15
def bank10128 : Fin 2 → Cell := twoBank p10128 ray10128
theorem signs10128 : ∀ j, Signs p10128 (bank10128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10129 := params 16
abbrev ray10129 := rays 16
def bank10129 : Fin 2 → Cell := twoBank p10129 ray10129
theorem signs10129 : ∀ j, Signs p10129 (bank10129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10130 := params 17
abbrev ray10130 := rays 17
def bank10130 : Fin 2 → Cell := twoBank p10130 ray10130
theorem signs10130 : ∀ j, Signs p10130 (bank10130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10131 := params 18
abbrev ray10131 := rays 18
def bank10131 : Fin 2 → Cell := twoBank p10131 ray10131
theorem signs10131 : ∀ j, Signs p10131 (bank10131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10132 := params 19
abbrev ray10132 := rays 19
def bank10132 : Fin 2 → Cell := twoBank p10132 ray10132
theorem signs10132 : ∀ j, Signs p10132 (bank10132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10133 := params 20
abbrev ray10133 := rays 20
def bank10133 : Fin 2 → Cell := twoBank p10133 ray10133
theorem signs10133 : ∀ j, Signs p10133 (bank10133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10134 := params 21
abbrev ray10134 := rays 21
def bank10134 : Fin 2 → Cell := twoBank p10134 ray10134
theorem signs10134 : ∀ j, Signs p10134 (bank10134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10135 := params 22
abbrev ray10135 := rays 22
def bank10135 : Fin 2 → Cell := twoBank p10135 ray10135
theorem signs10135 : ∀ j, Signs p10135 (bank10135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10136 := params 23
abbrev ray10136 := rays 23
def bank10136 : Fin 2 → Cell := twoBank p10136 ray10136
theorem signs10136 : ∀ j, Signs p10136 (bank10136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10137 := params 24
abbrev ray10137 := rays 24
def bank10137 : Fin 2 → Cell := twoBank p10137 ray10137
theorem signs10137 : ∀ j, Signs p10137 (bank10137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10138 := params 25
abbrev ray10138 := rays 25
def bank10138 : Fin 2 → Cell := twoBank p10138 ray10138
theorem signs10138 : ∀ j, Signs p10138 (bank10138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10139 := params 26
abbrev ray10139 := rays 26
def bank10139 : Fin 2 → Cell := twoBank p10139 ray10139
theorem signs10139 : ∀ j, Signs p10139 (bank10139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10140 := params 27
abbrev ray10140 := rays 27
def bank10140 : Fin 2 → Cell := twoBank p10140 ray10140
theorem signs10140 : ∀ j, Signs p10140 (bank10140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10141 := params 28
abbrev ray10141 := rays 28
def bank10141 : Fin 2 → Cell := twoBank p10141 ray10141
theorem signs10141 : ∀ j, Signs p10141 (bank10141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10142 := params 29
abbrev ray10142 := rays 29
def bank10142 : Fin 2 → Cell := twoBank p10142 ray10142
theorem signs10142 : ∀ j, Signs p10142 (bank10142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10143 := params 30
abbrev ray10143 := rays 30
def bank10143 : Fin 2 → Cell := twoBank p10143 ray10143
theorem signs10143 : ∀ j, Signs p10143 (bank10143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10144 := params 31
abbrev ray10144 := rays 31
def bank10144 : Fin 2 → Cell := twoBank p10144 ray10144
theorem signs10144 : ∀ j, Signs p10144 (bank10144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10113_10144
