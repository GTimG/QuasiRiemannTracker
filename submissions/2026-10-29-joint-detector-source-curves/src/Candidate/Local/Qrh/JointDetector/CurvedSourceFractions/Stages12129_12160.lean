/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12129_12160
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96644356304449,96643947542719,96643538761689,96643129961359,96642721141730,96642312302802,96641903444575,96641494567050,96641085670227,96640676754107,96640267818690,96639858863977,96639449889968,96639040896663,96638631884063,96638222852168,96637813800979,96637404730496,96636995640720,96636586531651,96636177403289,96635768255635,96635359088689,96634949902452,96634540696924,96634131472105,96633722227996,96633312964597,96632903681909,96632494379932,96632085058667,96631675718114,96631266358273]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12128+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12129 := params 0
abbrev ray12129 := rays 0
def bank12129 : Fin 2 → Cell := twoBank p12129 ray12129
theorem signs12129 : ∀ j, Signs p12129 (bank12129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12130 := params 1
abbrev ray12130 := rays 1
def bank12130 : Fin 2 → Cell := twoBank p12130 ray12130
theorem signs12130 : ∀ j, Signs p12130 (bank12130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12131 := params 2
abbrev ray12131 := rays 2
def bank12131 : Fin 2 → Cell := twoBank p12131 ray12131
theorem signs12131 : ∀ j, Signs p12131 (bank12131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12132 := params 3
abbrev ray12132 := rays 3
def bank12132 : Fin 2 → Cell := twoBank p12132 ray12132
theorem signs12132 : ∀ j, Signs p12132 (bank12132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12133 := params 4
abbrev ray12133 := rays 4
def bank12133 : Fin 2 → Cell := twoBank p12133 ray12133
theorem signs12133 : ∀ j, Signs p12133 (bank12133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12134 := params 5
abbrev ray12134 := rays 5
def bank12134 : Fin 2 → Cell := twoBank p12134 ray12134
theorem signs12134 : ∀ j, Signs p12134 (bank12134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12135 := params 6
abbrev ray12135 := rays 6
def bank12135 : Fin 2 → Cell := twoBank p12135 ray12135
theorem signs12135 : ∀ j, Signs p12135 (bank12135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12136 := params 7
abbrev ray12136 := rays 7
def bank12136 : Fin 2 → Cell := twoBank p12136 ray12136
theorem signs12136 : ∀ j, Signs p12136 (bank12136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12137 := params 8
abbrev ray12137 := rays 8
def bank12137 : Fin 2 → Cell := twoBank p12137 ray12137
theorem signs12137 : ∀ j, Signs p12137 (bank12137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12138 := params 9
abbrev ray12138 := rays 9
def bank12138 : Fin 2 → Cell := twoBank p12138 ray12138
theorem signs12138 : ∀ j, Signs p12138 (bank12138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12139 := params 10
abbrev ray12139 := rays 10
def bank12139 : Fin 2 → Cell := twoBank p12139 ray12139
theorem signs12139 : ∀ j, Signs p12139 (bank12139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12140 := params 11
abbrev ray12140 := rays 11
def bank12140 : Fin 2 → Cell := twoBank p12140 ray12140
theorem signs12140 : ∀ j, Signs p12140 (bank12140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12141 := params 12
abbrev ray12141 := rays 12
def bank12141 : Fin 2 → Cell := twoBank p12141 ray12141
theorem signs12141 : ∀ j, Signs p12141 (bank12141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12142 := params 13
abbrev ray12142 := rays 13
def bank12142 : Fin 2 → Cell := twoBank p12142 ray12142
theorem signs12142 : ∀ j, Signs p12142 (bank12142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12143 := params 14
abbrev ray12143 := rays 14
def bank12143 : Fin 2 → Cell := twoBank p12143 ray12143
theorem signs12143 : ∀ j, Signs p12143 (bank12143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12144 := params 15
abbrev ray12144 := rays 15
def bank12144 : Fin 2 → Cell := twoBank p12144 ray12144
theorem signs12144 : ∀ j, Signs p12144 (bank12144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12145 := params 16
abbrev ray12145 := rays 16
def bank12145 : Fin 2 → Cell := twoBank p12145 ray12145
theorem signs12145 : ∀ j, Signs p12145 (bank12145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12146 := params 17
abbrev ray12146 := rays 17
def bank12146 : Fin 2 → Cell := twoBank p12146 ray12146
theorem signs12146 : ∀ j, Signs p12146 (bank12146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12147 := params 18
abbrev ray12147 := rays 18
def bank12147 : Fin 2 → Cell := twoBank p12147 ray12147
theorem signs12147 : ∀ j, Signs p12147 (bank12147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12148 := params 19
abbrev ray12148 := rays 19
def bank12148 : Fin 2 → Cell := twoBank p12148 ray12148
theorem signs12148 : ∀ j, Signs p12148 (bank12148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12149 := params 20
abbrev ray12149 := rays 20
def bank12149 : Fin 2 → Cell := twoBank p12149 ray12149
theorem signs12149 : ∀ j, Signs p12149 (bank12149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12150 := params 21
abbrev ray12150 := rays 21
def bank12150 : Fin 2 → Cell := twoBank p12150 ray12150
theorem signs12150 : ∀ j, Signs p12150 (bank12150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12151 := params 22
abbrev ray12151 := rays 22
def bank12151 : Fin 2 → Cell := twoBank p12151 ray12151
theorem signs12151 : ∀ j, Signs p12151 (bank12151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12152 := params 23
abbrev ray12152 := rays 23
def bank12152 : Fin 2 → Cell := twoBank p12152 ray12152
theorem signs12152 : ∀ j, Signs p12152 (bank12152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12153 := params 24
abbrev ray12153 := rays 24
def bank12153 : Fin 2 → Cell := twoBank p12153 ray12153
theorem signs12153 : ∀ j, Signs p12153 (bank12153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12154 := params 25
abbrev ray12154 := rays 25
def bank12154 : Fin 2 → Cell := twoBank p12154 ray12154
theorem signs12154 : ∀ j, Signs p12154 (bank12154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12155 := params 26
abbrev ray12155 := rays 26
def bank12155 : Fin 2 → Cell := twoBank p12155 ray12155
theorem signs12155 : ∀ j, Signs p12155 (bank12155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12156 := params 27
abbrev ray12156 := rays 27
def bank12156 : Fin 2 → Cell := twoBank p12156 ray12156
theorem signs12156 : ∀ j, Signs p12156 (bank12156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12157 := params 28
abbrev ray12157 := rays 28
def bank12157 : Fin 2 → Cell := twoBank p12157 ray12157
theorem signs12157 : ∀ j, Signs p12157 (bank12157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12158 := params 29
abbrev ray12158 := rays 29
def bank12158 : Fin 2 → Cell := twoBank p12158 ray12158
theorem signs12158 : ∀ j, Signs p12158 (bank12158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12159 := params 30
abbrev ray12159 := rays 30
def bank12159 : Fin 2 → Cell := twoBank p12159 ray12159
theorem signs12159 : ∀ j, Signs p12159 (bank12159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12160 := params 31
abbrev ray12160 := rays 31
def bank12160 : Fin 2 → Cell := twoBank p12160 ray12160
theorem signs12160 : ∀ j, Signs p12160 (bank12160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12129_12160
