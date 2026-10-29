/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05121_05152
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99004266001580,99004006665451,99003747305338,99003487921243,99003228513166,99002969081109,99002709625072,99002450145056,99002190641063,99001931113093,99001671561147,99001411985227,99001152385333,99000892761466,99000633113627,99000373441818,99000113746039,98999854026291,98999594282575,98999334514892,98999074723243,98998814907630,98998555068053,98998295204513,98998035317011,98997775405548,98997515470125,98997255510743,98996995527403,98996735520106,98996475488852,98996215433643,98995955354480]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5120+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5121 := params 0
abbrev ray5121 := rays 0
def bank5121 : Fin 2 → Cell := twoBank p5121 ray5121
theorem signs5121 : ∀ j, Signs p5121 (bank5121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5122 := params 1
abbrev ray5122 := rays 1
def bank5122 : Fin 2 → Cell := twoBank p5122 ray5122
theorem signs5122 : ∀ j, Signs p5122 (bank5122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5123 := params 2
abbrev ray5123 := rays 2
def bank5123 : Fin 2 → Cell := twoBank p5123 ray5123
theorem signs5123 : ∀ j, Signs p5123 (bank5123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5124 := params 3
abbrev ray5124 := rays 3
def bank5124 : Fin 2 → Cell := twoBank p5124 ray5124
theorem signs5124 : ∀ j, Signs p5124 (bank5124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5125 := params 4
abbrev ray5125 := rays 4
def bank5125 : Fin 2 → Cell := twoBank p5125 ray5125
theorem signs5125 : ∀ j, Signs p5125 (bank5125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5126 := params 5
abbrev ray5126 := rays 5
def bank5126 : Fin 2 → Cell := twoBank p5126 ray5126
theorem signs5126 : ∀ j, Signs p5126 (bank5126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5127 := params 6
abbrev ray5127 := rays 6
def bank5127 : Fin 2 → Cell := twoBank p5127 ray5127
theorem signs5127 : ∀ j, Signs p5127 (bank5127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5128 := params 7
abbrev ray5128 := rays 7
def bank5128 : Fin 2 → Cell := twoBank p5128 ray5128
theorem signs5128 : ∀ j, Signs p5128 (bank5128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5129 := params 8
abbrev ray5129 := rays 8
def bank5129 : Fin 2 → Cell := twoBank p5129 ray5129
theorem signs5129 : ∀ j, Signs p5129 (bank5129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5130 := params 9
abbrev ray5130 := rays 9
def bank5130 : Fin 2 → Cell := twoBank p5130 ray5130
theorem signs5130 : ∀ j, Signs p5130 (bank5130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5131 := params 10
abbrev ray5131 := rays 10
def bank5131 : Fin 2 → Cell := twoBank p5131 ray5131
theorem signs5131 : ∀ j, Signs p5131 (bank5131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5132 := params 11
abbrev ray5132 := rays 11
def bank5132 : Fin 2 → Cell := twoBank p5132 ray5132
theorem signs5132 : ∀ j, Signs p5132 (bank5132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5133 := params 12
abbrev ray5133 := rays 12
def bank5133 : Fin 2 → Cell := twoBank p5133 ray5133
theorem signs5133 : ∀ j, Signs p5133 (bank5133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5134 := params 13
abbrev ray5134 := rays 13
def bank5134 : Fin 2 → Cell := twoBank p5134 ray5134
theorem signs5134 : ∀ j, Signs p5134 (bank5134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5135 := params 14
abbrev ray5135 := rays 14
def bank5135 : Fin 2 → Cell := twoBank p5135 ray5135
theorem signs5135 : ∀ j, Signs p5135 (bank5135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5136 := params 15
abbrev ray5136 := rays 15
def bank5136 : Fin 2 → Cell := twoBank p5136 ray5136
theorem signs5136 : ∀ j, Signs p5136 (bank5136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5137 := params 16
abbrev ray5137 := rays 16
def bank5137 : Fin 2 → Cell := twoBank p5137 ray5137
theorem signs5137 : ∀ j, Signs p5137 (bank5137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5138 := params 17
abbrev ray5138 := rays 17
def bank5138 : Fin 2 → Cell := twoBank p5138 ray5138
theorem signs5138 : ∀ j, Signs p5138 (bank5138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5139 := params 18
abbrev ray5139 := rays 18
def bank5139 : Fin 2 → Cell := twoBank p5139 ray5139
theorem signs5139 : ∀ j, Signs p5139 (bank5139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5140 := params 19
abbrev ray5140 := rays 19
def bank5140 : Fin 2 → Cell := twoBank p5140 ray5140
theorem signs5140 : ∀ j, Signs p5140 (bank5140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5141 := params 20
abbrev ray5141 := rays 20
def bank5141 : Fin 2 → Cell := twoBank p5141 ray5141
theorem signs5141 : ∀ j, Signs p5141 (bank5141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5142 := params 21
abbrev ray5142 := rays 21
def bank5142 : Fin 2 → Cell := twoBank p5142 ray5142
theorem signs5142 : ∀ j, Signs p5142 (bank5142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5143 := params 22
abbrev ray5143 := rays 22
def bank5143 : Fin 2 → Cell := twoBank p5143 ray5143
theorem signs5143 : ∀ j, Signs p5143 (bank5143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5144 := params 23
abbrev ray5144 := rays 23
def bank5144 : Fin 2 → Cell := twoBank p5144 ray5144
theorem signs5144 : ∀ j, Signs p5144 (bank5144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5145 := params 24
abbrev ray5145 := rays 24
def bank5145 : Fin 2 → Cell := twoBank p5145 ray5145
theorem signs5145 : ∀ j, Signs p5145 (bank5145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5146 := params 25
abbrev ray5146 := rays 25
def bank5146 : Fin 2 → Cell := twoBank p5146 ray5146
theorem signs5146 : ∀ j, Signs p5146 (bank5146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5147 := params 26
abbrev ray5147 := rays 26
def bank5147 : Fin 2 → Cell := twoBank p5147 ray5147
theorem signs5147 : ∀ j, Signs p5147 (bank5147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5148 := params 27
abbrev ray5148 := rays 27
def bank5148 : Fin 2 → Cell := twoBank p5148 ray5148
theorem signs5148 : ∀ j, Signs p5148 (bank5148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5149 := params 28
abbrev ray5149 := rays 28
def bank5149 : Fin 2 → Cell := twoBank p5149 ray5149
theorem signs5149 : ∀ j, Signs p5149 (bank5149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5150 := params 29
abbrev ray5150 := rays 29
def bank5150 : Fin 2 → Cell := twoBank p5150 ray5150
theorem signs5150 : ∀ j, Signs p5150 (bank5150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5151 := params 30
abbrev ray5151 := rays 30
def bank5151 : Fin 2 → Cell := twoBank p5151 ray5151
theorem signs5151 : ∀ j, Signs p5151 (bank5151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5152 := params 31
abbrev ray5152 := rays 31
def bank5152 : Fin 2 → Cell := twoBank p5152 ray5152
theorem signs5152 : ∀ j, Signs p5152 (bank5152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05121_05152
