/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05153_05184
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98995955354480,98995695251364,98995435124296,98995174973277,98994914798308,98994654599389,98994394376522,98994134129708,98993873858947,98993613564241,98993353245591,98993092902997,98992832536461,98992572145984,98992311731566,98992051293209,98991790830913,98991530344680,98991269834510,98991009300405,98990748742365,98990488160391,98990227554485,98989966924647,98989706270879,98989445593181,98989184891554,98988924165999,98988663416518,98988402643111,98988141845779,98987881024523,98987620179344]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5152+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5153 := params 0
abbrev ray5153 := rays 0
def bank5153 : Fin 2 → Cell := twoBank p5153 ray5153
theorem signs5153 : ∀ j, Signs p5153 (bank5153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5154 := params 1
abbrev ray5154 := rays 1
def bank5154 : Fin 2 → Cell := twoBank p5154 ray5154
theorem signs5154 : ∀ j, Signs p5154 (bank5154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5155 := params 2
abbrev ray5155 := rays 2
def bank5155 : Fin 2 → Cell := twoBank p5155 ray5155
theorem signs5155 : ∀ j, Signs p5155 (bank5155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5156 := params 3
abbrev ray5156 := rays 3
def bank5156 : Fin 2 → Cell := twoBank p5156 ray5156
theorem signs5156 : ∀ j, Signs p5156 (bank5156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5157 := params 4
abbrev ray5157 := rays 4
def bank5157 : Fin 2 → Cell := twoBank p5157 ray5157
theorem signs5157 : ∀ j, Signs p5157 (bank5157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5158 := params 5
abbrev ray5158 := rays 5
def bank5158 : Fin 2 → Cell := twoBank p5158 ray5158
theorem signs5158 : ∀ j, Signs p5158 (bank5158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5159 := params 6
abbrev ray5159 := rays 6
def bank5159 : Fin 2 → Cell := twoBank p5159 ray5159
theorem signs5159 : ∀ j, Signs p5159 (bank5159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5160 := params 7
abbrev ray5160 := rays 7
def bank5160 : Fin 2 → Cell := twoBank p5160 ray5160
theorem signs5160 : ∀ j, Signs p5160 (bank5160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5161 := params 8
abbrev ray5161 := rays 8
def bank5161 : Fin 2 → Cell := twoBank p5161 ray5161
theorem signs5161 : ∀ j, Signs p5161 (bank5161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5162 := params 9
abbrev ray5162 := rays 9
def bank5162 : Fin 2 → Cell := twoBank p5162 ray5162
theorem signs5162 : ∀ j, Signs p5162 (bank5162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5163 := params 10
abbrev ray5163 := rays 10
def bank5163 : Fin 2 → Cell := twoBank p5163 ray5163
theorem signs5163 : ∀ j, Signs p5163 (bank5163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5164 := params 11
abbrev ray5164 := rays 11
def bank5164 : Fin 2 → Cell := twoBank p5164 ray5164
theorem signs5164 : ∀ j, Signs p5164 (bank5164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5165 := params 12
abbrev ray5165 := rays 12
def bank5165 : Fin 2 → Cell := twoBank p5165 ray5165
theorem signs5165 : ∀ j, Signs p5165 (bank5165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5166 := params 13
abbrev ray5166 := rays 13
def bank5166 : Fin 2 → Cell := twoBank p5166 ray5166
theorem signs5166 : ∀ j, Signs p5166 (bank5166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5167 := params 14
abbrev ray5167 := rays 14
def bank5167 : Fin 2 → Cell := twoBank p5167 ray5167
theorem signs5167 : ∀ j, Signs p5167 (bank5167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5168 := params 15
abbrev ray5168 := rays 15
def bank5168 : Fin 2 → Cell := twoBank p5168 ray5168
theorem signs5168 : ∀ j, Signs p5168 (bank5168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5169 := params 16
abbrev ray5169 := rays 16
def bank5169 : Fin 2 → Cell := twoBank p5169 ray5169
theorem signs5169 : ∀ j, Signs p5169 (bank5169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5170 := params 17
abbrev ray5170 := rays 17
def bank5170 : Fin 2 → Cell := twoBank p5170 ray5170
theorem signs5170 : ∀ j, Signs p5170 (bank5170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5171 := params 18
abbrev ray5171 := rays 18
def bank5171 : Fin 2 → Cell := twoBank p5171 ray5171
theorem signs5171 : ∀ j, Signs p5171 (bank5171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5172 := params 19
abbrev ray5172 := rays 19
def bank5172 : Fin 2 → Cell := twoBank p5172 ray5172
theorem signs5172 : ∀ j, Signs p5172 (bank5172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5173 := params 20
abbrev ray5173 := rays 20
def bank5173 : Fin 2 → Cell := twoBank p5173 ray5173
theorem signs5173 : ∀ j, Signs p5173 (bank5173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5174 := params 21
abbrev ray5174 := rays 21
def bank5174 : Fin 2 → Cell := twoBank p5174 ray5174
theorem signs5174 : ∀ j, Signs p5174 (bank5174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5175 := params 22
abbrev ray5175 := rays 22
def bank5175 : Fin 2 → Cell := twoBank p5175 ray5175
theorem signs5175 : ∀ j, Signs p5175 (bank5175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5176 := params 23
abbrev ray5176 := rays 23
def bank5176 : Fin 2 → Cell := twoBank p5176 ray5176
theorem signs5176 : ∀ j, Signs p5176 (bank5176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5177 := params 24
abbrev ray5177 := rays 24
def bank5177 : Fin 2 → Cell := twoBank p5177 ray5177
theorem signs5177 : ∀ j, Signs p5177 (bank5177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5178 := params 25
abbrev ray5178 := rays 25
def bank5178 : Fin 2 → Cell := twoBank p5178 ray5178
theorem signs5178 : ∀ j, Signs p5178 (bank5178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5179 := params 26
abbrev ray5179 := rays 26
def bank5179 : Fin 2 → Cell := twoBank p5179 ray5179
theorem signs5179 : ∀ j, Signs p5179 (bank5179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5180 := params 27
abbrev ray5180 := rays 27
def bank5180 : Fin 2 → Cell := twoBank p5180 ray5180
theorem signs5180 : ∀ j, Signs p5180 (bank5180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5181 := params 28
abbrev ray5181 := rays 28
def bank5181 : Fin 2 → Cell := twoBank p5181 ray5181
theorem signs5181 : ∀ j, Signs p5181 (bank5181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5182 := params 29
abbrev ray5182 := rays 29
def bank5182 : Fin 2 → Cell := twoBank p5182 ray5182
theorem signs5182 : ∀ j, Signs p5182 (bank5182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5183 := params 30
abbrev ray5183 := rays 30
def bank5183 : Fin 2 → Cell := twoBank p5183 ray5183
theorem signs5183 : ∀ j, Signs p5183 (bank5183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5184 := params 31
abbrev ray5184 := rays 31
def bank5184 : Fin 2 → Cell := twoBank p5184 ray5184
theorem signs5184 : ∀ j, Signs p5184 (bank5184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05153_05184
