/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09153_09184
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97773278161793,97772928977361,97772579772099,97772230546007,97771881299086,97771532031336,97771182742758,97770833433352,97770484103120,97770134752061,97769785380177,97769435987468,97769086573934,97768737139576,97768387684395,97768038208392,97767688711567,97767339193920,97766989655453,97766640096165,97766290516058,97765940915132,97765591293388,97765241650826,97764891987447,97764542303251,97764192598239,97763842872412,97763493125771,97763143358315,97762793570046,97762443760964,97762093931070]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9152+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9153 := params 0
abbrev ray9153 := rays 0
def bank9153 : Fin 2 → Cell := twoBank p9153 ray9153
theorem signs9153 : ∀ j, Signs p9153 (bank9153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9154 := params 1
abbrev ray9154 := rays 1
def bank9154 : Fin 2 → Cell := twoBank p9154 ray9154
theorem signs9154 : ∀ j, Signs p9154 (bank9154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9155 := params 2
abbrev ray9155 := rays 2
def bank9155 : Fin 2 → Cell := twoBank p9155 ray9155
theorem signs9155 : ∀ j, Signs p9155 (bank9155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9156 := params 3
abbrev ray9156 := rays 3
def bank9156 : Fin 2 → Cell := twoBank p9156 ray9156
theorem signs9156 : ∀ j, Signs p9156 (bank9156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9157 := params 4
abbrev ray9157 := rays 4
def bank9157 : Fin 2 → Cell := twoBank p9157 ray9157
theorem signs9157 : ∀ j, Signs p9157 (bank9157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9158 := params 5
abbrev ray9158 := rays 5
def bank9158 : Fin 2 → Cell := twoBank p9158 ray9158
theorem signs9158 : ∀ j, Signs p9158 (bank9158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9159 := params 6
abbrev ray9159 := rays 6
def bank9159 : Fin 2 → Cell := twoBank p9159 ray9159
theorem signs9159 : ∀ j, Signs p9159 (bank9159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9160 := params 7
abbrev ray9160 := rays 7
def bank9160 : Fin 2 → Cell := twoBank p9160 ray9160
theorem signs9160 : ∀ j, Signs p9160 (bank9160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9161 := params 8
abbrev ray9161 := rays 8
def bank9161 : Fin 2 → Cell := twoBank p9161 ray9161
theorem signs9161 : ∀ j, Signs p9161 (bank9161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9162 := params 9
abbrev ray9162 := rays 9
def bank9162 : Fin 2 → Cell := twoBank p9162 ray9162
theorem signs9162 : ∀ j, Signs p9162 (bank9162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9163 := params 10
abbrev ray9163 := rays 10
def bank9163 : Fin 2 → Cell := twoBank p9163 ray9163
theorem signs9163 : ∀ j, Signs p9163 (bank9163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9164 := params 11
abbrev ray9164 := rays 11
def bank9164 : Fin 2 → Cell := twoBank p9164 ray9164
theorem signs9164 : ∀ j, Signs p9164 (bank9164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9165 := params 12
abbrev ray9165 := rays 12
def bank9165 : Fin 2 → Cell := twoBank p9165 ray9165
theorem signs9165 : ∀ j, Signs p9165 (bank9165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9166 := params 13
abbrev ray9166 := rays 13
def bank9166 : Fin 2 → Cell := twoBank p9166 ray9166
theorem signs9166 : ∀ j, Signs p9166 (bank9166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9167 := params 14
abbrev ray9167 := rays 14
def bank9167 : Fin 2 → Cell := twoBank p9167 ray9167
theorem signs9167 : ∀ j, Signs p9167 (bank9167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9168 := params 15
abbrev ray9168 := rays 15
def bank9168 : Fin 2 → Cell := twoBank p9168 ray9168
theorem signs9168 : ∀ j, Signs p9168 (bank9168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9169 := params 16
abbrev ray9169 := rays 16
def bank9169 : Fin 2 → Cell := twoBank p9169 ray9169
theorem signs9169 : ∀ j, Signs p9169 (bank9169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9170 := params 17
abbrev ray9170 := rays 17
def bank9170 : Fin 2 → Cell := twoBank p9170 ray9170
theorem signs9170 : ∀ j, Signs p9170 (bank9170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9171 := params 18
abbrev ray9171 := rays 18
def bank9171 : Fin 2 → Cell := twoBank p9171 ray9171
theorem signs9171 : ∀ j, Signs p9171 (bank9171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9172 := params 19
abbrev ray9172 := rays 19
def bank9172 : Fin 2 → Cell := twoBank p9172 ray9172
theorem signs9172 : ∀ j, Signs p9172 (bank9172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9173 := params 20
abbrev ray9173 := rays 20
def bank9173 : Fin 2 → Cell := twoBank p9173 ray9173
theorem signs9173 : ∀ j, Signs p9173 (bank9173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9174 := params 21
abbrev ray9174 := rays 21
def bank9174 : Fin 2 → Cell := twoBank p9174 ray9174
theorem signs9174 : ∀ j, Signs p9174 (bank9174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9175 := params 22
abbrev ray9175 := rays 22
def bank9175 : Fin 2 → Cell := twoBank p9175 ray9175
theorem signs9175 : ∀ j, Signs p9175 (bank9175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9176 := params 23
abbrev ray9176 := rays 23
def bank9176 : Fin 2 → Cell := twoBank p9176 ray9176
theorem signs9176 : ∀ j, Signs p9176 (bank9176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9177 := params 24
abbrev ray9177 := rays 24
def bank9177 : Fin 2 → Cell := twoBank p9177 ray9177
theorem signs9177 : ∀ j, Signs p9177 (bank9177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9178 := params 25
abbrev ray9178 := rays 25
def bank9178 : Fin 2 → Cell := twoBank p9178 ray9178
theorem signs9178 : ∀ j, Signs p9178 (bank9178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9179 := params 26
abbrev ray9179 := rays 26
def bank9179 : Fin 2 → Cell := twoBank p9179 ray9179
theorem signs9179 : ∀ j, Signs p9179 (bank9179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9180 := params 27
abbrev ray9180 := rays 27
def bank9180 : Fin 2 → Cell := twoBank p9180 ray9180
theorem signs9180 : ∀ j, Signs p9180 (bank9180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9181 := params 28
abbrev ray9181 := rays 28
def bank9181 : Fin 2 → Cell := twoBank p9181 ray9181
theorem signs9181 : ∀ j, Signs p9181 (bank9181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9182 := params 29
abbrev ray9182 := rays 29
def bank9182 : Fin 2 → Cell := twoBank p9182 ray9182
theorem signs9182 : ∀ j, Signs p9182 (bank9182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9183 := params 30
abbrev ray9183 := rays 30
def bank9183 : Fin 2 → Cell := twoBank p9183 ray9183
theorem signs9183 : ∀ j, Signs p9183 (bank9183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9184 := params 31
abbrev ray9184 := rays 31
def bank9184 : Fin 2 → Cell := twoBank p9184 ray9184
theorem signs9184 : ∀ j, Signs p9184 (bank9184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09153_09184
