/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05185_05216
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98987620179344,98987359310243,98987098417221,98986837500279,98986576559419,98986315594641,98986054605946,98985793593334,98985532556807,98985271496366,98985010412012,98984749303746,98984488171569,98984227015482,98983965835485,98983704631580,98983443403768,98983182152050,98982920876426,98982659576898,98982398253466,98982136906132,98981875534897,98981614139761,98981352720726,98981091277792,98980829810961,98980568320233,98980306805609,98980045267091,98979783704679,98979522118374,98979260508178]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5184+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5185 := params 0
abbrev ray5185 := rays 0
def bank5185 : Fin 2 → Cell := twoBank p5185 ray5185
theorem signs5185 : ∀ j, Signs p5185 (bank5185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5186 := params 1
abbrev ray5186 := rays 1
def bank5186 : Fin 2 → Cell := twoBank p5186 ray5186
theorem signs5186 : ∀ j, Signs p5186 (bank5186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5187 := params 2
abbrev ray5187 := rays 2
def bank5187 : Fin 2 → Cell := twoBank p5187 ray5187
theorem signs5187 : ∀ j, Signs p5187 (bank5187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5188 := params 3
abbrev ray5188 := rays 3
def bank5188 : Fin 2 → Cell := twoBank p5188 ray5188
theorem signs5188 : ∀ j, Signs p5188 (bank5188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5189 := params 4
abbrev ray5189 := rays 4
def bank5189 : Fin 2 → Cell := twoBank p5189 ray5189
theorem signs5189 : ∀ j, Signs p5189 (bank5189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5190 := params 5
abbrev ray5190 := rays 5
def bank5190 : Fin 2 → Cell := twoBank p5190 ray5190
theorem signs5190 : ∀ j, Signs p5190 (bank5190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5191 := params 6
abbrev ray5191 := rays 6
def bank5191 : Fin 2 → Cell := twoBank p5191 ray5191
theorem signs5191 : ∀ j, Signs p5191 (bank5191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5192 := params 7
abbrev ray5192 := rays 7
def bank5192 : Fin 2 → Cell := twoBank p5192 ray5192
theorem signs5192 : ∀ j, Signs p5192 (bank5192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5193 := params 8
abbrev ray5193 := rays 8
def bank5193 : Fin 2 → Cell := twoBank p5193 ray5193
theorem signs5193 : ∀ j, Signs p5193 (bank5193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5194 := params 9
abbrev ray5194 := rays 9
def bank5194 : Fin 2 → Cell := twoBank p5194 ray5194
theorem signs5194 : ∀ j, Signs p5194 (bank5194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5195 := params 10
abbrev ray5195 := rays 10
def bank5195 : Fin 2 → Cell := twoBank p5195 ray5195
theorem signs5195 : ∀ j, Signs p5195 (bank5195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5196 := params 11
abbrev ray5196 := rays 11
def bank5196 : Fin 2 → Cell := twoBank p5196 ray5196
theorem signs5196 : ∀ j, Signs p5196 (bank5196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5197 := params 12
abbrev ray5197 := rays 12
def bank5197 : Fin 2 → Cell := twoBank p5197 ray5197
theorem signs5197 : ∀ j, Signs p5197 (bank5197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5198 := params 13
abbrev ray5198 := rays 13
def bank5198 : Fin 2 → Cell := twoBank p5198 ray5198
theorem signs5198 : ∀ j, Signs p5198 (bank5198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5199 := params 14
abbrev ray5199 := rays 14
def bank5199 : Fin 2 → Cell := twoBank p5199 ray5199
theorem signs5199 : ∀ j, Signs p5199 (bank5199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5200 := params 15
abbrev ray5200 := rays 15
def bank5200 : Fin 2 → Cell := twoBank p5200 ray5200
theorem signs5200 : ∀ j, Signs p5200 (bank5200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5201 := params 16
abbrev ray5201 := rays 16
def bank5201 : Fin 2 → Cell := twoBank p5201 ray5201
theorem signs5201 : ∀ j, Signs p5201 (bank5201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5202 := params 17
abbrev ray5202 := rays 17
def bank5202 : Fin 2 → Cell := twoBank p5202 ray5202
theorem signs5202 : ∀ j, Signs p5202 (bank5202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5203 := params 18
abbrev ray5203 := rays 18
def bank5203 : Fin 2 → Cell := twoBank p5203 ray5203
theorem signs5203 : ∀ j, Signs p5203 (bank5203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5204 := params 19
abbrev ray5204 := rays 19
def bank5204 : Fin 2 → Cell := twoBank p5204 ray5204
theorem signs5204 : ∀ j, Signs p5204 (bank5204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5205 := params 20
abbrev ray5205 := rays 20
def bank5205 : Fin 2 → Cell := twoBank p5205 ray5205
theorem signs5205 : ∀ j, Signs p5205 (bank5205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5206 := params 21
abbrev ray5206 := rays 21
def bank5206 : Fin 2 → Cell := twoBank p5206 ray5206
theorem signs5206 : ∀ j, Signs p5206 (bank5206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5207 := params 22
abbrev ray5207 := rays 22
def bank5207 : Fin 2 → Cell := twoBank p5207 ray5207
theorem signs5207 : ∀ j, Signs p5207 (bank5207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5208 := params 23
abbrev ray5208 := rays 23
def bank5208 : Fin 2 → Cell := twoBank p5208 ray5208
theorem signs5208 : ∀ j, Signs p5208 (bank5208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5209 := params 24
abbrev ray5209 := rays 24
def bank5209 : Fin 2 → Cell := twoBank p5209 ray5209
theorem signs5209 : ∀ j, Signs p5209 (bank5209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5210 := params 25
abbrev ray5210 := rays 25
def bank5210 : Fin 2 → Cell := twoBank p5210 ray5210
theorem signs5210 : ∀ j, Signs p5210 (bank5210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5211 := params 26
abbrev ray5211 := rays 26
def bank5211 : Fin 2 → Cell := twoBank p5211 ray5211
theorem signs5211 : ∀ j, Signs p5211 (bank5211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5212 := params 27
abbrev ray5212 := rays 27
def bank5212 : Fin 2 → Cell := twoBank p5212 ray5212
theorem signs5212 : ∀ j, Signs p5212 (bank5212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5213 := params 28
abbrev ray5213 := rays 28
def bank5213 : Fin 2 → Cell := twoBank p5213 ray5213
theorem signs5213 : ∀ j, Signs p5213 (bank5213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5214 := params 29
abbrev ray5214 := rays 29
def bank5214 : Fin 2 → Cell := twoBank p5214 ray5214
theorem signs5214 : ∀ j, Signs p5214 (bank5214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5215 := params 30
abbrev ray5215 := rays 30
def bank5215 : Fin 2 → Cell := twoBank p5215 ray5215
theorem signs5215 : ∀ j, Signs p5215 (bank5215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5216 := params 31
abbrev ray5216 := rays 31
def bank5216 : Fin 2 → Cell := twoBank p5216 ray5216
theorem signs5216 : ∀ j, Signs p5216 (bank5216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05185_05216
