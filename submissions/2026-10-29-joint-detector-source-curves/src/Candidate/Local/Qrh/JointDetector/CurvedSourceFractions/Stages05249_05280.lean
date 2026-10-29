/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05249_05280
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98970876372872,98970613974793,98970351552855,98970089107059,98969826637406,98969564143898,98969301626535,98969039085318,98968776520248,98968513931326,98968251318553,98967988681930,98967726021458,98967463337137,98967200628969,98966937896955,98966675141096,98966412361393,98966149557846,98965886730457,98965623879227,98965361004156,98965098105246,98964835182497,98964572235911,98964309265488,98964046271230,98963783253137,98963520211210,98963257145451,98962994055860,98962730942438,98962467805186]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5248+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5249 := params 0
abbrev ray5249 := rays 0
def bank5249 : Fin 2 → Cell := twoBank p5249 ray5249
theorem signs5249 : ∀ j, Signs p5249 (bank5249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5250 := params 1
abbrev ray5250 := rays 1
def bank5250 : Fin 2 → Cell := twoBank p5250 ray5250
theorem signs5250 : ∀ j, Signs p5250 (bank5250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5251 := params 2
abbrev ray5251 := rays 2
def bank5251 : Fin 2 → Cell := twoBank p5251 ray5251
theorem signs5251 : ∀ j, Signs p5251 (bank5251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5252 := params 3
abbrev ray5252 := rays 3
def bank5252 : Fin 2 → Cell := twoBank p5252 ray5252
theorem signs5252 : ∀ j, Signs p5252 (bank5252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5253 := params 4
abbrev ray5253 := rays 4
def bank5253 : Fin 2 → Cell := twoBank p5253 ray5253
theorem signs5253 : ∀ j, Signs p5253 (bank5253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5254 := params 5
abbrev ray5254 := rays 5
def bank5254 : Fin 2 → Cell := twoBank p5254 ray5254
theorem signs5254 : ∀ j, Signs p5254 (bank5254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5255 := params 6
abbrev ray5255 := rays 6
def bank5255 : Fin 2 → Cell := twoBank p5255 ray5255
theorem signs5255 : ∀ j, Signs p5255 (bank5255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5256 := params 7
abbrev ray5256 := rays 7
def bank5256 : Fin 2 → Cell := twoBank p5256 ray5256
theorem signs5256 : ∀ j, Signs p5256 (bank5256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5257 := params 8
abbrev ray5257 := rays 8
def bank5257 : Fin 2 → Cell := twoBank p5257 ray5257
theorem signs5257 : ∀ j, Signs p5257 (bank5257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5258 := params 9
abbrev ray5258 := rays 9
def bank5258 : Fin 2 → Cell := twoBank p5258 ray5258
theorem signs5258 : ∀ j, Signs p5258 (bank5258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5259 := params 10
abbrev ray5259 := rays 10
def bank5259 : Fin 2 → Cell := twoBank p5259 ray5259
theorem signs5259 : ∀ j, Signs p5259 (bank5259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5260 := params 11
abbrev ray5260 := rays 11
def bank5260 : Fin 2 → Cell := twoBank p5260 ray5260
theorem signs5260 : ∀ j, Signs p5260 (bank5260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5261 := params 12
abbrev ray5261 := rays 12
def bank5261 : Fin 2 → Cell := twoBank p5261 ray5261
theorem signs5261 : ∀ j, Signs p5261 (bank5261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5262 := params 13
abbrev ray5262 := rays 13
def bank5262 : Fin 2 → Cell := twoBank p5262 ray5262
theorem signs5262 : ∀ j, Signs p5262 (bank5262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5263 := params 14
abbrev ray5263 := rays 14
def bank5263 : Fin 2 → Cell := twoBank p5263 ray5263
theorem signs5263 : ∀ j, Signs p5263 (bank5263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5264 := params 15
abbrev ray5264 := rays 15
def bank5264 : Fin 2 → Cell := twoBank p5264 ray5264
theorem signs5264 : ∀ j, Signs p5264 (bank5264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5265 := params 16
abbrev ray5265 := rays 16
def bank5265 : Fin 2 → Cell := twoBank p5265 ray5265
theorem signs5265 : ∀ j, Signs p5265 (bank5265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5266 := params 17
abbrev ray5266 := rays 17
def bank5266 : Fin 2 → Cell := twoBank p5266 ray5266
theorem signs5266 : ∀ j, Signs p5266 (bank5266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5267 := params 18
abbrev ray5267 := rays 18
def bank5267 : Fin 2 → Cell := twoBank p5267 ray5267
theorem signs5267 : ∀ j, Signs p5267 (bank5267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5268 := params 19
abbrev ray5268 := rays 19
def bank5268 : Fin 2 → Cell := twoBank p5268 ray5268
theorem signs5268 : ∀ j, Signs p5268 (bank5268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5269 := params 20
abbrev ray5269 := rays 20
def bank5269 : Fin 2 → Cell := twoBank p5269 ray5269
theorem signs5269 : ∀ j, Signs p5269 (bank5269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5270 := params 21
abbrev ray5270 := rays 21
def bank5270 : Fin 2 → Cell := twoBank p5270 ray5270
theorem signs5270 : ∀ j, Signs p5270 (bank5270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5271 := params 22
abbrev ray5271 := rays 22
def bank5271 : Fin 2 → Cell := twoBank p5271 ray5271
theorem signs5271 : ∀ j, Signs p5271 (bank5271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5272 := params 23
abbrev ray5272 := rays 23
def bank5272 : Fin 2 → Cell := twoBank p5272 ray5272
theorem signs5272 : ∀ j, Signs p5272 (bank5272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5273 := params 24
abbrev ray5273 := rays 24
def bank5273 : Fin 2 → Cell := twoBank p5273 ray5273
theorem signs5273 : ∀ j, Signs p5273 (bank5273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5274 := params 25
abbrev ray5274 := rays 25
def bank5274 : Fin 2 → Cell := twoBank p5274 ray5274
theorem signs5274 : ∀ j, Signs p5274 (bank5274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5275 := params 26
abbrev ray5275 := rays 26
def bank5275 : Fin 2 → Cell := twoBank p5275 ray5275
theorem signs5275 : ∀ j, Signs p5275 (bank5275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5276 := params 27
abbrev ray5276 := rays 27
def bank5276 : Fin 2 → Cell := twoBank p5276 ray5276
theorem signs5276 : ∀ j, Signs p5276 (bank5276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5277 := params 28
abbrev ray5277 := rays 28
def bank5277 : Fin 2 → Cell := twoBank p5277 ray5277
theorem signs5277 : ∀ j, Signs p5277 (bank5277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5278 := params 29
abbrev ray5278 := rays 29
def bank5278 : Fin 2 → Cell := twoBank p5278 ray5278
theorem signs5278 : ∀ j, Signs p5278 (bank5278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5279 := params 30
abbrev ray5279 := rays 30
def bank5279 : Fin 2 → Cell := twoBank p5279 ray5279
theorem signs5279 : ∀ j, Signs p5279 (bank5279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5280 := params 31
abbrev ray5280 := rays 31
def bank5280 : Fin 2 → Cell := twoBank p5280 ray5280
theorem signs5280 : ∀ j, Signs p5280 (bank5280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05249_05280
