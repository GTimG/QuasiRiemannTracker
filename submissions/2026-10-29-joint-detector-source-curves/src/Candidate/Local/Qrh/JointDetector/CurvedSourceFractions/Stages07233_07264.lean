/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07233_07264
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98404531770235,98404223798620,98403915804857,98403607788947,98403299750891,98402991690689,98402683608342,98402375503851,98402067377216,98401759228439,98401451057520,98401142864460,98400834649260,98400526411920,98400218152441,98399909870824,98399601567070,98399293241180,98398984893154,98398676522993,98398368130698,98398059716269,98397751279708,98397442821015,98397134340191,98396825837236,98396517312152,98396208764939,98395900195598,98395591604129,98395282990534,98394974354813,98394665696967]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7232+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7233 := params 0
abbrev ray7233 := rays 0
def bank7233 : Fin 2 → Cell := twoBank p7233 ray7233
theorem signs7233 : ∀ j, Signs p7233 (bank7233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7234 := params 1
abbrev ray7234 := rays 1
def bank7234 : Fin 2 → Cell := twoBank p7234 ray7234
theorem signs7234 : ∀ j, Signs p7234 (bank7234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7235 := params 2
abbrev ray7235 := rays 2
def bank7235 : Fin 2 → Cell := twoBank p7235 ray7235
theorem signs7235 : ∀ j, Signs p7235 (bank7235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7236 := params 3
abbrev ray7236 := rays 3
def bank7236 : Fin 2 → Cell := twoBank p7236 ray7236
theorem signs7236 : ∀ j, Signs p7236 (bank7236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7237 := params 4
abbrev ray7237 := rays 4
def bank7237 : Fin 2 → Cell := twoBank p7237 ray7237
theorem signs7237 : ∀ j, Signs p7237 (bank7237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7238 := params 5
abbrev ray7238 := rays 5
def bank7238 : Fin 2 → Cell := twoBank p7238 ray7238
theorem signs7238 : ∀ j, Signs p7238 (bank7238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7239 := params 6
abbrev ray7239 := rays 6
def bank7239 : Fin 2 → Cell := twoBank p7239 ray7239
theorem signs7239 : ∀ j, Signs p7239 (bank7239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7240 := params 7
abbrev ray7240 := rays 7
def bank7240 : Fin 2 → Cell := twoBank p7240 ray7240
theorem signs7240 : ∀ j, Signs p7240 (bank7240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7241 := params 8
abbrev ray7241 := rays 8
def bank7241 : Fin 2 → Cell := twoBank p7241 ray7241
theorem signs7241 : ∀ j, Signs p7241 (bank7241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7242 := params 9
abbrev ray7242 := rays 9
def bank7242 : Fin 2 → Cell := twoBank p7242 ray7242
theorem signs7242 : ∀ j, Signs p7242 (bank7242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7243 := params 10
abbrev ray7243 := rays 10
def bank7243 : Fin 2 → Cell := twoBank p7243 ray7243
theorem signs7243 : ∀ j, Signs p7243 (bank7243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7244 := params 11
abbrev ray7244 := rays 11
def bank7244 : Fin 2 → Cell := twoBank p7244 ray7244
theorem signs7244 : ∀ j, Signs p7244 (bank7244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7245 := params 12
abbrev ray7245 := rays 12
def bank7245 : Fin 2 → Cell := twoBank p7245 ray7245
theorem signs7245 : ∀ j, Signs p7245 (bank7245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7246 := params 13
abbrev ray7246 := rays 13
def bank7246 : Fin 2 → Cell := twoBank p7246 ray7246
theorem signs7246 : ∀ j, Signs p7246 (bank7246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7247 := params 14
abbrev ray7247 := rays 14
def bank7247 : Fin 2 → Cell := twoBank p7247 ray7247
theorem signs7247 : ∀ j, Signs p7247 (bank7247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7248 := params 15
abbrev ray7248 := rays 15
def bank7248 : Fin 2 → Cell := twoBank p7248 ray7248
theorem signs7248 : ∀ j, Signs p7248 (bank7248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7249 := params 16
abbrev ray7249 := rays 16
def bank7249 : Fin 2 → Cell := twoBank p7249 ray7249
theorem signs7249 : ∀ j, Signs p7249 (bank7249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7250 := params 17
abbrev ray7250 := rays 17
def bank7250 : Fin 2 → Cell := twoBank p7250 ray7250
theorem signs7250 : ∀ j, Signs p7250 (bank7250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7251 := params 18
abbrev ray7251 := rays 18
def bank7251 : Fin 2 → Cell := twoBank p7251 ray7251
theorem signs7251 : ∀ j, Signs p7251 (bank7251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7252 := params 19
abbrev ray7252 := rays 19
def bank7252 : Fin 2 → Cell := twoBank p7252 ray7252
theorem signs7252 : ∀ j, Signs p7252 (bank7252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7253 := params 20
abbrev ray7253 := rays 20
def bank7253 : Fin 2 → Cell := twoBank p7253 ray7253
theorem signs7253 : ∀ j, Signs p7253 (bank7253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7254 := params 21
abbrev ray7254 := rays 21
def bank7254 : Fin 2 → Cell := twoBank p7254 ray7254
theorem signs7254 : ∀ j, Signs p7254 (bank7254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7255 := params 22
abbrev ray7255 := rays 22
def bank7255 : Fin 2 → Cell := twoBank p7255 ray7255
theorem signs7255 : ∀ j, Signs p7255 (bank7255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7256 := params 23
abbrev ray7256 := rays 23
def bank7256 : Fin 2 → Cell := twoBank p7256 ray7256
theorem signs7256 : ∀ j, Signs p7256 (bank7256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7257 := params 24
abbrev ray7257 := rays 24
def bank7257 : Fin 2 → Cell := twoBank p7257 ray7257
theorem signs7257 : ∀ j, Signs p7257 (bank7257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7258 := params 25
abbrev ray7258 := rays 25
def bank7258 : Fin 2 → Cell := twoBank p7258 ray7258
theorem signs7258 : ∀ j, Signs p7258 (bank7258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7259 := params 26
abbrev ray7259 := rays 26
def bank7259 : Fin 2 → Cell := twoBank p7259 ray7259
theorem signs7259 : ∀ j, Signs p7259 (bank7259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7260 := params 27
abbrev ray7260 := rays 27
def bank7260 : Fin 2 → Cell := twoBank p7260 ray7260
theorem signs7260 : ∀ j, Signs p7260 (bank7260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7261 := params 28
abbrev ray7261 := rays 28
def bank7261 : Fin 2 → Cell := twoBank p7261 ray7261
theorem signs7261 : ∀ j, Signs p7261 (bank7261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7262 := params 29
abbrev ray7262 := rays 29
def bank7262 : Fin 2 → Cell := twoBank p7262 ray7262
theorem signs7262 : ∀ j, Signs p7262 (bank7262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7263 := params 30
abbrev ray7263 := rays 30
def bank7263 : Fin 2 → Cell := twoBank p7263 ray7263
theorem signs7263 : ∀ j, Signs p7263 (bank7263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7264 := params 31
abbrev ray7264 := rays 31
def bank7264 : Fin 2 → Cell := twoBank p7264 ray7264
theorem signs7264 : ∀ j, Signs p7264 (bank7264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07233_07264
