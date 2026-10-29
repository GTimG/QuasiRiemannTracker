/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16257_16288
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94811257588684,94810780119358,94810302634047,94809825132750,94809347615468,94808870082201,94808392532949,94807914967711,94807437386488,94806959789280,94806482176087,94806004546909,94805526901746,94805049240597,94804571563463,94804093870344,94803616161240,94803138436151,94802660695077,94802182938018,94801705164974,94801227375945,94800749570931,94800271749932,94799793912948,94799316059979,94798838191025,94798360306087,94797882405164,94797404488256,94796926555363,94796448606485,94795970641622]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16256+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16257 := params 0
abbrev ray16257 := rays 0
def bank16257 : Fin 1 → Cell := oneBank p16257 ray16257
theorem signs16257 : ∀ j, Signs p16257 (bank16257 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16258 := params 1
abbrev ray16258 := rays 1
def bank16258 : Fin 1 → Cell := oneBank p16258 ray16258
theorem signs16258 : ∀ j, Signs p16258 (bank16258 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16259 := params 2
abbrev ray16259 := rays 2
def bank16259 : Fin 1 → Cell := oneBank p16259 ray16259
theorem signs16259 : ∀ j, Signs p16259 (bank16259 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16260 := params 3
abbrev ray16260 := rays 3
def bank16260 : Fin 1 → Cell := oneBank p16260 ray16260
theorem signs16260 : ∀ j, Signs p16260 (bank16260 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16261 := params 4
abbrev ray16261 := rays 4
def bank16261 : Fin 1 → Cell := oneBank p16261 ray16261
theorem signs16261 : ∀ j, Signs p16261 (bank16261 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16262 := params 5
abbrev ray16262 := rays 5
def bank16262 : Fin 1 → Cell := oneBank p16262 ray16262
theorem signs16262 : ∀ j, Signs p16262 (bank16262 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16263 := params 6
abbrev ray16263 := rays 6
def bank16263 : Fin 1 → Cell := oneBank p16263 ray16263
theorem signs16263 : ∀ j, Signs p16263 (bank16263 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16264 := params 7
abbrev ray16264 := rays 7
def bank16264 : Fin 1 → Cell := oneBank p16264 ray16264
theorem signs16264 : ∀ j, Signs p16264 (bank16264 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16265 := params 8
abbrev ray16265 := rays 8
def bank16265 : Fin 1 → Cell := oneBank p16265 ray16265
theorem signs16265 : ∀ j, Signs p16265 (bank16265 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16266 := params 9
abbrev ray16266 := rays 9
def bank16266 : Fin 1 → Cell := oneBank p16266 ray16266
theorem signs16266 : ∀ j, Signs p16266 (bank16266 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16267 := params 10
abbrev ray16267 := rays 10
def bank16267 : Fin 1 → Cell := oneBank p16267 ray16267
theorem signs16267 : ∀ j, Signs p16267 (bank16267 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16268 := params 11
abbrev ray16268 := rays 11
def bank16268 : Fin 1 → Cell := oneBank p16268 ray16268
theorem signs16268 : ∀ j, Signs p16268 (bank16268 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16269 := params 12
abbrev ray16269 := rays 12
def bank16269 : Fin 1 → Cell := oneBank p16269 ray16269
theorem signs16269 : ∀ j, Signs p16269 (bank16269 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16270 := params 13
abbrev ray16270 := rays 13
def bank16270 : Fin 1 → Cell := oneBank p16270 ray16270
theorem signs16270 : ∀ j, Signs p16270 (bank16270 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16271 := params 14
abbrev ray16271 := rays 14
def bank16271 : Fin 1 → Cell := oneBank p16271 ray16271
theorem signs16271 : ∀ j, Signs p16271 (bank16271 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16272 := params 15
abbrev ray16272 := rays 15
def bank16272 : Fin 1 → Cell := oneBank p16272 ray16272
theorem signs16272 : ∀ j, Signs p16272 (bank16272 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16273 := params 16
abbrev ray16273 := rays 16
def bank16273 : Fin 1 → Cell := oneBank p16273 ray16273
theorem signs16273 : ∀ j, Signs p16273 (bank16273 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16274 := params 17
abbrev ray16274 := rays 17
def bank16274 : Fin 1 → Cell := oneBank p16274 ray16274
theorem signs16274 : ∀ j, Signs p16274 (bank16274 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16275 := params 18
abbrev ray16275 := rays 18
def bank16275 : Fin 1 → Cell := oneBank p16275 ray16275
theorem signs16275 : ∀ j, Signs p16275 (bank16275 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16276 := params 19
abbrev ray16276 := rays 19
def bank16276 : Fin 1 → Cell := oneBank p16276 ray16276
theorem signs16276 : ∀ j, Signs p16276 (bank16276 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16277 := params 20
abbrev ray16277 := rays 20
def bank16277 : Fin 1 → Cell := oneBank p16277 ray16277
theorem signs16277 : ∀ j, Signs p16277 (bank16277 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16278 := params 21
abbrev ray16278 := rays 21
def bank16278 : Fin 1 → Cell := oneBank p16278 ray16278
theorem signs16278 : ∀ j, Signs p16278 (bank16278 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16279 := params 22
abbrev ray16279 := rays 22
def bank16279 : Fin 1 → Cell := oneBank p16279 ray16279
theorem signs16279 : ∀ j, Signs p16279 (bank16279 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16280 := params 23
abbrev ray16280 := rays 23
def bank16280 : Fin 1 → Cell := oneBank p16280 ray16280
theorem signs16280 : ∀ j, Signs p16280 (bank16280 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16281 := params 24
abbrev ray16281 := rays 24
def bank16281 : Fin 1 → Cell := oneBank p16281 ray16281
theorem signs16281 : ∀ j, Signs p16281 (bank16281 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16282 := params 25
abbrev ray16282 := rays 25
def bank16282 : Fin 1 → Cell := oneBank p16282 ray16282
theorem signs16282 : ∀ j, Signs p16282 (bank16282 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16283 := params 26
abbrev ray16283 := rays 26
def bank16283 : Fin 1 → Cell := oneBank p16283 ray16283
theorem signs16283 : ∀ j, Signs p16283 (bank16283 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16284 := params 27
abbrev ray16284 := rays 27
def bank16284 : Fin 1 → Cell := oneBank p16284 ray16284
theorem signs16284 : ∀ j, Signs p16284 (bank16284 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16285 := params 28
abbrev ray16285 := rays 28
def bank16285 : Fin 1 → Cell := oneBank p16285 ray16285
theorem signs16285 : ∀ j, Signs p16285 (bank16285 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16286 := params 29
abbrev ray16286 := rays 29
def bank16286 : Fin 1 → Cell := oneBank p16286 ray16286
theorem signs16286 : ∀ j, Signs p16286 (bank16286 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16287 := params 30
abbrev ray16287 := rays 30
def bank16287 : Fin 1 → Cell := oneBank p16287 ray16287
theorem signs16287 : ∀ j, Signs p16287 (bank16287 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16288 := params 31
abbrev ray16288 := rays 31
def bank16288 : Fin 1 → Cell := oneBank p16288 ray16288
theorem signs16288 : ∀ j, Signs p16288 (bank16288 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16257_16288
