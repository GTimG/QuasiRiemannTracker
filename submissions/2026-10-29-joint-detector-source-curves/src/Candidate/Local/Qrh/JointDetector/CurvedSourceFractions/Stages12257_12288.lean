/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12257_12288
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96591878074813,96591466846080,96591055598101,96590644330876,96590233044405,96589821738689,96589410413728,96588999069523,96588587706074,96588176323382,96587764921446,96587353500268,96586942059848,96586530600186,96586119121282,96585707623137,96585296105752,96584884569127,96584473013262,96584061438158,96583649843815,96583238230233,96582826597413,96582414945356,96582003274061,96581591583529,96581179873761,96580768144757,96580356396517,96579944629042,96579532842333,96579121036389,96578709211211]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12256+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12257 := params 0
abbrev ray12257 := rays 0
def bank12257 : Fin 2 → Cell := twoBank p12257 ray12257
theorem signs12257 : ∀ j, Signs p12257 (bank12257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12258 := params 1
abbrev ray12258 := rays 1
def bank12258 : Fin 2 → Cell := twoBank p12258 ray12258
theorem signs12258 : ∀ j, Signs p12258 (bank12258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12259 := params 2
abbrev ray12259 := rays 2
def bank12259 : Fin 2 → Cell := twoBank p12259 ray12259
theorem signs12259 : ∀ j, Signs p12259 (bank12259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12260 := params 3
abbrev ray12260 := rays 3
def bank12260 : Fin 2 → Cell := twoBank p12260 ray12260
theorem signs12260 : ∀ j, Signs p12260 (bank12260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12261 := params 4
abbrev ray12261 := rays 4
def bank12261 : Fin 2 → Cell := twoBank p12261 ray12261
theorem signs12261 : ∀ j, Signs p12261 (bank12261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12262 := params 5
abbrev ray12262 := rays 5
def bank12262 : Fin 2 → Cell := twoBank p12262 ray12262
theorem signs12262 : ∀ j, Signs p12262 (bank12262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12263 := params 6
abbrev ray12263 := rays 6
def bank12263 : Fin 2 → Cell := twoBank p12263 ray12263
theorem signs12263 : ∀ j, Signs p12263 (bank12263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12264 := params 7
abbrev ray12264 := rays 7
def bank12264 : Fin 2 → Cell := twoBank p12264 ray12264
theorem signs12264 : ∀ j, Signs p12264 (bank12264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12265 := params 8
abbrev ray12265 := rays 8
def bank12265 : Fin 2 → Cell := twoBank p12265 ray12265
theorem signs12265 : ∀ j, Signs p12265 (bank12265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12266 := params 9
abbrev ray12266 := rays 9
def bank12266 : Fin 2 → Cell := twoBank p12266 ray12266
theorem signs12266 : ∀ j, Signs p12266 (bank12266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12267 := params 10
abbrev ray12267 := rays 10
def bank12267 : Fin 2 → Cell := twoBank p12267 ray12267
theorem signs12267 : ∀ j, Signs p12267 (bank12267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12268 := params 11
abbrev ray12268 := rays 11
def bank12268 : Fin 2 → Cell := twoBank p12268 ray12268
theorem signs12268 : ∀ j, Signs p12268 (bank12268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12269 := params 12
abbrev ray12269 := rays 12
def bank12269 : Fin 2 → Cell := twoBank p12269 ray12269
theorem signs12269 : ∀ j, Signs p12269 (bank12269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12270 := params 13
abbrev ray12270 := rays 13
def bank12270 : Fin 2 → Cell := twoBank p12270 ray12270
theorem signs12270 : ∀ j, Signs p12270 (bank12270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12271 := params 14
abbrev ray12271 := rays 14
def bank12271 : Fin 2 → Cell := twoBank p12271 ray12271
theorem signs12271 : ∀ j, Signs p12271 (bank12271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12272 := params 15
abbrev ray12272 := rays 15
def bank12272 : Fin 2 → Cell := twoBank p12272 ray12272
theorem signs12272 : ∀ j, Signs p12272 (bank12272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12273 := params 16
abbrev ray12273 := rays 16
def bank12273 : Fin 2 → Cell := twoBank p12273 ray12273
theorem signs12273 : ∀ j, Signs p12273 (bank12273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12274 := params 17
abbrev ray12274 := rays 17
def bank12274 : Fin 2 → Cell := twoBank p12274 ray12274
theorem signs12274 : ∀ j, Signs p12274 (bank12274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12275 := params 18
abbrev ray12275 := rays 18
def bank12275 : Fin 2 → Cell := twoBank p12275 ray12275
theorem signs12275 : ∀ j, Signs p12275 (bank12275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12276 := params 19
abbrev ray12276 := rays 19
def bank12276 : Fin 2 → Cell := twoBank p12276 ray12276
theorem signs12276 : ∀ j, Signs p12276 (bank12276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12277 := params 20
abbrev ray12277 := rays 20
def bank12277 : Fin 2 → Cell := twoBank p12277 ray12277
theorem signs12277 : ∀ j, Signs p12277 (bank12277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12278 := params 21
abbrev ray12278 := rays 21
def bank12278 : Fin 2 → Cell := twoBank p12278 ray12278
theorem signs12278 : ∀ j, Signs p12278 (bank12278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12279 := params 22
abbrev ray12279 := rays 22
def bank12279 : Fin 2 → Cell := twoBank p12279 ray12279
theorem signs12279 : ∀ j, Signs p12279 (bank12279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12280 := params 23
abbrev ray12280 := rays 23
def bank12280 : Fin 2 → Cell := twoBank p12280 ray12280
theorem signs12280 : ∀ j, Signs p12280 (bank12280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12281 := params 24
abbrev ray12281 := rays 24
def bank12281 : Fin 2 → Cell := twoBank p12281 ray12281
theorem signs12281 : ∀ j, Signs p12281 (bank12281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12282 := params 25
abbrev ray12282 := rays 25
def bank12282 : Fin 2 → Cell := twoBank p12282 ray12282
theorem signs12282 : ∀ j, Signs p12282 (bank12282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12283 := params 26
abbrev ray12283 := rays 26
def bank12283 : Fin 2 → Cell := twoBank p12283 ray12283
theorem signs12283 : ∀ j, Signs p12283 (bank12283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12284 := params 27
abbrev ray12284 := rays 27
def bank12284 : Fin 2 → Cell := twoBank p12284 ray12284
theorem signs12284 : ∀ j, Signs p12284 (bank12284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12285 := params 28
abbrev ray12285 := rays 28
def bank12285 : Fin 2 → Cell := twoBank p12285 ray12285
theorem signs12285 : ∀ j, Signs p12285 (bank12285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12286 := params 29
abbrev ray12286 := rays 29
def bank12286 : Fin 2 → Cell := twoBank p12286 ray12286
theorem signs12286 : ∀ j, Signs p12286 (bank12286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12287 := params 30
abbrev ray12287 := rays 30
def bank12287 : Fin 2 → Cell := twoBank p12287 ray12287
theorem signs12287 : ∀ j, Signs p12287 (bank12287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12288 := params 31
abbrev ray12288 := rays 31
def bank12288 : Fin 2 → Cell := twoBank p12288 ray12288
theorem signs12288 : ∀ j, Signs p12288 (bank12288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12257_12288
