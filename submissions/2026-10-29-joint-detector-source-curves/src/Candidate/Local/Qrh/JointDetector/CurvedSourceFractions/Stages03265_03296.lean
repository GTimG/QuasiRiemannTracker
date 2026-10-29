/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03265_03296
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99443153259240,99442940263453,99442727241638,99442514193795,99442301119927,99442088020034,99441874894118,99441661742179,99441448564219,99441235360240,99441022130242,99440808874227,99440595592196,99440382284150,99440168950091,99439955590019,99439742203936,99439528791843,99439315353742,99439101889633,99438888399518,99438674883398,99438461341275,99438247773149,99438034179022,99437820558895,99437606912769,99437393240645,99437179542525,99436965818410,99436752068301,99436538292200,99436324490107]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3264+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3265 := params 0
abbrev ray3265 := rays 0
def bank3265 : Fin 2 → Cell := twoBank p3265 ray3265
theorem signs3265 : ∀ j, Signs p3265 (bank3265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3266 := params 1
abbrev ray3266 := rays 1
def bank3266 : Fin 2 → Cell := twoBank p3266 ray3266
theorem signs3266 : ∀ j, Signs p3266 (bank3266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3267 := params 2
abbrev ray3267 := rays 2
def bank3267 : Fin 2 → Cell := twoBank p3267 ray3267
theorem signs3267 : ∀ j, Signs p3267 (bank3267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3268 := params 3
abbrev ray3268 := rays 3
def bank3268 : Fin 2 → Cell := twoBank p3268 ray3268
theorem signs3268 : ∀ j, Signs p3268 (bank3268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3269 := params 4
abbrev ray3269 := rays 4
def bank3269 : Fin 2 → Cell := twoBank p3269 ray3269
theorem signs3269 : ∀ j, Signs p3269 (bank3269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3270 := params 5
abbrev ray3270 := rays 5
def bank3270 : Fin 2 → Cell := twoBank p3270 ray3270
theorem signs3270 : ∀ j, Signs p3270 (bank3270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3271 := params 6
abbrev ray3271 := rays 6
def bank3271 : Fin 2 → Cell := twoBank p3271 ray3271
theorem signs3271 : ∀ j, Signs p3271 (bank3271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3272 := params 7
abbrev ray3272 := rays 7
def bank3272 : Fin 2 → Cell := twoBank p3272 ray3272
theorem signs3272 : ∀ j, Signs p3272 (bank3272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3273 := params 8
abbrev ray3273 := rays 8
def bank3273 : Fin 2 → Cell := twoBank p3273 ray3273
theorem signs3273 : ∀ j, Signs p3273 (bank3273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3274 := params 9
abbrev ray3274 := rays 9
def bank3274 : Fin 2 → Cell := twoBank p3274 ray3274
theorem signs3274 : ∀ j, Signs p3274 (bank3274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3275 := params 10
abbrev ray3275 := rays 10
def bank3275 : Fin 2 → Cell := twoBank p3275 ray3275
theorem signs3275 : ∀ j, Signs p3275 (bank3275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3276 := params 11
abbrev ray3276 := rays 11
def bank3276 : Fin 2 → Cell := twoBank p3276 ray3276
theorem signs3276 : ∀ j, Signs p3276 (bank3276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3277 := params 12
abbrev ray3277 := rays 12
def bank3277 : Fin 2 → Cell := twoBank p3277 ray3277
theorem signs3277 : ∀ j, Signs p3277 (bank3277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3278 := params 13
abbrev ray3278 := rays 13
def bank3278 : Fin 2 → Cell := twoBank p3278 ray3278
theorem signs3278 : ∀ j, Signs p3278 (bank3278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3279 := params 14
abbrev ray3279 := rays 14
def bank3279 : Fin 2 → Cell := twoBank p3279 ray3279
theorem signs3279 : ∀ j, Signs p3279 (bank3279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3280 := params 15
abbrev ray3280 := rays 15
def bank3280 : Fin 2 → Cell := twoBank p3280 ray3280
theorem signs3280 : ∀ j, Signs p3280 (bank3280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3281 := params 16
abbrev ray3281 := rays 16
def bank3281 : Fin 2 → Cell := twoBank p3281 ray3281
theorem signs3281 : ∀ j, Signs p3281 (bank3281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3282 := params 17
abbrev ray3282 := rays 17
def bank3282 : Fin 2 → Cell := twoBank p3282 ray3282
theorem signs3282 : ∀ j, Signs p3282 (bank3282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3283 := params 18
abbrev ray3283 := rays 18
def bank3283 : Fin 2 → Cell := twoBank p3283 ray3283
theorem signs3283 : ∀ j, Signs p3283 (bank3283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3284 := params 19
abbrev ray3284 := rays 19
def bank3284 : Fin 2 → Cell := twoBank p3284 ray3284
theorem signs3284 : ∀ j, Signs p3284 (bank3284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3285 := params 20
abbrev ray3285 := rays 20
def bank3285 : Fin 2 → Cell := twoBank p3285 ray3285
theorem signs3285 : ∀ j, Signs p3285 (bank3285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3286 := params 21
abbrev ray3286 := rays 21
def bank3286 : Fin 2 → Cell := twoBank p3286 ray3286
theorem signs3286 : ∀ j, Signs p3286 (bank3286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3287 := params 22
abbrev ray3287 := rays 22
def bank3287 : Fin 2 → Cell := twoBank p3287 ray3287
theorem signs3287 : ∀ j, Signs p3287 (bank3287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3288 := params 23
abbrev ray3288 := rays 23
def bank3288 : Fin 2 → Cell := twoBank p3288 ray3288
theorem signs3288 : ∀ j, Signs p3288 (bank3288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3289 := params 24
abbrev ray3289 := rays 24
def bank3289 : Fin 2 → Cell := twoBank p3289 ray3289
theorem signs3289 : ∀ j, Signs p3289 (bank3289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3290 := params 25
abbrev ray3290 := rays 25
def bank3290 : Fin 2 → Cell := twoBank p3290 ray3290
theorem signs3290 : ∀ j, Signs p3290 (bank3290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3291 := params 26
abbrev ray3291 := rays 26
def bank3291 : Fin 2 → Cell := twoBank p3291 ray3291
theorem signs3291 : ∀ j, Signs p3291 (bank3291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3292 := params 27
abbrev ray3292 := rays 27
def bank3292 : Fin 2 → Cell := twoBank p3292 ray3292
theorem signs3292 : ∀ j, Signs p3292 (bank3292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3293 := params 28
abbrev ray3293 := rays 28
def bank3293 : Fin 2 → Cell := twoBank p3293 ray3293
theorem signs3293 : ∀ j, Signs p3293 (bank3293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3294 := params 29
abbrev ray3294 := rays 29
def bank3294 : Fin 2 → Cell := twoBank p3294 ray3294
theorem signs3294 : ∀ j, Signs p3294 (bank3294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3295 := params 30
abbrev ray3295 := rays 30
def bank3295 : Fin 2 → Cell := twoBank p3295 ray3295
theorem signs3295 : ∀ j, Signs p3295 (bank3295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3296 := params 31
abbrev ray3296 := rays 31
def bank3296 : Fin 2 → Cell := twoBank p3296 ray3296
theorem signs3296 : ∀ j, Signs p3296 (bank3296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03265_03296
