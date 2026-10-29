/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03329_03360
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99429469107002,99429254447880,99429039762808,99428825051788,99428610314820,99428395551906,99428180763047,99427965948245,99427751107500,99427536240814,99427321348188,99427106429623,99426891485121,99426676514683,99426461518309,99426246496002,99426031447762,99425816373590,99425601273488,99425386147457,99425170995498,99424955817613,99424740613803,99424525384068,99424310128411,99424094846832,99423879539332,99423664205913,99423448846576,99423233461322,99423018050153,99422802613069,99422587150072]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3328+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3329 := params 0
abbrev ray3329 := rays 0
def bank3329 : Fin 2 → Cell := twoBank p3329 ray3329
theorem signs3329 : ∀ j, Signs p3329 (bank3329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3330 := params 1
abbrev ray3330 := rays 1
def bank3330 : Fin 2 → Cell := twoBank p3330 ray3330
theorem signs3330 : ∀ j, Signs p3330 (bank3330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3331 := params 2
abbrev ray3331 := rays 2
def bank3331 : Fin 2 → Cell := twoBank p3331 ray3331
theorem signs3331 : ∀ j, Signs p3331 (bank3331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3332 := params 3
abbrev ray3332 := rays 3
def bank3332 : Fin 2 → Cell := twoBank p3332 ray3332
theorem signs3332 : ∀ j, Signs p3332 (bank3332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3333 := params 4
abbrev ray3333 := rays 4
def bank3333 : Fin 2 → Cell := twoBank p3333 ray3333
theorem signs3333 : ∀ j, Signs p3333 (bank3333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3334 := params 5
abbrev ray3334 := rays 5
def bank3334 : Fin 2 → Cell := twoBank p3334 ray3334
theorem signs3334 : ∀ j, Signs p3334 (bank3334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3335 := params 6
abbrev ray3335 := rays 6
def bank3335 : Fin 2 → Cell := twoBank p3335 ray3335
theorem signs3335 : ∀ j, Signs p3335 (bank3335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3336 := params 7
abbrev ray3336 := rays 7
def bank3336 : Fin 2 → Cell := twoBank p3336 ray3336
theorem signs3336 : ∀ j, Signs p3336 (bank3336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3337 := params 8
abbrev ray3337 := rays 8
def bank3337 : Fin 2 → Cell := twoBank p3337 ray3337
theorem signs3337 : ∀ j, Signs p3337 (bank3337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3338 := params 9
abbrev ray3338 := rays 9
def bank3338 : Fin 2 → Cell := twoBank p3338 ray3338
theorem signs3338 : ∀ j, Signs p3338 (bank3338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3339 := params 10
abbrev ray3339 := rays 10
def bank3339 : Fin 2 → Cell := twoBank p3339 ray3339
theorem signs3339 : ∀ j, Signs p3339 (bank3339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3340 := params 11
abbrev ray3340 := rays 11
def bank3340 : Fin 2 → Cell := twoBank p3340 ray3340
theorem signs3340 : ∀ j, Signs p3340 (bank3340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3341 := params 12
abbrev ray3341 := rays 12
def bank3341 : Fin 2 → Cell := twoBank p3341 ray3341
theorem signs3341 : ∀ j, Signs p3341 (bank3341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3342 := params 13
abbrev ray3342 := rays 13
def bank3342 : Fin 2 → Cell := twoBank p3342 ray3342
theorem signs3342 : ∀ j, Signs p3342 (bank3342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3343 := params 14
abbrev ray3343 := rays 14
def bank3343 : Fin 2 → Cell := twoBank p3343 ray3343
theorem signs3343 : ∀ j, Signs p3343 (bank3343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3344 := params 15
abbrev ray3344 := rays 15
def bank3344 : Fin 2 → Cell := twoBank p3344 ray3344
theorem signs3344 : ∀ j, Signs p3344 (bank3344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3345 := params 16
abbrev ray3345 := rays 16
def bank3345 : Fin 2 → Cell := twoBank p3345 ray3345
theorem signs3345 : ∀ j, Signs p3345 (bank3345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3346 := params 17
abbrev ray3346 := rays 17
def bank3346 : Fin 2 → Cell := twoBank p3346 ray3346
theorem signs3346 : ∀ j, Signs p3346 (bank3346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3347 := params 18
abbrev ray3347 := rays 18
def bank3347 : Fin 2 → Cell := twoBank p3347 ray3347
theorem signs3347 : ∀ j, Signs p3347 (bank3347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3348 := params 19
abbrev ray3348 := rays 19
def bank3348 : Fin 2 → Cell := twoBank p3348 ray3348
theorem signs3348 : ∀ j, Signs p3348 (bank3348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3349 := params 20
abbrev ray3349 := rays 20
def bank3349 : Fin 2 → Cell := twoBank p3349 ray3349
theorem signs3349 : ∀ j, Signs p3349 (bank3349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3350 := params 21
abbrev ray3350 := rays 21
def bank3350 : Fin 2 → Cell := twoBank p3350 ray3350
theorem signs3350 : ∀ j, Signs p3350 (bank3350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3351 := params 22
abbrev ray3351 := rays 22
def bank3351 : Fin 2 → Cell := twoBank p3351 ray3351
theorem signs3351 : ∀ j, Signs p3351 (bank3351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3352 := params 23
abbrev ray3352 := rays 23
def bank3352 : Fin 2 → Cell := twoBank p3352 ray3352
theorem signs3352 : ∀ j, Signs p3352 (bank3352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3353 := params 24
abbrev ray3353 := rays 24
def bank3353 : Fin 2 → Cell := twoBank p3353 ray3353
theorem signs3353 : ∀ j, Signs p3353 (bank3353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3354 := params 25
abbrev ray3354 := rays 25
def bank3354 : Fin 2 → Cell := twoBank p3354 ray3354
theorem signs3354 : ∀ j, Signs p3354 (bank3354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3355 := params 26
abbrev ray3355 := rays 26
def bank3355 : Fin 2 → Cell := twoBank p3355 ray3355
theorem signs3355 : ∀ j, Signs p3355 (bank3355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3356 := params 27
abbrev ray3356 := rays 27
def bank3356 : Fin 2 → Cell := twoBank p3356 ray3356
theorem signs3356 : ∀ j, Signs p3356 (bank3356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3357 := params 28
abbrev ray3357 := rays 28
def bank3357 : Fin 2 → Cell := twoBank p3357 ray3357
theorem signs3357 : ∀ j, Signs p3357 (bank3357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3358 := params 29
abbrev ray3358 := rays 29
def bank3358 : Fin 2 → Cell := twoBank p3358 ray3358
theorem signs3358 : ∀ j, Signs p3358 (bank3358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3359 := params 30
abbrev ray3359 := rays 30
def bank3359 : Fin 2 → Cell := twoBank p3359 ray3359
theorem signs3359 : ∀ j, Signs p3359 (bank3359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3360 := params 31
abbrev ray3360 := rays 31
def bank3360 : Fin 2 → Cell := twoBank p3360 ray3360
theorem signs3360 : ∀ j, Signs p3360 (bank3360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03329_03360
