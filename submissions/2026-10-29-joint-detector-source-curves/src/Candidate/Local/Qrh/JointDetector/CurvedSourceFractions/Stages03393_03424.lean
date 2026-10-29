/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03393_03424
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99415678659315,99415462341867,99415245998547,99415029629356,99414813234296,99414596813368,99414380366573,99414163893912,99413947395386,99413730870997,99413514320746,99413297744634,99413081142662,99412864514832,99412647861144,99412431181600,99412214476201,99411997744949,99411780987844,99411564204888,99411347396082,99411130561427,99410913700925,99410696814576,99410479902382,99410262964344,99410046000463,99409829010741,99409611995179,99409394953777,99409177886537,99408960793461,99408743674549]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3392+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3393 := params 0
abbrev ray3393 := rays 0
def bank3393 : Fin 2 → Cell := twoBank p3393 ray3393
theorem signs3393 : ∀ j, Signs p3393 (bank3393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3394 := params 1
abbrev ray3394 := rays 1
def bank3394 : Fin 2 → Cell := twoBank p3394 ray3394
theorem signs3394 : ∀ j, Signs p3394 (bank3394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3395 := params 2
abbrev ray3395 := rays 2
def bank3395 : Fin 2 → Cell := twoBank p3395 ray3395
theorem signs3395 : ∀ j, Signs p3395 (bank3395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3396 := params 3
abbrev ray3396 := rays 3
def bank3396 : Fin 2 → Cell := twoBank p3396 ray3396
theorem signs3396 : ∀ j, Signs p3396 (bank3396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3397 := params 4
abbrev ray3397 := rays 4
def bank3397 : Fin 2 → Cell := twoBank p3397 ray3397
theorem signs3397 : ∀ j, Signs p3397 (bank3397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3398 := params 5
abbrev ray3398 := rays 5
def bank3398 : Fin 2 → Cell := twoBank p3398 ray3398
theorem signs3398 : ∀ j, Signs p3398 (bank3398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3399 := params 6
abbrev ray3399 := rays 6
def bank3399 : Fin 2 → Cell := twoBank p3399 ray3399
theorem signs3399 : ∀ j, Signs p3399 (bank3399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3400 := params 7
abbrev ray3400 := rays 7
def bank3400 : Fin 2 → Cell := twoBank p3400 ray3400
theorem signs3400 : ∀ j, Signs p3400 (bank3400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3401 := params 8
abbrev ray3401 := rays 8
def bank3401 : Fin 2 → Cell := twoBank p3401 ray3401
theorem signs3401 : ∀ j, Signs p3401 (bank3401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3402 := params 9
abbrev ray3402 := rays 9
def bank3402 : Fin 2 → Cell := twoBank p3402 ray3402
theorem signs3402 : ∀ j, Signs p3402 (bank3402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3403 := params 10
abbrev ray3403 := rays 10
def bank3403 : Fin 2 → Cell := twoBank p3403 ray3403
theorem signs3403 : ∀ j, Signs p3403 (bank3403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3404 := params 11
abbrev ray3404 := rays 11
def bank3404 : Fin 2 → Cell := twoBank p3404 ray3404
theorem signs3404 : ∀ j, Signs p3404 (bank3404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3405 := params 12
abbrev ray3405 := rays 12
def bank3405 : Fin 2 → Cell := twoBank p3405 ray3405
theorem signs3405 : ∀ j, Signs p3405 (bank3405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3406 := params 13
abbrev ray3406 := rays 13
def bank3406 : Fin 2 → Cell := twoBank p3406 ray3406
theorem signs3406 : ∀ j, Signs p3406 (bank3406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3407 := params 14
abbrev ray3407 := rays 14
def bank3407 : Fin 2 → Cell := twoBank p3407 ray3407
theorem signs3407 : ∀ j, Signs p3407 (bank3407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3408 := params 15
abbrev ray3408 := rays 15
def bank3408 : Fin 2 → Cell := twoBank p3408 ray3408
theorem signs3408 : ∀ j, Signs p3408 (bank3408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3409 := params 16
abbrev ray3409 := rays 16
def bank3409 : Fin 2 → Cell := twoBank p3409 ray3409
theorem signs3409 : ∀ j, Signs p3409 (bank3409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3410 := params 17
abbrev ray3410 := rays 17
def bank3410 : Fin 2 → Cell := twoBank p3410 ray3410
theorem signs3410 : ∀ j, Signs p3410 (bank3410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3411 := params 18
abbrev ray3411 := rays 18
def bank3411 : Fin 2 → Cell := twoBank p3411 ray3411
theorem signs3411 : ∀ j, Signs p3411 (bank3411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3412 := params 19
abbrev ray3412 := rays 19
def bank3412 : Fin 2 → Cell := twoBank p3412 ray3412
theorem signs3412 : ∀ j, Signs p3412 (bank3412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3413 := params 20
abbrev ray3413 := rays 20
def bank3413 : Fin 2 → Cell := twoBank p3413 ray3413
theorem signs3413 : ∀ j, Signs p3413 (bank3413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3414 := params 21
abbrev ray3414 := rays 21
def bank3414 : Fin 2 → Cell := twoBank p3414 ray3414
theorem signs3414 : ∀ j, Signs p3414 (bank3414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3415 := params 22
abbrev ray3415 := rays 22
def bank3415 : Fin 2 → Cell := twoBank p3415 ray3415
theorem signs3415 : ∀ j, Signs p3415 (bank3415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3416 := params 23
abbrev ray3416 := rays 23
def bank3416 : Fin 2 → Cell := twoBank p3416 ray3416
theorem signs3416 : ∀ j, Signs p3416 (bank3416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3417 := params 24
abbrev ray3417 := rays 24
def bank3417 : Fin 2 → Cell := twoBank p3417 ray3417
theorem signs3417 : ∀ j, Signs p3417 (bank3417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3418 := params 25
abbrev ray3418 := rays 25
def bank3418 : Fin 2 → Cell := twoBank p3418 ray3418
theorem signs3418 : ∀ j, Signs p3418 (bank3418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3419 := params 26
abbrev ray3419 := rays 26
def bank3419 : Fin 2 → Cell := twoBank p3419 ray3419
theorem signs3419 : ∀ j, Signs p3419 (bank3419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3420 := params 27
abbrev ray3420 := rays 27
def bank3420 : Fin 2 → Cell := twoBank p3420 ray3420
theorem signs3420 : ∀ j, Signs p3420 (bank3420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3421 := params 28
abbrev ray3421 := rays 28
def bank3421 : Fin 2 → Cell := twoBank p3421 ray3421
theorem signs3421 : ∀ j, Signs p3421 (bank3421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3422 := params 29
abbrev ray3422 := rays 29
def bank3422 : Fin 2 → Cell := twoBank p3422 ray3422
theorem signs3422 : ∀ j, Signs p3422 (bank3422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3423 := params 30
abbrev ray3423 := rays 30
def bank3423 : Fin 2 → Cell := twoBank p3423 ray3423
theorem signs3423 : ∀ j, Signs p3423 (bank3423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3424 := params 31
abbrev ray3424 := rays 31
def bank3424 : Fin 2 → Cell := twoBank p3424 ray3424
theorem signs3424 : ∀ j, Signs p3424 (bank3424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03393_03424
