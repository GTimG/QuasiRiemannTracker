/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08385_08416
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98035253179675,98034920179375,98034587157752,98034254114808,98033921050543,98033587964957,98033254858052,98032921729828,98032588580285,98032255409425,98031922217248,98031589003754,98031255768944,98030922512819,98030589235380,98030255936627,98029922616561,98029589275183,98029255912493,98028922528492,98028589123181,98028255696560,98027922248630,98027588779392,98027255288847,98026921776995,98026588243836,98026254689372,98025921113603,98025587516529,98025253898152,98024920258472,98024586597489]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8384+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8385 := params 0
abbrev ray8385 := rays 0
def bank8385 : Fin 2 → Cell := twoBank p8385 ray8385
theorem signs8385 : ∀ j, Signs p8385 (bank8385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8386 := params 1
abbrev ray8386 := rays 1
def bank8386 : Fin 2 → Cell := twoBank p8386 ray8386
theorem signs8386 : ∀ j, Signs p8386 (bank8386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8387 := params 2
abbrev ray8387 := rays 2
def bank8387 : Fin 2 → Cell := twoBank p8387 ray8387
theorem signs8387 : ∀ j, Signs p8387 (bank8387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8388 := params 3
abbrev ray8388 := rays 3
def bank8388 : Fin 2 → Cell := twoBank p8388 ray8388
theorem signs8388 : ∀ j, Signs p8388 (bank8388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8389 := params 4
abbrev ray8389 := rays 4
def bank8389 : Fin 2 → Cell := twoBank p8389 ray8389
theorem signs8389 : ∀ j, Signs p8389 (bank8389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8390 := params 5
abbrev ray8390 := rays 5
def bank8390 : Fin 2 → Cell := twoBank p8390 ray8390
theorem signs8390 : ∀ j, Signs p8390 (bank8390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8391 := params 6
abbrev ray8391 := rays 6
def bank8391 : Fin 2 → Cell := twoBank p8391 ray8391
theorem signs8391 : ∀ j, Signs p8391 (bank8391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8392 := params 7
abbrev ray8392 := rays 7
def bank8392 : Fin 2 → Cell := twoBank p8392 ray8392
theorem signs8392 : ∀ j, Signs p8392 (bank8392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8393 := params 8
abbrev ray8393 := rays 8
def bank8393 : Fin 2 → Cell := twoBank p8393 ray8393
theorem signs8393 : ∀ j, Signs p8393 (bank8393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8394 := params 9
abbrev ray8394 := rays 9
def bank8394 : Fin 2 → Cell := twoBank p8394 ray8394
theorem signs8394 : ∀ j, Signs p8394 (bank8394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8395 := params 10
abbrev ray8395 := rays 10
def bank8395 : Fin 2 → Cell := twoBank p8395 ray8395
theorem signs8395 : ∀ j, Signs p8395 (bank8395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8396 := params 11
abbrev ray8396 := rays 11
def bank8396 : Fin 2 → Cell := twoBank p8396 ray8396
theorem signs8396 : ∀ j, Signs p8396 (bank8396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8397 := params 12
abbrev ray8397 := rays 12
def bank8397 : Fin 2 → Cell := twoBank p8397 ray8397
theorem signs8397 : ∀ j, Signs p8397 (bank8397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8398 := params 13
abbrev ray8398 := rays 13
def bank8398 : Fin 2 → Cell := twoBank p8398 ray8398
theorem signs8398 : ∀ j, Signs p8398 (bank8398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8399 := params 14
abbrev ray8399 := rays 14
def bank8399 : Fin 2 → Cell := twoBank p8399 ray8399
theorem signs8399 : ∀ j, Signs p8399 (bank8399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8400 := params 15
abbrev ray8400 := rays 15
def bank8400 : Fin 2 → Cell := twoBank p8400 ray8400
theorem signs8400 : ∀ j, Signs p8400 (bank8400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8401 := params 16
abbrev ray8401 := rays 16
def bank8401 : Fin 2 → Cell := twoBank p8401 ray8401
theorem signs8401 : ∀ j, Signs p8401 (bank8401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8402 := params 17
abbrev ray8402 := rays 17
def bank8402 : Fin 2 → Cell := twoBank p8402 ray8402
theorem signs8402 : ∀ j, Signs p8402 (bank8402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8403 := params 18
abbrev ray8403 := rays 18
def bank8403 : Fin 2 → Cell := twoBank p8403 ray8403
theorem signs8403 : ∀ j, Signs p8403 (bank8403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8404 := params 19
abbrev ray8404 := rays 19
def bank8404 : Fin 2 → Cell := twoBank p8404 ray8404
theorem signs8404 : ∀ j, Signs p8404 (bank8404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8405 := params 20
abbrev ray8405 := rays 20
def bank8405 : Fin 2 → Cell := twoBank p8405 ray8405
theorem signs8405 : ∀ j, Signs p8405 (bank8405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8406 := params 21
abbrev ray8406 := rays 21
def bank8406 : Fin 2 → Cell := twoBank p8406 ray8406
theorem signs8406 : ∀ j, Signs p8406 (bank8406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8407 := params 22
abbrev ray8407 := rays 22
def bank8407 : Fin 2 → Cell := twoBank p8407 ray8407
theorem signs8407 : ∀ j, Signs p8407 (bank8407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8408 := params 23
abbrev ray8408 := rays 23
def bank8408 : Fin 2 → Cell := twoBank p8408 ray8408
theorem signs8408 : ∀ j, Signs p8408 (bank8408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8409 := params 24
abbrev ray8409 := rays 24
def bank8409 : Fin 2 → Cell := twoBank p8409 ray8409
theorem signs8409 : ∀ j, Signs p8409 (bank8409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8410 := params 25
abbrev ray8410 := rays 25
def bank8410 : Fin 2 → Cell := twoBank p8410 ray8410
theorem signs8410 : ∀ j, Signs p8410 (bank8410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8411 := params 26
abbrev ray8411 := rays 26
def bank8411 : Fin 2 → Cell := twoBank p8411 ray8411
theorem signs8411 : ∀ j, Signs p8411 (bank8411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8412 := params 27
abbrev ray8412 := rays 27
def bank8412 : Fin 2 → Cell := twoBank p8412 ray8412
theorem signs8412 : ∀ j, Signs p8412 (bank8412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8413 := params 28
abbrev ray8413 := rays 28
def bank8413 : Fin 2 → Cell := twoBank p8413 ray8413
theorem signs8413 : ∀ j, Signs p8413 (bank8413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8414 := params 29
abbrev ray8414 := rays 29
def bank8414 : Fin 2 → Cell := twoBank p8414 ray8414
theorem signs8414 : ∀ j, Signs p8414 (bank8414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8415 := params 30
abbrev ray8415 := rays 30
def bank8415 : Fin 2 → Cell := twoBank p8415 ray8415
theorem signs8415 : ∀ j, Signs p8415 (bank8415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8416 := params 31
abbrev ray8416 := rays 31
def bank8416 : Fin 2 → Cell := twoBank p8416 ray8416
theorem signs8416 : ∀ j, Signs p8416 (bank8416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08385_08416
