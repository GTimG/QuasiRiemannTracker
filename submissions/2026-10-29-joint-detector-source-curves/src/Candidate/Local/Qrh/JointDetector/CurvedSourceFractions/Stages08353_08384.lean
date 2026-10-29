/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08353_08384
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98045897927059,98045565609429,98045233270455,98044900910138,98044568528478,98044236125476,98043903701133,98043571255450,98043238788427,98042906300065,98042573790364,98042241259325,98041908706949,98041576133237,98041243538189,98040910921806,98040578284089,98040245625038,98039912944654,98039580242937,98039247519889,98038914775509,98038582009799,98038249222759,98037916414390,98037583584693,98037250733668,98036917861316,98036584967638,98036252052634,98035919116305,98035586158652,98035253179675]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8352+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8353 := params 0
abbrev ray8353 := rays 0
def bank8353 : Fin 2 → Cell := twoBank p8353 ray8353
theorem signs8353 : ∀ j, Signs p8353 (bank8353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8354 := params 1
abbrev ray8354 := rays 1
def bank8354 : Fin 2 → Cell := twoBank p8354 ray8354
theorem signs8354 : ∀ j, Signs p8354 (bank8354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8355 := params 2
abbrev ray8355 := rays 2
def bank8355 : Fin 2 → Cell := twoBank p8355 ray8355
theorem signs8355 : ∀ j, Signs p8355 (bank8355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8356 := params 3
abbrev ray8356 := rays 3
def bank8356 : Fin 2 → Cell := twoBank p8356 ray8356
theorem signs8356 : ∀ j, Signs p8356 (bank8356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8357 := params 4
abbrev ray8357 := rays 4
def bank8357 : Fin 2 → Cell := twoBank p8357 ray8357
theorem signs8357 : ∀ j, Signs p8357 (bank8357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8358 := params 5
abbrev ray8358 := rays 5
def bank8358 : Fin 2 → Cell := twoBank p8358 ray8358
theorem signs8358 : ∀ j, Signs p8358 (bank8358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8359 := params 6
abbrev ray8359 := rays 6
def bank8359 : Fin 2 → Cell := twoBank p8359 ray8359
theorem signs8359 : ∀ j, Signs p8359 (bank8359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8360 := params 7
abbrev ray8360 := rays 7
def bank8360 : Fin 2 → Cell := twoBank p8360 ray8360
theorem signs8360 : ∀ j, Signs p8360 (bank8360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8361 := params 8
abbrev ray8361 := rays 8
def bank8361 : Fin 2 → Cell := twoBank p8361 ray8361
theorem signs8361 : ∀ j, Signs p8361 (bank8361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8362 := params 9
abbrev ray8362 := rays 9
def bank8362 : Fin 2 → Cell := twoBank p8362 ray8362
theorem signs8362 : ∀ j, Signs p8362 (bank8362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8363 := params 10
abbrev ray8363 := rays 10
def bank8363 : Fin 2 → Cell := twoBank p8363 ray8363
theorem signs8363 : ∀ j, Signs p8363 (bank8363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8364 := params 11
abbrev ray8364 := rays 11
def bank8364 : Fin 2 → Cell := twoBank p8364 ray8364
theorem signs8364 : ∀ j, Signs p8364 (bank8364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8365 := params 12
abbrev ray8365 := rays 12
def bank8365 : Fin 2 → Cell := twoBank p8365 ray8365
theorem signs8365 : ∀ j, Signs p8365 (bank8365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8366 := params 13
abbrev ray8366 := rays 13
def bank8366 : Fin 2 → Cell := twoBank p8366 ray8366
theorem signs8366 : ∀ j, Signs p8366 (bank8366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8367 := params 14
abbrev ray8367 := rays 14
def bank8367 : Fin 2 → Cell := twoBank p8367 ray8367
theorem signs8367 : ∀ j, Signs p8367 (bank8367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8368 := params 15
abbrev ray8368 := rays 15
def bank8368 : Fin 2 → Cell := twoBank p8368 ray8368
theorem signs8368 : ∀ j, Signs p8368 (bank8368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8369 := params 16
abbrev ray8369 := rays 16
def bank8369 : Fin 2 → Cell := twoBank p8369 ray8369
theorem signs8369 : ∀ j, Signs p8369 (bank8369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8370 := params 17
abbrev ray8370 := rays 17
def bank8370 : Fin 2 → Cell := twoBank p8370 ray8370
theorem signs8370 : ∀ j, Signs p8370 (bank8370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8371 := params 18
abbrev ray8371 := rays 18
def bank8371 : Fin 2 → Cell := twoBank p8371 ray8371
theorem signs8371 : ∀ j, Signs p8371 (bank8371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8372 := params 19
abbrev ray8372 := rays 19
def bank8372 : Fin 2 → Cell := twoBank p8372 ray8372
theorem signs8372 : ∀ j, Signs p8372 (bank8372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8373 := params 20
abbrev ray8373 := rays 20
def bank8373 : Fin 2 → Cell := twoBank p8373 ray8373
theorem signs8373 : ∀ j, Signs p8373 (bank8373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8374 := params 21
abbrev ray8374 := rays 21
def bank8374 : Fin 2 → Cell := twoBank p8374 ray8374
theorem signs8374 : ∀ j, Signs p8374 (bank8374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8375 := params 22
abbrev ray8375 := rays 22
def bank8375 : Fin 2 → Cell := twoBank p8375 ray8375
theorem signs8375 : ∀ j, Signs p8375 (bank8375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8376 := params 23
abbrev ray8376 := rays 23
def bank8376 : Fin 2 → Cell := twoBank p8376 ray8376
theorem signs8376 : ∀ j, Signs p8376 (bank8376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8377 := params 24
abbrev ray8377 := rays 24
def bank8377 : Fin 2 → Cell := twoBank p8377 ray8377
theorem signs8377 : ∀ j, Signs p8377 (bank8377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8378 := params 25
abbrev ray8378 := rays 25
def bank8378 : Fin 2 → Cell := twoBank p8378 ray8378
theorem signs8378 : ∀ j, Signs p8378 (bank8378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8379 := params 26
abbrev ray8379 := rays 26
def bank8379 : Fin 2 → Cell := twoBank p8379 ray8379
theorem signs8379 : ∀ j, Signs p8379 (bank8379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8380 := params 27
abbrev ray8380 := rays 27
def bank8380 : Fin 2 → Cell := twoBank p8380 ray8380
theorem signs8380 : ∀ j, Signs p8380 (bank8380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8381 := params 28
abbrev ray8381 := rays 28
def bank8381 : Fin 2 → Cell := twoBank p8381 ray8381
theorem signs8381 : ∀ j, Signs p8381 (bank8381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8382 := params 29
abbrev ray8382 := rays 29
def bank8382 : Fin 2 → Cell := twoBank p8382 ray8382
theorem signs8382 : ∀ j, Signs p8382 (bank8382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8383 := params 30
abbrev ray8383 := rays 30
def bank8383 : Fin 2 → Cell := twoBank p8383 ray8383
theorem signs8383 : ∀ j, Signs p8383 (bank8383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8384 := params 31
abbrev ray8384 := rays 31
def bank8384 : Fin 2 → Cell := twoBank p8384 ray8384
theorem signs8384 : ∀ j, Signs p8384 (bank8384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08353_08384
