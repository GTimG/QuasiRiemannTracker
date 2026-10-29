/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04353_04384
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99196277702698,99196037085137,99195796442802,99195555775694,99195315083814,99195074367163,99194833625743,99194592859554,99194352068598,99194111252876,99193870412388,99193629547136,99193388657121,99193147742344,99192906802806,99192665838508,99192424849451,99192183835636,99191942797065,99191701733738,99191460645657,99191219532822,99190978395235,99190737232897,99190496045808,99190254833970,99190013597384,99189772336051,99189531049972,99189289739148,99189048403581,99188807043271,99188565658219]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4352+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4353 := params 0
abbrev ray4353 := rays 0
def bank4353 : Fin 2 → Cell := twoBank p4353 ray4353
theorem signs4353 : ∀ j, Signs p4353 (bank4353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4354 := params 1
abbrev ray4354 := rays 1
def bank4354 : Fin 2 → Cell := twoBank p4354 ray4354
theorem signs4354 : ∀ j, Signs p4354 (bank4354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4355 := params 2
abbrev ray4355 := rays 2
def bank4355 : Fin 2 → Cell := twoBank p4355 ray4355
theorem signs4355 : ∀ j, Signs p4355 (bank4355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4356 := params 3
abbrev ray4356 := rays 3
def bank4356 : Fin 2 → Cell := twoBank p4356 ray4356
theorem signs4356 : ∀ j, Signs p4356 (bank4356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4357 := params 4
abbrev ray4357 := rays 4
def bank4357 : Fin 2 → Cell := twoBank p4357 ray4357
theorem signs4357 : ∀ j, Signs p4357 (bank4357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4358 := params 5
abbrev ray4358 := rays 5
def bank4358 : Fin 2 → Cell := twoBank p4358 ray4358
theorem signs4358 : ∀ j, Signs p4358 (bank4358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4359 := params 6
abbrev ray4359 := rays 6
def bank4359 : Fin 2 → Cell := twoBank p4359 ray4359
theorem signs4359 : ∀ j, Signs p4359 (bank4359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4360 := params 7
abbrev ray4360 := rays 7
def bank4360 : Fin 2 → Cell := twoBank p4360 ray4360
theorem signs4360 : ∀ j, Signs p4360 (bank4360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4361 := params 8
abbrev ray4361 := rays 8
def bank4361 : Fin 2 → Cell := twoBank p4361 ray4361
theorem signs4361 : ∀ j, Signs p4361 (bank4361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4362 := params 9
abbrev ray4362 := rays 9
def bank4362 : Fin 2 → Cell := twoBank p4362 ray4362
theorem signs4362 : ∀ j, Signs p4362 (bank4362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4363 := params 10
abbrev ray4363 := rays 10
def bank4363 : Fin 2 → Cell := twoBank p4363 ray4363
theorem signs4363 : ∀ j, Signs p4363 (bank4363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4364 := params 11
abbrev ray4364 := rays 11
def bank4364 : Fin 2 → Cell := twoBank p4364 ray4364
theorem signs4364 : ∀ j, Signs p4364 (bank4364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4365 := params 12
abbrev ray4365 := rays 12
def bank4365 : Fin 2 → Cell := twoBank p4365 ray4365
theorem signs4365 : ∀ j, Signs p4365 (bank4365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4366 := params 13
abbrev ray4366 := rays 13
def bank4366 : Fin 2 → Cell := twoBank p4366 ray4366
theorem signs4366 : ∀ j, Signs p4366 (bank4366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4367 := params 14
abbrev ray4367 := rays 14
def bank4367 : Fin 2 → Cell := twoBank p4367 ray4367
theorem signs4367 : ∀ j, Signs p4367 (bank4367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4368 := params 15
abbrev ray4368 := rays 15
def bank4368 : Fin 2 → Cell := twoBank p4368 ray4368
theorem signs4368 : ∀ j, Signs p4368 (bank4368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4369 := params 16
abbrev ray4369 := rays 16
def bank4369 : Fin 2 → Cell := twoBank p4369 ray4369
theorem signs4369 : ∀ j, Signs p4369 (bank4369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4370 := params 17
abbrev ray4370 := rays 17
def bank4370 : Fin 2 → Cell := twoBank p4370 ray4370
theorem signs4370 : ∀ j, Signs p4370 (bank4370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4371 := params 18
abbrev ray4371 := rays 18
def bank4371 : Fin 2 → Cell := twoBank p4371 ray4371
theorem signs4371 : ∀ j, Signs p4371 (bank4371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4372 := params 19
abbrev ray4372 := rays 19
def bank4372 : Fin 2 → Cell := twoBank p4372 ray4372
theorem signs4372 : ∀ j, Signs p4372 (bank4372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4373 := params 20
abbrev ray4373 := rays 20
def bank4373 : Fin 2 → Cell := twoBank p4373 ray4373
theorem signs4373 : ∀ j, Signs p4373 (bank4373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4374 := params 21
abbrev ray4374 := rays 21
def bank4374 : Fin 2 → Cell := twoBank p4374 ray4374
theorem signs4374 : ∀ j, Signs p4374 (bank4374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4375 := params 22
abbrev ray4375 := rays 22
def bank4375 : Fin 2 → Cell := twoBank p4375 ray4375
theorem signs4375 : ∀ j, Signs p4375 (bank4375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4376 := params 23
abbrev ray4376 := rays 23
def bank4376 : Fin 2 → Cell := twoBank p4376 ray4376
theorem signs4376 : ∀ j, Signs p4376 (bank4376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4377 := params 24
abbrev ray4377 := rays 24
def bank4377 : Fin 2 → Cell := twoBank p4377 ray4377
theorem signs4377 : ∀ j, Signs p4377 (bank4377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4378 := params 25
abbrev ray4378 := rays 25
def bank4378 : Fin 2 → Cell := twoBank p4378 ray4378
theorem signs4378 : ∀ j, Signs p4378 (bank4378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4379 := params 26
abbrev ray4379 := rays 26
def bank4379 : Fin 2 → Cell := twoBank p4379 ray4379
theorem signs4379 : ∀ j, Signs p4379 (bank4379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4380 := params 27
abbrev ray4380 := rays 27
def bank4380 : Fin 2 → Cell := twoBank p4380 ray4380
theorem signs4380 : ∀ j, Signs p4380 (bank4380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4381 := params 28
abbrev ray4381 := rays 28
def bank4381 : Fin 2 → Cell := twoBank p4381 ray4381
theorem signs4381 : ∀ j, Signs p4381 (bank4381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4382 := params 29
abbrev ray4382 := rays 29
def bank4382 : Fin 2 → Cell := twoBank p4382 ray4382
theorem signs4382 : ∀ j, Signs p4382 (bank4382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4383 := params 30
abbrev ray4383 := rays 30
def bank4383 : Fin 2 → Cell := twoBank p4383 ray4383
theorem signs4383 : ∀ j, Signs p4383 (bank4383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4384 := params 31
abbrev ray4384 := rays 31
def bank4384 : Fin 2 → Cell := twoBank p4384 ray4384
theorem signs4384 : ∀ j, Signs p4384 (bank4384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04353_04384
