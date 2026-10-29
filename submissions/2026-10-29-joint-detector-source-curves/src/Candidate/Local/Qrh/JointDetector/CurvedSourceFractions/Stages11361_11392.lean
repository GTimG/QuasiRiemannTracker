/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11361_11392
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96952553039541,96952159230000,96951765400816,96951371551990,96950977683522,96950583795412,96950189887661,96949795960270,96949402013238,96949008046567,96948614060257,96948220054308,96947826028721,96947431983496,96947037918633,96946643834134,96946249729998,96945855606226,96945461462819,96945067299777,96944673117100,96944278914789,96943884692845,96943490451268,96943096190058,96942701909216,96942307608742,96941913288637,96941518948901,96941124589535,96940730210539,96940335811913,96939941393659]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11360+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11361 := params 0
abbrev ray11361 := rays 0
def bank11361 : Fin 2 → Cell := twoBank p11361 ray11361
theorem signs11361 : ∀ j, Signs p11361 (bank11361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11362 := params 1
abbrev ray11362 := rays 1
def bank11362 : Fin 2 → Cell := twoBank p11362 ray11362
theorem signs11362 : ∀ j, Signs p11362 (bank11362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11363 := params 2
abbrev ray11363 := rays 2
def bank11363 : Fin 2 → Cell := twoBank p11363 ray11363
theorem signs11363 : ∀ j, Signs p11363 (bank11363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11364 := params 3
abbrev ray11364 := rays 3
def bank11364 : Fin 2 → Cell := twoBank p11364 ray11364
theorem signs11364 : ∀ j, Signs p11364 (bank11364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11365 := params 4
abbrev ray11365 := rays 4
def bank11365 : Fin 2 → Cell := twoBank p11365 ray11365
theorem signs11365 : ∀ j, Signs p11365 (bank11365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11366 := params 5
abbrev ray11366 := rays 5
def bank11366 : Fin 2 → Cell := twoBank p11366 ray11366
theorem signs11366 : ∀ j, Signs p11366 (bank11366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11367 := params 6
abbrev ray11367 := rays 6
def bank11367 : Fin 2 → Cell := twoBank p11367 ray11367
theorem signs11367 : ∀ j, Signs p11367 (bank11367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11368 := params 7
abbrev ray11368 := rays 7
def bank11368 : Fin 2 → Cell := twoBank p11368 ray11368
theorem signs11368 : ∀ j, Signs p11368 (bank11368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11369 := params 8
abbrev ray11369 := rays 8
def bank11369 : Fin 2 → Cell := twoBank p11369 ray11369
theorem signs11369 : ∀ j, Signs p11369 (bank11369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11370 := params 9
abbrev ray11370 := rays 9
def bank11370 : Fin 2 → Cell := twoBank p11370 ray11370
theorem signs11370 : ∀ j, Signs p11370 (bank11370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11371 := params 10
abbrev ray11371 := rays 10
def bank11371 : Fin 2 → Cell := twoBank p11371 ray11371
theorem signs11371 : ∀ j, Signs p11371 (bank11371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11372 := params 11
abbrev ray11372 := rays 11
def bank11372 : Fin 2 → Cell := twoBank p11372 ray11372
theorem signs11372 : ∀ j, Signs p11372 (bank11372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11373 := params 12
abbrev ray11373 := rays 12
def bank11373 : Fin 2 → Cell := twoBank p11373 ray11373
theorem signs11373 : ∀ j, Signs p11373 (bank11373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11374 := params 13
abbrev ray11374 := rays 13
def bank11374 : Fin 2 → Cell := twoBank p11374 ray11374
theorem signs11374 : ∀ j, Signs p11374 (bank11374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11375 := params 14
abbrev ray11375 := rays 14
def bank11375 : Fin 2 → Cell := twoBank p11375 ray11375
theorem signs11375 : ∀ j, Signs p11375 (bank11375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11376 := params 15
abbrev ray11376 := rays 15
def bank11376 : Fin 2 → Cell := twoBank p11376 ray11376
theorem signs11376 : ∀ j, Signs p11376 (bank11376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11377 := params 16
abbrev ray11377 := rays 16
def bank11377 : Fin 2 → Cell := twoBank p11377 ray11377
theorem signs11377 : ∀ j, Signs p11377 (bank11377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11378 := params 17
abbrev ray11378 := rays 17
def bank11378 : Fin 2 → Cell := twoBank p11378 ray11378
theorem signs11378 : ∀ j, Signs p11378 (bank11378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11379 := params 18
abbrev ray11379 := rays 18
def bank11379 : Fin 2 → Cell := twoBank p11379 ray11379
theorem signs11379 : ∀ j, Signs p11379 (bank11379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11380 := params 19
abbrev ray11380 := rays 19
def bank11380 : Fin 2 → Cell := twoBank p11380 ray11380
theorem signs11380 : ∀ j, Signs p11380 (bank11380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11381 := params 20
abbrev ray11381 := rays 20
def bank11381 : Fin 2 → Cell := twoBank p11381 ray11381
theorem signs11381 : ∀ j, Signs p11381 (bank11381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11382 := params 21
abbrev ray11382 := rays 21
def bank11382 : Fin 2 → Cell := twoBank p11382 ray11382
theorem signs11382 : ∀ j, Signs p11382 (bank11382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11383 := params 22
abbrev ray11383 := rays 22
def bank11383 : Fin 2 → Cell := twoBank p11383 ray11383
theorem signs11383 : ∀ j, Signs p11383 (bank11383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11384 := params 23
abbrev ray11384 := rays 23
def bank11384 : Fin 2 → Cell := twoBank p11384 ray11384
theorem signs11384 : ∀ j, Signs p11384 (bank11384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11385 := params 24
abbrev ray11385 := rays 24
def bank11385 : Fin 2 → Cell := twoBank p11385 ray11385
theorem signs11385 : ∀ j, Signs p11385 (bank11385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11386 := params 25
abbrev ray11386 := rays 25
def bank11386 : Fin 2 → Cell := twoBank p11386 ray11386
theorem signs11386 : ∀ j, Signs p11386 (bank11386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11387 := params 26
abbrev ray11387 := rays 26
def bank11387 : Fin 2 → Cell := twoBank p11387 ray11387
theorem signs11387 : ∀ j, Signs p11387 (bank11387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11388 := params 27
abbrev ray11388 := rays 27
def bank11388 : Fin 2 → Cell := twoBank p11388 ray11388
theorem signs11388 : ∀ j, Signs p11388 (bank11388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11389 := params 28
abbrev ray11389 := rays 28
def bank11389 : Fin 2 → Cell := twoBank p11389 ray11389
theorem signs11389 : ∀ j, Signs p11389 (bank11389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11390 := params 29
abbrev ray11390 := rays 29
def bank11390 : Fin 2 → Cell := twoBank p11390 ray11390
theorem signs11390 : ∀ j, Signs p11390 (bank11390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11391 := params 30
abbrev ray11391 := rays 30
def bank11391 : Fin 2 → Cell := twoBank p11391 ray11391
theorem signs11391 : ∀ j, Signs p11391 (bank11391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11392 := params 31
abbrev ray11392 := rays 31
def bank11392 : Fin 2 → Cell := twoBank p11392 ray11392
theorem signs11392 : ∀ j, Signs p11392 (bank11392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11361_11392
