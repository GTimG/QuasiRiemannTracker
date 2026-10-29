/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05409_05440
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98928589841691,98928323638436,98928057411476,98927791160811,98927524886443,98927258588372,98926992266600,98926725921127,98926459551954,98926193159082,98925926742512,98925660302245,98925393838283,98925127350625,98924860839273,98924594304228,98924327745491,98924061163063,98923794556945,98923527927137,98923261273641,98922994596457,98922727895587,98922461171031,98922194422791,98921927650867,98921660855260,98921394035972,98921127193003,98920860326354,98920593436026,98920326522020,98920059584337]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5408+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5409 := params 0
abbrev ray5409 := rays 0
def bank5409 : Fin 2 → Cell := twoBank p5409 ray5409
theorem signs5409 : ∀ j, Signs p5409 (bank5409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5410 := params 1
abbrev ray5410 := rays 1
def bank5410 : Fin 2 → Cell := twoBank p5410 ray5410
theorem signs5410 : ∀ j, Signs p5410 (bank5410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5411 := params 2
abbrev ray5411 := rays 2
def bank5411 : Fin 2 → Cell := twoBank p5411 ray5411
theorem signs5411 : ∀ j, Signs p5411 (bank5411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5412 := params 3
abbrev ray5412 := rays 3
def bank5412 : Fin 2 → Cell := twoBank p5412 ray5412
theorem signs5412 : ∀ j, Signs p5412 (bank5412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5413 := params 4
abbrev ray5413 := rays 4
def bank5413 : Fin 2 → Cell := twoBank p5413 ray5413
theorem signs5413 : ∀ j, Signs p5413 (bank5413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5414 := params 5
abbrev ray5414 := rays 5
def bank5414 : Fin 2 → Cell := twoBank p5414 ray5414
theorem signs5414 : ∀ j, Signs p5414 (bank5414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5415 := params 6
abbrev ray5415 := rays 6
def bank5415 : Fin 2 → Cell := twoBank p5415 ray5415
theorem signs5415 : ∀ j, Signs p5415 (bank5415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5416 := params 7
abbrev ray5416 := rays 7
def bank5416 : Fin 2 → Cell := twoBank p5416 ray5416
theorem signs5416 : ∀ j, Signs p5416 (bank5416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5417 := params 8
abbrev ray5417 := rays 8
def bank5417 : Fin 2 → Cell := twoBank p5417 ray5417
theorem signs5417 : ∀ j, Signs p5417 (bank5417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5418 := params 9
abbrev ray5418 := rays 9
def bank5418 : Fin 2 → Cell := twoBank p5418 ray5418
theorem signs5418 : ∀ j, Signs p5418 (bank5418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5419 := params 10
abbrev ray5419 := rays 10
def bank5419 : Fin 2 → Cell := twoBank p5419 ray5419
theorem signs5419 : ∀ j, Signs p5419 (bank5419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5420 := params 11
abbrev ray5420 := rays 11
def bank5420 : Fin 2 → Cell := twoBank p5420 ray5420
theorem signs5420 : ∀ j, Signs p5420 (bank5420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5421 := params 12
abbrev ray5421 := rays 12
def bank5421 : Fin 2 → Cell := twoBank p5421 ray5421
theorem signs5421 : ∀ j, Signs p5421 (bank5421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5422 := params 13
abbrev ray5422 := rays 13
def bank5422 : Fin 2 → Cell := twoBank p5422 ray5422
theorem signs5422 : ∀ j, Signs p5422 (bank5422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5423 := params 14
abbrev ray5423 := rays 14
def bank5423 : Fin 2 → Cell := twoBank p5423 ray5423
theorem signs5423 : ∀ j, Signs p5423 (bank5423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5424 := params 15
abbrev ray5424 := rays 15
def bank5424 : Fin 2 → Cell := twoBank p5424 ray5424
theorem signs5424 : ∀ j, Signs p5424 (bank5424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5425 := params 16
abbrev ray5425 := rays 16
def bank5425 : Fin 2 → Cell := twoBank p5425 ray5425
theorem signs5425 : ∀ j, Signs p5425 (bank5425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5426 := params 17
abbrev ray5426 := rays 17
def bank5426 : Fin 2 → Cell := twoBank p5426 ray5426
theorem signs5426 : ∀ j, Signs p5426 (bank5426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5427 := params 18
abbrev ray5427 := rays 18
def bank5427 : Fin 2 → Cell := twoBank p5427 ray5427
theorem signs5427 : ∀ j, Signs p5427 (bank5427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5428 := params 19
abbrev ray5428 := rays 19
def bank5428 : Fin 2 → Cell := twoBank p5428 ray5428
theorem signs5428 : ∀ j, Signs p5428 (bank5428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5429 := params 20
abbrev ray5429 := rays 20
def bank5429 : Fin 2 → Cell := twoBank p5429 ray5429
theorem signs5429 : ∀ j, Signs p5429 (bank5429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5430 := params 21
abbrev ray5430 := rays 21
def bank5430 : Fin 2 → Cell := twoBank p5430 ray5430
theorem signs5430 : ∀ j, Signs p5430 (bank5430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5431 := params 22
abbrev ray5431 := rays 22
def bank5431 : Fin 2 → Cell := twoBank p5431 ray5431
theorem signs5431 : ∀ j, Signs p5431 (bank5431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5432 := params 23
abbrev ray5432 := rays 23
def bank5432 : Fin 2 → Cell := twoBank p5432 ray5432
theorem signs5432 : ∀ j, Signs p5432 (bank5432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5433 := params 24
abbrev ray5433 := rays 24
def bank5433 : Fin 2 → Cell := twoBank p5433 ray5433
theorem signs5433 : ∀ j, Signs p5433 (bank5433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5434 := params 25
abbrev ray5434 := rays 25
def bank5434 : Fin 2 → Cell := twoBank p5434 ray5434
theorem signs5434 : ∀ j, Signs p5434 (bank5434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5435 := params 26
abbrev ray5435 := rays 26
def bank5435 : Fin 2 → Cell := twoBank p5435 ray5435
theorem signs5435 : ∀ j, Signs p5435 (bank5435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5436 := params 27
abbrev ray5436 := rays 27
def bank5436 : Fin 2 → Cell := twoBank p5436 ray5436
theorem signs5436 : ∀ j, Signs p5436 (bank5436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5437 := params 28
abbrev ray5437 := rays 28
def bank5437 : Fin 2 → Cell := twoBank p5437 ray5437
theorem signs5437 : ∀ j, Signs p5437 (bank5437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5438 := params 29
abbrev ray5438 := rays 29
def bank5438 : Fin 2 → Cell := twoBank p5438 ray5438
theorem signs5438 : ∀ j, Signs p5438 (bank5438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5439 := params 30
abbrev ray5439 := rays 30
def bank5439 : Fin 2 → Cell := twoBank p5439 ray5439
theorem signs5439 : ∀ j, Signs p5439 (bank5439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5440 := params 31
abbrev ray5440 := rays 31
def bank5440 : Fin 2 → Cell := twoBank p5440 ray5440
theorem signs5440 : ∀ j, Signs p5440 (bank5440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05409_05440
