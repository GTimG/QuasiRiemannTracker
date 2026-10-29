/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05473_05504
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98911505082664,98911237364169,98910969622029,98910701856245,98910434066818,98910166253749,98909898417038,98909630556687,98909362672697,98909094765069,98908826833803,98908558878901,98908290900363,98908022898191,98907754872385,98907486822946,98907218749875,98906950653174,98906682532843,98906414388883,98906146221295,98905878030080,98905609815239,98905341576772,98905073314681,98904805028967,98904536719631,98904268386673,98904000030095,98903731649897,98903463246080,98903194818646,98902926367595]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5472+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5473 := params 0
abbrev ray5473 := rays 0
def bank5473 : Fin 2 → Cell := twoBank p5473 ray5473
theorem signs5473 : ∀ j, Signs p5473 (bank5473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5474 := params 1
abbrev ray5474 := rays 1
def bank5474 : Fin 2 → Cell := twoBank p5474 ray5474
theorem signs5474 : ∀ j, Signs p5474 (bank5474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5475 := params 2
abbrev ray5475 := rays 2
def bank5475 : Fin 2 → Cell := twoBank p5475 ray5475
theorem signs5475 : ∀ j, Signs p5475 (bank5475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5476 := params 3
abbrev ray5476 := rays 3
def bank5476 : Fin 2 → Cell := twoBank p5476 ray5476
theorem signs5476 : ∀ j, Signs p5476 (bank5476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5477 := params 4
abbrev ray5477 := rays 4
def bank5477 : Fin 2 → Cell := twoBank p5477 ray5477
theorem signs5477 : ∀ j, Signs p5477 (bank5477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5478 := params 5
abbrev ray5478 := rays 5
def bank5478 : Fin 2 → Cell := twoBank p5478 ray5478
theorem signs5478 : ∀ j, Signs p5478 (bank5478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5479 := params 6
abbrev ray5479 := rays 6
def bank5479 : Fin 2 → Cell := twoBank p5479 ray5479
theorem signs5479 : ∀ j, Signs p5479 (bank5479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5480 := params 7
abbrev ray5480 := rays 7
def bank5480 : Fin 2 → Cell := twoBank p5480 ray5480
theorem signs5480 : ∀ j, Signs p5480 (bank5480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5481 := params 8
abbrev ray5481 := rays 8
def bank5481 : Fin 2 → Cell := twoBank p5481 ray5481
theorem signs5481 : ∀ j, Signs p5481 (bank5481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5482 := params 9
abbrev ray5482 := rays 9
def bank5482 : Fin 2 → Cell := twoBank p5482 ray5482
theorem signs5482 : ∀ j, Signs p5482 (bank5482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5483 := params 10
abbrev ray5483 := rays 10
def bank5483 : Fin 2 → Cell := twoBank p5483 ray5483
theorem signs5483 : ∀ j, Signs p5483 (bank5483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5484 := params 11
abbrev ray5484 := rays 11
def bank5484 : Fin 2 → Cell := twoBank p5484 ray5484
theorem signs5484 : ∀ j, Signs p5484 (bank5484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5485 := params 12
abbrev ray5485 := rays 12
def bank5485 : Fin 2 → Cell := twoBank p5485 ray5485
theorem signs5485 : ∀ j, Signs p5485 (bank5485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5486 := params 13
abbrev ray5486 := rays 13
def bank5486 : Fin 2 → Cell := twoBank p5486 ray5486
theorem signs5486 : ∀ j, Signs p5486 (bank5486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5487 := params 14
abbrev ray5487 := rays 14
def bank5487 : Fin 2 → Cell := twoBank p5487 ray5487
theorem signs5487 : ∀ j, Signs p5487 (bank5487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5488 := params 15
abbrev ray5488 := rays 15
def bank5488 : Fin 2 → Cell := twoBank p5488 ray5488
theorem signs5488 : ∀ j, Signs p5488 (bank5488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5489 := params 16
abbrev ray5489 := rays 16
def bank5489 : Fin 2 → Cell := twoBank p5489 ray5489
theorem signs5489 : ∀ j, Signs p5489 (bank5489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5490 := params 17
abbrev ray5490 := rays 17
def bank5490 : Fin 2 → Cell := twoBank p5490 ray5490
theorem signs5490 : ∀ j, Signs p5490 (bank5490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5491 := params 18
abbrev ray5491 := rays 18
def bank5491 : Fin 2 → Cell := twoBank p5491 ray5491
theorem signs5491 : ∀ j, Signs p5491 (bank5491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5492 := params 19
abbrev ray5492 := rays 19
def bank5492 : Fin 2 → Cell := twoBank p5492 ray5492
theorem signs5492 : ∀ j, Signs p5492 (bank5492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5493 := params 20
abbrev ray5493 := rays 20
def bank5493 : Fin 2 → Cell := twoBank p5493 ray5493
theorem signs5493 : ∀ j, Signs p5493 (bank5493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5494 := params 21
abbrev ray5494 := rays 21
def bank5494 : Fin 2 → Cell := twoBank p5494 ray5494
theorem signs5494 : ∀ j, Signs p5494 (bank5494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5495 := params 22
abbrev ray5495 := rays 22
def bank5495 : Fin 2 → Cell := twoBank p5495 ray5495
theorem signs5495 : ∀ j, Signs p5495 (bank5495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5496 := params 23
abbrev ray5496 := rays 23
def bank5496 : Fin 2 → Cell := twoBank p5496 ray5496
theorem signs5496 : ∀ j, Signs p5496 (bank5496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5497 := params 24
abbrev ray5497 := rays 24
def bank5497 : Fin 2 → Cell := twoBank p5497 ray5497
theorem signs5497 : ∀ j, Signs p5497 (bank5497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5498 := params 25
abbrev ray5498 := rays 25
def bank5498 : Fin 2 → Cell := twoBank p5498 ray5498
theorem signs5498 : ∀ j, Signs p5498 (bank5498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5499 := params 26
abbrev ray5499 := rays 26
def bank5499 : Fin 2 → Cell := twoBank p5499 ray5499
theorem signs5499 : ∀ j, Signs p5499 (bank5499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5500 := params 27
abbrev ray5500 := rays 27
def bank5500 : Fin 2 → Cell := twoBank p5500 ray5500
theorem signs5500 : ∀ j, Signs p5500 (bank5500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5501 := params 28
abbrev ray5501 := rays 28
def bank5501 : Fin 2 → Cell := twoBank p5501 ray5501
theorem signs5501 : ∀ j, Signs p5501 (bank5501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5502 := params 29
abbrev ray5502 := rays 29
def bank5502 : Fin 2 → Cell := twoBank p5502 ray5502
theorem signs5502 : ∀ j, Signs p5502 (bank5502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5503 := params 30
abbrev ray5503 := rays 30
def bank5503 : Fin 2 → Cell := twoBank p5503 ray5503
theorem signs5503 : ∀ j, Signs p5503 (bank5503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5504 := params 31
abbrev ray5504 := rays 31
def bank5504 : Fin 2 → Cell := twoBank p5504 ray5504
theorem signs5504 : ∀ j, Signs p5504 (bank5504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05473_05504
