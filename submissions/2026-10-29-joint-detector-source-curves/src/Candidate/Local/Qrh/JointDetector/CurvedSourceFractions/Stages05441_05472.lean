/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05441_05472
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98920059584337,98919792622978,98919525637944,98919258629236,98918991596854,98918724540800,98918457461075,98918190357679,98917923230614,98917656079880,98917388905479,98917121707411,98916854485677,98916587240279,98916319971217,98916052678492,98915785362105,98915518022057,98915250658349,98914983270982,98914715859957,98914448425275,98914180966936,98913913484942,98913645979294,98913378449992,98913110897038,98912843320432,98912575720176,98912308096270,98912040448715,98911772777513,98911505082664]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5440+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5441 := params 0
abbrev ray5441 := rays 0
def bank5441 : Fin 2 → Cell := twoBank p5441 ray5441
theorem signs5441 : ∀ j, Signs p5441 (bank5441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5442 := params 1
abbrev ray5442 := rays 1
def bank5442 : Fin 2 → Cell := twoBank p5442 ray5442
theorem signs5442 : ∀ j, Signs p5442 (bank5442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5443 := params 2
abbrev ray5443 := rays 2
def bank5443 : Fin 2 → Cell := twoBank p5443 ray5443
theorem signs5443 : ∀ j, Signs p5443 (bank5443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5444 := params 3
abbrev ray5444 := rays 3
def bank5444 : Fin 2 → Cell := twoBank p5444 ray5444
theorem signs5444 : ∀ j, Signs p5444 (bank5444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5445 := params 4
abbrev ray5445 := rays 4
def bank5445 : Fin 2 → Cell := twoBank p5445 ray5445
theorem signs5445 : ∀ j, Signs p5445 (bank5445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5446 := params 5
abbrev ray5446 := rays 5
def bank5446 : Fin 2 → Cell := twoBank p5446 ray5446
theorem signs5446 : ∀ j, Signs p5446 (bank5446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5447 := params 6
abbrev ray5447 := rays 6
def bank5447 : Fin 2 → Cell := twoBank p5447 ray5447
theorem signs5447 : ∀ j, Signs p5447 (bank5447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5448 := params 7
abbrev ray5448 := rays 7
def bank5448 : Fin 2 → Cell := twoBank p5448 ray5448
theorem signs5448 : ∀ j, Signs p5448 (bank5448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5449 := params 8
abbrev ray5449 := rays 8
def bank5449 : Fin 2 → Cell := twoBank p5449 ray5449
theorem signs5449 : ∀ j, Signs p5449 (bank5449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5450 := params 9
abbrev ray5450 := rays 9
def bank5450 : Fin 2 → Cell := twoBank p5450 ray5450
theorem signs5450 : ∀ j, Signs p5450 (bank5450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5451 := params 10
abbrev ray5451 := rays 10
def bank5451 : Fin 2 → Cell := twoBank p5451 ray5451
theorem signs5451 : ∀ j, Signs p5451 (bank5451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5452 := params 11
abbrev ray5452 := rays 11
def bank5452 : Fin 2 → Cell := twoBank p5452 ray5452
theorem signs5452 : ∀ j, Signs p5452 (bank5452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5453 := params 12
abbrev ray5453 := rays 12
def bank5453 : Fin 2 → Cell := twoBank p5453 ray5453
theorem signs5453 : ∀ j, Signs p5453 (bank5453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5454 := params 13
abbrev ray5454 := rays 13
def bank5454 : Fin 2 → Cell := twoBank p5454 ray5454
theorem signs5454 : ∀ j, Signs p5454 (bank5454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5455 := params 14
abbrev ray5455 := rays 14
def bank5455 : Fin 2 → Cell := twoBank p5455 ray5455
theorem signs5455 : ∀ j, Signs p5455 (bank5455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5456 := params 15
abbrev ray5456 := rays 15
def bank5456 : Fin 2 → Cell := twoBank p5456 ray5456
theorem signs5456 : ∀ j, Signs p5456 (bank5456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5457 := params 16
abbrev ray5457 := rays 16
def bank5457 : Fin 2 → Cell := twoBank p5457 ray5457
theorem signs5457 : ∀ j, Signs p5457 (bank5457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5458 := params 17
abbrev ray5458 := rays 17
def bank5458 : Fin 2 → Cell := twoBank p5458 ray5458
theorem signs5458 : ∀ j, Signs p5458 (bank5458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5459 := params 18
abbrev ray5459 := rays 18
def bank5459 : Fin 2 → Cell := twoBank p5459 ray5459
theorem signs5459 : ∀ j, Signs p5459 (bank5459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5460 := params 19
abbrev ray5460 := rays 19
def bank5460 : Fin 2 → Cell := twoBank p5460 ray5460
theorem signs5460 : ∀ j, Signs p5460 (bank5460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5461 := params 20
abbrev ray5461 := rays 20
def bank5461 : Fin 2 → Cell := twoBank p5461 ray5461
theorem signs5461 : ∀ j, Signs p5461 (bank5461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5462 := params 21
abbrev ray5462 := rays 21
def bank5462 : Fin 2 → Cell := twoBank p5462 ray5462
theorem signs5462 : ∀ j, Signs p5462 (bank5462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5463 := params 22
abbrev ray5463 := rays 22
def bank5463 : Fin 2 → Cell := twoBank p5463 ray5463
theorem signs5463 : ∀ j, Signs p5463 (bank5463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5464 := params 23
abbrev ray5464 := rays 23
def bank5464 : Fin 2 → Cell := twoBank p5464 ray5464
theorem signs5464 : ∀ j, Signs p5464 (bank5464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5465 := params 24
abbrev ray5465 := rays 24
def bank5465 : Fin 2 → Cell := twoBank p5465 ray5465
theorem signs5465 : ∀ j, Signs p5465 (bank5465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5466 := params 25
abbrev ray5466 := rays 25
def bank5466 : Fin 2 → Cell := twoBank p5466 ray5466
theorem signs5466 : ∀ j, Signs p5466 (bank5466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5467 := params 26
abbrev ray5467 := rays 26
def bank5467 : Fin 2 → Cell := twoBank p5467 ray5467
theorem signs5467 : ∀ j, Signs p5467 (bank5467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5468 := params 27
abbrev ray5468 := rays 27
def bank5468 : Fin 2 → Cell := twoBank p5468 ray5468
theorem signs5468 : ∀ j, Signs p5468 (bank5468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5469 := params 28
abbrev ray5469 := rays 28
def bank5469 : Fin 2 → Cell := twoBank p5469 ray5469
theorem signs5469 : ∀ j, Signs p5469 (bank5469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5470 := params 29
abbrev ray5470 := rays 29
def bank5470 : Fin 2 → Cell := twoBank p5470 ray5470
theorem signs5470 : ∀ j, Signs p5470 (bank5470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5471 := params 30
abbrev ray5471 := rays 30
def bank5471 : Fin 2 → Cell := twoBank p5471 ray5471
theorem signs5471 : ∀ j, Signs p5471 (bank5471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5472 := params 31
abbrev ray5472 := rays 31
def bank5472 : Fin 2 → Cell := twoBank p5472 ray5472
theorem signs5472 : ∀ j, Signs p5472 (bank5472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05441_05472
