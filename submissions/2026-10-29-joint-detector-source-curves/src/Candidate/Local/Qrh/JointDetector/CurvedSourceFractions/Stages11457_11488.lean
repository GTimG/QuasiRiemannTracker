/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11457_11488
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96914657818541,96914262125405,96913866412671,96913470680339,96913074928410,96912679156884,96912283365762,96911887555044,96911491724730,96911095874821,96910700005318,96910304116221,96909908207530,96909512279246,96909116331369,96908720363900,96908324376839,96907928370187,96907532343944,96907136298111,96906740232688,96906344147676,96905948043075,96905551918885,96905155775107,96904759611741,96904363428788,96903967226248,96903571004122,96903174762410,96902778501113,96902382220231,96901985919765]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11456+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11457 := params 0
abbrev ray11457 := rays 0
def bank11457 : Fin 2 → Cell := twoBank p11457 ray11457
theorem signs11457 : ∀ j, Signs p11457 (bank11457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11458 := params 1
abbrev ray11458 := rays 1
def bank11458 : Fin 2 → Cell := twoBank p11458 ray11458
theorem signs11458 : ∀ j, Signs p11458 (bank11458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11459 := params 2
abbrev ray11459 := rays 2
def bank11459 : Fin 2 → Cell := twoBank p11459 ray11459
theorem signs11459 : ∀ j, Signs p11459 (bank11459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11460 := params 3
abbrev ray11460 := rays 3
def bank11460 : Fin 2 → Cell := twoBank p11460 ray11460
theorem signs11460 : ∀ j, Signs p11460 (bank11460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11461 := params 4
abbrev ray11461 := rays 4
def bank11461 : Fin 2 → Cell := twoBank p11461 ray11461
theorem signs11461 : ∀ j, Signs p11461 (bank11461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11462 := params 5
abbrev ray11462 := rays 5
def bank11462 : Fin 2 → Cell := twoBank p11462 ray11462
theorem signs11462 : ∀ j, Signs p11462 (bank11462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11463 := params 6
abbrev ray11463 := rays 6
def bank11463 : Fin 2 → Cell := twoBank p11463 ray11463
theorem signs11463 : ∀ j, Signs p11463 (bank11463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11464 := params 7
abbrev ray11464 := rays 7
def bank11464 : Fin 2 → Cell := twoBank p11464 ray11464
theorem signs11464 : ∀ j, Signs p11464 (bank11464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11465 := params 8
abbrev ray11465 := rays 8
def bank11465 : Fin 2 → Cell := twoBank p11465 ray11465
theorem signs11465 : ∀ j, Signs p11465 (bank11465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11466 := params 9
abbrev ray11466 := rays 9
def bank11466 : Fin 2 → Cell := twoBank p11466 ray11466
theorem signs11466 : ∀ j, Signs p11466 (bank11466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11467 := params 10
abbrev ray11467 := rays 10
def bank11467 : Fin 2 → Cell := twoBank p11467 ray11467
theorem signs11467 : ∀ j, Signs p11467 (bank11467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11468 := params 11
abbrev ray11468 := rays 11
def bank11468 : Fin 2 → Cell := twoBank p11468 ray11468
theorem signs11468 : ∀ j, Signs p11468 (bank11468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11469 := params 12
abbrev ray11469 := rays 12
def bank11469 : Fin 2 → Cell := twoBank p11469 ray11469
theorem signs11469 : ∀ j, Signs p11469 (bank11469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11470 := params 13
abbrev ray11470 := rays 13
def bank11470 : Fin 2 → Cell := twoBank p11470 ray11470
theorem signs11470 : ∀ j, Signs p11470 (bank11470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11471 := params 14
abbrev ray11471 := rays 14
def bank11471 : Fin 2 → Cell := twoBank p11471 ray11471
theorem signs11471 : ∀ j, Signs p11471 (bank11471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11472 := params 15
abbrev ray11472 := rays 15
def bank11472 : Fin 2 → Cell := twoBank p11472 ray11472
theorem signs11472 : ∀ j, Signs p11472 (bank11472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11473 := params 16
abbrev ray11473 := rays 16
def bank11473 : Fin 2 → Cell := twoBank p11473 ray11473
theorem signs11473 : ∀ j, Signs p11473 (bank11473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11474 := params 17
abbrev ray11474 := rays 17
def bank11474 : Fin 2 → Cell := twoBank p11474 ray11474
theorem signs11474 : ∀ j, Signs p11474 (bank11474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11475 := params 18
abbrev ray11475 := rays 18
def bank11475 : Fin 2 → Cell := twoBank p11475 ray11475
theorem signs11475 : ∀ j, Signs p11475 (bank11475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11476 := params 19
abbrev ray11476 := rays 19
def bank11476 : Fin 2 → Cell := twoBank p11476 ray11476
theorem signs11476 : ∀ j, Signs p11476 (bank11476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11477 := params 20
abbrev ray11477 := rays 20
def bank11477 : Fin 2 → Cell := twoBank p11477 ray11477
theorem signs11477 : ∀ j, Signs p11477 (bank11477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11478 := params 21
abbrev ray11478 := rays 21
def bank11478 : Fin 2 → Cell := twoBank p11478 ray11478
theorem signs11478 : ∀ j, Signs p11478 (bank11478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11479 := params 22
abbrev ray11479 := rays 22
def bank11479 : Fin 2 → Cell := twoBank p11479 ray11479
theorem signs11479 : ∀ j, Signs p11479 (bank11479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11480 := params 23
abbrev ray11480 := rays 23
def bank11480 : Fin 2 → Cell := twoBank p11480 ray11480
theorem signs11480 : ∀ j, Signs p11480 (bank11480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11481 := params 24
abbrev ray11481 := rays 24
def bank11481 : Fin 2 → Cell := twoBank p11481 ray11481
theorem signs11481 : ∀ j, Signs p11481 (bank11481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11482 := params 25
abbrev ray11482 := rays 25
def bank11482 : Fin 2 → Cell := twoBank p11482 ray11482
theorem signs11482 : ∀ j, Signs p11482 (bank11482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11483 := params 26
abbrev ray11483 := rays 26
def bank11483 : Fin 2 → Cell := twoBank p11483 ray11483
theorem signs11483 : ∀ j, Signs p11483 (bank11483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11484 := params 27
abbrev ray11484 := rays 27
def bank11484 : Fin 2 → Cell := twoBank p11484 ray11484
theorem signs11484 : ∀ j, Signs p11484 (bank11484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11485 := params 28
abbrev ray11485 := rays 28
def bank11485 : Fin 2 → Cell := twoBank p11485 ray11485
theorem signs11485 : ∀ j, Signs p11485 (bank11485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11486 := params 29
abbrev ray11486 := rays 29
def bank11486 : Fin 2 → Cell := twoBank p11486 ray11486
theorem signs11486 : ∀ j, Signs p11486 (bank11486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11487 := params 30
abbrev ray11487 := rays 30
def bank11487 : Fin 2 → Cell := twoBank p11487 ray11487
theorem signs11487 : ∀ j, Signs p11487 (bank11487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11488 := params 31
abbrev ray11488 := rays 31
def bank11488 : Fin 2 → Cell := twoBank p11488 ray11488
theorem signs11488 : ∀ j, Signs p11488 (bank11488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11457_11488
