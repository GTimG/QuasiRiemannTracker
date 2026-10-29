/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11521_11552
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96889293967056,96888897020564,96888500054503,96888103068874,96887706063677,96887309038913,96886911994582,96886514930684,96886117847220,96885720744191,96885323621597,96884926479438,96884529317715,96884132136428,96883734935578,96883337715165,96882940475190,96882543215653,96882145936555,96881748637896,96881351319676,96880953981896,96880556624557,96880159247658,96879761851201,96879364435186,96878966999613,96878569544483,96878172069796,96877774575552,96877377061752,96876979528397,96876581975487]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11520+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11521 := params 0
abbrev ray11521 := rays 0
def bank11521 : Fin 2 → Cell := twoBank p11521 ray11521
theorem signs11521 : ∀ j, Signs p11521 (bank11521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11522 := params 1
abbrev ray11522 := rays 1
def bank11522 : Fin 2 → Cell := twoBank p11522 ray11522
theorem signs11522 : ∀ j, Signs p11522 (bank11522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11523 := params 2
abbrev ray11523 := rays 2
def bank11523 : Fin 2 → Cell := twoBank p11523 ray11523
theorem signs11523 : ∀ j, Signs p11523 (bank11523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11524 := params 3
abbrev ray11524 := rays 3
def bank11524 : Fin 2 → Cell := twoBank p11524 ray11524
theorem signs11524 : ∀ j, Signs p11524 (bank11524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11525 := params 4
abbrev ray11525 := rays 4
def bank11525 : Fin 2 → Cell := twoBank p11525 ray11525
theorem signs11525 : ∀ j, Signs p11525 (bank11525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11526 := params 5
abbrev ray11526 := rays 5
def bank11526 : Fin 2 → Cell := twoBank p11526 ray11526
theorem signs11526 : ∀ j, Signs p11526 (bank11526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11527 := params 6
abbrev ray11527 := rays 6
def bank11527 : Fin 2 → Cell := twoBank p11527 ray11527
theorem signs11527 : ∀ j, Signs p11527 (bank11527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11528 := params 7
abbrev ray11528 := rays 7
def bank11528 : Fin 2 → Cell := twoBank p11528 ray11528
theorem signs11528 : ∀ j, Signs p11528 (bank11528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11529 := params 8
abbrev ray11529 := rays 8
def bank11529 : Fin 2 → Cell := twoBank p11529 ray11529
theorem signs11529 : ∀ j, Signs p11529 (bank11529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11530 := params 9
abbrev ray11530 := rays 9
def bank11530 : Fin 2 → Cell := twoBank p11530 ray11530
theorem signs11530 : ∀ j, Signs p11530 (bank11530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11531 := params 10
abbrev ray11531 := rays 10
def bank11531 : Fin 2 → Cell := twoBank p11531 ray11531
theorem signs11531 : ∀ j, Signs p11531 (bank11531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11532 := params 11
abbrev ray11532 := rays 11
def bank11532 : Fin 2 → Cell := twoBank p11532 ray11532
theorem signs11532 : ∀ j, Signs p11532 (bank11532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11533 := params 12
abbrev ray11533 := rays 12
def bank11533 : Fin 2 → Cell := twoBank p11533 ray11533
theorem signs11533 : ∀ j, Signs p11533 (bank11533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11534 := params 13
abbrev ray11534 := rays 13
def bank11534 : Fin 2 → Cell := twoBank p11534 ray11534
theorem signs11534 : ∀ j, Signs p11534 (bank11534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11535 := params 14
abbrev ray11535 := rays 14
def bank11535 : Fin 2 → Cell := twoBank p11535 ray11535
theorem signs11535 : ∀ j, Signs p11535 (bank11535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11536 := params 15
abbrev ray11536 := rays 15
def bank11536 : Fin 2 → Cell := twoBank p11536 ray11536
theorem signs11536 : ∀ j, Signs p11536 (bank11536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11537 := params 16
abbrev ray11537 := rays 16
def bank11537 : Fin 2 → Cell := twoBank p11537 ray11537
theorem signs11537 : ∀ j, Signs p11537 (bank11537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11538 := params 17
abbrev ray11538 := rays 17
def bank11538 : Fin 2 → Cell := twoBank p11538 ray11538
theorem signs11538 : ∀ j, Signs p11538 (bank11538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11539 := params 18
abbrev ray11539 := rays 18
def bank11539 : Fin 2 → Cell := twoBank p11539 ray11539
theorem signs11539 : ∀ j, Signs p11539 (bank11539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11540 := params 19
abbrev ray11540 := rays 19
def bank11540 : Fin 2 → Cell := twoBank p11540 ray11540
theorem signs11540 : ∀ j, Signs p11540 (bank11540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11541 := params 20
abbrev ray11541 := rays 20
def bank11541 : Fin 2 → Cell := twoBank p11541 ray11541
theorem signs11541 : ∀ j, Signs p11541 (bank11541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11542 := params 21
abbrev ray11542 := rays 21
def bank11542 : Fin 2 → Cell := twoBank p11542 ray11542
theorem signs11542 : ∀ j, Signs p11542 (bank11542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11543 := params 22
abbrev ray11543 := rays 22
def bank11543 : Fin 2 → Cell := twoBank p11543 ray11543
theorem signs11543 : ∀ j, Signs p11543 (bank11543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11544 := params 23
abbrev ray11544 := rays 23
def bank11544 : Fin 2 → Cell := twoBank p11544 ray11544
theorem signs11544 : ∀ j, Signs p11544 (bank11544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11545 := params 24
abbrev ray11545 := rays 24
def bank11545 : Fin 2 → Cell := twoBank p11545 ray11545
theorem signs11545 : ∀ j, Signs p11545 (bank11545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11546 := params 25
abbrev ray11546 := rays 25
def bank11546 : Fin 2 → Cell := twoBank p11546 ray11546
theorem signs11546 : ∀ j, Signs p11546 (bank11546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11547 := params 26
abbrev ray11547 := rays 26
def bank11547 : Fin 2 → Cell := twoBank p11547 ray11547
theorem signs11547 : ∀ j, Signs p11547 (bank11547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11548 := params 27
abbrev ray11548 := rays 27
def bank11548 : Fin 2 → Cell := twoBank p11548 ray11548
theorem signs11548 : ∀ j, Signs p11548 (bank11548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11549 := params 28
abbrev ray11549 := rays 28
def bank11549 : Fin 2 → Cell := twoBank p11549 ray11549
theorem signs11549 : ∀ j, Signs p11549 (bank11549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11550 := params 29
abbrev ray11550 := rays 29
def bank11550 : Fin 2 → Cell := twoBank p11550 ray11550
theorem signs11550 : ∀ j, Signs p11550 (bank11550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11551 := params 30
abbrev ray11551 := rays 30
def bank11551 : Fin 2 → Cell := twoBank p11551 ray11551
theorem signs11551 : ∀ j, Signs p11551 (bank11551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11552 := params 31
abbrev ray11552 := rays 31
def bank11552 : Fin 2 → Cell := twoBank p11552 ray11552
theorem signs11552 : ∀ j, Signs p11552 (bank11552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11521_11552
