/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03521_03552
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99387780152147,99387560532912,99387340887959,99387121217289,99386901520904,99386681798804,99386462050991,99386242277467,99386022478232,99385802653288,99385582802635,99385362926275,99385143024209,99384923096439,99384703142965,99384483163789,99384263158912,99384043128335,99383823072059,99383602990086,99383382882416,99383162749051,99382942589992,99382722405240,99382502194797,99382281958663,99382061696840,99381841409329,99381621096131,99381400757248,99381180392680,99380960002429,99380739586496]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3520+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3521 := params 0
abbrev ray3521 := rays 0
def bank3521 : Fin 2 → Cell := twoBank p3521 ray3521
theorem signs3521 : ∀ j, Signs p3521 (bank3521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3522 := params 1
abbrev ray3522 := rays 1
def bank3522 : Fin 2 → Cell := twoBank p3522 ray3522
theorem signs3522 : ∀ j, Signs p3522 (bank3522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3523 := params 2
abbrev ray3523 := rays 2
def bank3523 : Fin 2 → Cell := twoBank p3523 ray3523
theorem signs3523 : ∀ j, Signs p3523 (bank3523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3524 := params 3
abbrev ray3524 := rays 3
def bank3524 : Fin 2 → Cell := twoBank p3524 ray3524
theorem signs3524 : ∀ j, Signs p3524 (bank3524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3525 := params 4
abbrev ray3525 := rays 4
def bank3525 : Fin 2 → Cell := twoBank p3525 ray3525
theorem signs3525 : ∀ j, Signs p3525 (bank3525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3526 := params 5
abbrev ray3526 := rays 5
def bank3526 : Fin 2 → Cell := twoBank p3526 ray3526
theorem signs3526 : ∀ j, Signs p3526 (bank3526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3527 := params 6
abbrev ray3527 := rays 6
def bank3527 : Fin 2 → Cell := twoBank p3527 ray3527
theorem signs3527 : ∀ j, Signs p3527 (bank3527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3528 := params 7
abbrev ray3528 := rays 7
def bank3528 : Fin 2 → Cell := twoBank p3528 ray3528
theorem signs3528 : ∀ j, Signs p3528 (bank3528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3529 := params 8
abbrev ray3529 := rays 8
def bank3529 : Fin 2 → Cell := twoBank p3529 ray3529
theorem signs3529 : ∀ j, Signs p3529 (bank3529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3530 := params 9
abbrev ray3530 := rays 9
def bank3530 : Fin 2 → Cell := twoBank p3530 ray3530
theorem signs3530 : ∀ j, Signs p3530 (bank3530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3531 := params 10
abbrev ray3531 := rays 10
def bank3531 : Fin 2 → Cell := twoBank p3531 ray3531
theorem signs3531 : ∀ j, Signs p3531 (bank3531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3532 := params 11
abbrev ray3532 := rays 11
def bank3532 : Fin 2 → Cell := twoBank p3532 ray3532
theorem signs3532 : ∀ j, Signs p3532 (bank3532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3533 := params 12
abbrev ray3533 := rays 12
def bank3533 : Fin 2 → Cell := twoBank p3533 ray3533
theorem signs3533 : ∀ j, Signs p3533 (bank3533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3534 := params 13
abbrev ray3534 := rays 13
def bank3534 : Fin 2 → Cell := twoBank p3534 ray3534
theorem signs3534 : ∀ j, Signs p3534 (bank3534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3535 := params 14
abbrev ray3535 := rays 14
def bank3535 : Fin 2 → Cell := twoBank p3535 ray3535
theorem signs3535 : ∀ j, Signs p3535 (bank3535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3536 := params 15
abbrev ray3536 := rays 15
def bank3536 : Fin 2 → Cell := twoBank p3536 ray3536
theorem signs3536 : ∀ j, Signs p3536 (bank3536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3537 := params 16
abbrev ray3537 := rays 16
def bank3537 : Fin 2 → Cell := twoBank p3537 ray3537
theorem signs3537 : ∀ j, Signs p3537 (bank3537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3538 := params 17
abbrev ray3538 := rays 17
def bank3538 : Fin 2 → Cell := twoBank p3538 ray3538
theorem signs3538 : ∀ j, Signs p3538 (bank3538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3539 := params 18
abbrev ray3539 := rays 18
def bank3539 : Fin 2 → Cell := twoBank p3539 ray3539
theorem signs3539 : ∀ j, Signs p3539 (bank3539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3540 := params 19
abbrev ray3540 := rays 19
def bank3540 : Fin 2 → Cell := twoBank p3540 ray3540
theorem signs3540 : ∀ j, Signs p3540 (bank3540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3541 := params 20
abbrev ray3541 := rays 20
def bank3541 : Fin 2 → Cell := twoBank p3541 ray3541
theorem signs3541 : ∀ j, Signs p3541 (bank3541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3542 := params 21
abbrev ray3542 := rays 21
def bank3542 : Fin 2 → Cell := twoBank p3542 ray3542
theorem signs3542 : ∀ j, Signs p3542 (bank3542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3543 := params 22
abbrev ray3543 := rays 22
def bank3543 : Fin 2 → Cell := twoBank p3543 ray3543
theorem signs3543 : ∀ j, Signs p3543 (bank3543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3544 := params 23
abbrev ray3544 := rays 23
def bank3544 : Fin 2 → Cell := twoBank p3544 ray3544
theorem signs3544 : ∀ j, Signs p3544 (bank3544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3545 := params 24
abbrev ray3545 := rays 24
def bank3545 : Fin 2 → Cell := twoBank p3545 ray3545
theorem signs3545 : ∀ j, Signs p3545 (bank3545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3546 := params 25
abbrev ray3546 := rays 25
def bank3546 : Fin 2 → Cell := twoBank p3546 ray3546
theorem signs3546 : ∀ j, Signs p3546 (bank3546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3547 := params 26
abbrev ray3547 := rays 26
def bank3547 : Fin 2 → Cell := twoBank p3547 ray3547
theorem signs3547 : ∀ j, Signs p3547 (bank3547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3548 := params 27
abbrev ray3548 := rays 27
def bank3548 : Fin 2 → Cell := twoBank p3548 ray3548
theorem signs3548 : ∀ j, Signs p3548 (bank3548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3549 := params 28
abbrev ray3549 := rays 28
def bank3549 : Fin 2 → Cell := twoBank p3549 ray3549
theorem signs3549 : ∀ j, Signs p3549 (bank3549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3550 := params 29
abbrev ray3550 := rays 29
def bank3550 : Fin 2 → Cell := twoBank p3550 ray3550
theorem signs3550 : ∀ j, Signs p3550 (bank3550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3551 := params 30
abbrev ray3551 := rays 30
def bank3551 : Fin 2 → Cell := twoBank p3551 ray3551
theorem signs3551 : ∀ j, Signs p3551 (bank3551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3552 := params 31
abbrev ray3552 := rays 31
def bank3552 : Fin 2 → Cell := twoBank p3552 ray3552
theorem signs3552 : ∀ j, Signs p3552 (bank3552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03521_03552
