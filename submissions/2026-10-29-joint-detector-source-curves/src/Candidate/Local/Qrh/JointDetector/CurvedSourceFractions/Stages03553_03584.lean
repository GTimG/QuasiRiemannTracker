/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03553_03584
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99380739586496,99380519144882,99380298677588,99380078184616,99379857665967,99379637121642,99379416551642,99379195955968,99378975334621,99378754687603,99378534014915,99378313316558,99378092592533,99377871842841,99377651067484,99377430266463,99377209439779,99376988587433,99376767709426,99376546805760,99376325876435,99376104921453,99375883940815,99375662934523,99375441902577,99375220844979,99374999761730,99374778652831,99374557518283,99374336358087,99374115172245,99373893960757,99373672723625]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3552+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3553 := params 0
abbrev ray3553 := rays 0
def bank3553 : Fin 2 → Cell := twoBank p3553 ray3553
theorem signs3553 : ∀ j, Signs p3553 (bank3553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3554 := params 1
abbrev ray3554 := rays 1
def bank3554 : Fin 2 → Cell := twoBank p3554 ray3554
theorem signs3554 : ∀ j, Signs p3554 (bank3554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3555 := params 2
abbrev ray3555 := rays 2
def bank3555 : Fin 2 → Cell := twoBank p3555 ray3555
theorem signs3555 : ∀ j, Signs p3555 (bank3555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3556 := params 3
abbrev ray3556 := rays 3
def bank3556 : Fin 2 → Cell := twoBank p3556 ray3556
theorem signs3556 : ∀ j, Signs p3556 (bank3556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3557 := params 4
abbrev ray3557 := rays 4
def bank3557 : Fin 2 → Cell := twoBank p3557 ray3557
theorem signs3557 : ∀ j, Signs p3557 (bank3557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3558 := params 5
abbrev ray3558 := rays 5
def bank3558 : Fin 2 → Cell := twoBank p3558 ray3558
theorem signs3558 : ∀ j, Signs p3558 (bank3558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3559 := params 6
abbrev ray3559 := rays 6
def bank3559 : Fin 2 → Cell := twoBank p3559 ray3559
theorem signs3559 : ∀ j, Signs p3559 (bank3559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3560 := params 7
abbrev ray3560 := rays 7
def bank3560 : Fin 2 → Cell := twoBank p3560 ray3560
theorem signs3560 : ∀ j, Signs p3560 (bank3560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3561 := params 8
abbrev ray3561 := rays 8
def bank3561 : Fin 2 → Cell := twoBank p3561 ray3561
theorem signs3561 : ∀ j, Signs p3561 (bank3561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3562 := params 9
abbrev ray3562 := rays 9
def bank3562 : Fin 2 → Cell := twoBank p3562 ray3562
theorem signs3562 : ∀ j, Signs p3562 (bank3562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3563 := params 10
abbrev ray3563 := rays 10
def bank3563 : Fin 2 → Cell := twoBank p3563 ray3563
theorem signs3563 : ∀ j, Signs p3563 (bank3563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3564 := params 11
abbrev ray3564 := rays 11
def bank3564 : Fin 2 → Cell := twoBank p3564 ray3564
theorem signs3564 : ∀ j, Signs p3564 (bank3564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3565 := params 12
abbrev ray3565 := rays 12
def bank3565 : Fin 2 → Cell := twoBank p3565 ray3565
theorem signs3565 : ∀ j, Signs p3565 (bank3565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3566 := params 13
abbrev ray3566 := rays 13
def bank3566 : Fin 2 → Cell := twoBank p3566 ray3566
theorem signs3566 : ∀ j, Signs p3566 (bank3566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3567 := params 14
abbrev ray3567 := rays 14
def bank3567 : Fin 2 → Cell := twoBank p3567 ray3567
theorem signs3567 : ∀ j, Signs p3567 (bank3567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3568 := params 15
abbrev ray3568 := rays 15
def bank3568 : Fin 2 → Cell := twoBank p3568 ray3568
theorem signs3568 : ∀ j, Signs p3568 (bank3568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3569 := params 16
abbrev ray3569 := rays 16
def bank3569 : Fin 2 → Cell := twoBank p3569 ray3569
theorem signs3569 : ∀ j, Signs p3569 (bank3569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3570 := params 17
abbrev ray3570 := rays 17
def bank3570 : Fin 2 → Cell := twoBank p3570 ray3570
theorem signs3570 : ∀ j, Signs p3570 (bank3570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3571 := params 18
abbrev ray3571 := rays 18
def bank3571 : Fin 2 → Cell := twoBank p3571 ray3571
theorem signs3571 : ∀ j, Signs p3571 (bank3571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3572 := params 19
abbrev ray3572 := rays 19
def bank3572 : Fin 2 → Cell := twoBank p3572 ray3572
theorem signs3572 : ∀ j, Signs p3572 (bank3572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3573 := params 20
abbrev ray3573 := rays 20
def bank3573 : Fin 2 → Cell := twoBank p3573 ray3573
theorem signs3573 : ∀ j, Signs p3573 (bank3573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3574 := params 21
abbrev ray3574 := rays 21
def bank3574 : Fin 2 → Cell := twoBank p3574 ray3574
theorem signs3574 : ∀ j, Signs p3574 (bank3574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3575 := params 22
abbrev ray3575 := rays 22
def bank3575 : Fin 2 → Cell := twoBank p3575 ray3575
theorem signs3575 : ∀ j, Signs p3575 (bank3575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3576 := params 23
abbrev ray3576 := rays 23
def bank3576 : Fin 2 → Cell := twoBank p3576 ray3576
theorem signs3576 : ∀ j, Signs p3576 (bank3576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3577 := params 24
abbrev ray3577 := rays 24
def bank3577 : Fin 2 → Cell := twoBank p3577 ray3577
theorem signs3577 : ∀ j, Signs p3577 (bank3577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3578 := params 25
abbrev ray3578 := rays 25
def bank3578 : Fin 2 → Cell := twoBank p3578 ray3578
theorem signs3578 : ∀ j, Signs p3578 (bank3578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3579 := params 26
abbrev ray3579 := rays 26
def bank3579 : Fin 2 → Cell := twoBank p3579 ray3579
theorem signs3579 : ∀ j, Signs p3579 (bank3579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3580 := params 27
abbrev ray3580 := rays 27
def bank3580 : Fin 2 → Cell := twoBank p3580 ray3580
theorem signs3580 : ∀ j, Signs p3580 (bank3580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3581 := params 28
abbrev ray3581 := rays 28
def bank3581 : Fin 2 → Cell := twoBank p3581 ray3581
theorem signs3581 : ∀ j, Signs p3581 (bank3581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3582 := params 29
abbrev ray3582 := rays 29
def bank3582 : Fin 2 → Cell := twoBank p3582 ray3582
theorem signs3582 : ∀ j, Signs p3582 (bank3582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3583 := params 30
abbrev ray3583 := rays 30
def bank3583 : Fin 2 → Cell := twoBank p3583 ray3583
theorem signs3583 : ∀ j, Signs p3583 (bank3583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3584 := params 31
abbrev ray3584 := rays 31
def bank3584 : Fin 2 → Cell := twoBank p3584 ray3584
theorem signs3584 : ∀ j, Signs p3584 (bank3584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03553_03584
