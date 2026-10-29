/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03585_03616
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99373672723625,99373451460850,99373230172434,99373008858377,99372787518681,99372566153347,99372344762376,99372123345769,99371901903527,99371680435652,99371458942145,99371237423007,99371015878239,99370794307842,99370572711818,99370351090167,99370129442891,99369907769991,99369686071468,99369464347324,99369242597559,99369020822175,99368799021173,99368577194554,99368355342320,99368133464471,99367911561009,99367689631935,99367467677250,99367245696955,99367023691051,99366801659540,99366579602423]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3584+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3585 := params 0
abbrev ray3585 := rays 0
def bank3585 : Fin 2 → Cell := twoBank p3585 ray3585
theorem signs3585 : ∀ j, Signs p3585 (bank3585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3586 := params 1
abbrev ray3586 := rays 1
def bank3586 : Fin 2 → Cell := twoBank p3586 ray3586
theorem signs3586 : ∀ j, Signs p3586 (bank3586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3587 := params 2
abbrev ray3587 := rays 2
def bank3587 : Fin 2 → Cell := twoBank p3587 ray3587
theorem signs3587 : ∀ j, Signs p3587 (bank3587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3588 := params 3
abbrev ray3588 := rays 3
def bank3588 : Fin 2 → Cell := twoBank p3588 ray3588
theorem signs3588 : ∀ j, Signs p3588 (bank3588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3589 := params 4
abbrev ray3589 := rays 4
def bank3589 : Fin 2 → Cell := twoBank p3589 ray3589
theorem signs3589 : ∀ j, Signs p3589 (bank3589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3590 := params 5
abbrev ray3590 := rays 5
def bank3590 : Fin 2 → Cell := twoBank p3590 ray3590
theorem signs3590 : ∀ j, Signs p3590 (bank3590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3591 := params 6
abbrev ray3591 := rays 6
def bank3591 : Fin 2 → Cell := twoBank p3591 ray3591
theorem signs3591 : ∀ j, Signs p3591 (bank3591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3592 := params 7
abbrev ray3592 := rays 7
def bank3592 : Fin 2 → Cell := twoBank p3592 ray3592
theorem signs3592 : ∀ j, Signs p3592 (bank3592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3593 := params 8
abbrev ray3593 := rays 8
def bank3593 : Fin 2 → Cell := twoBank p3593 ray3593
theorem signs3593 : ∀ j, Signs p3593 (bank3593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3594 := params 9
abbrev ray3594 := rays 9
def bank3594 : Fin 2 → Cell := twoBank p3594 ray3594
theorem signs3594 : ∀ j, Signs p3594 (bank3594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3595 := params 10
abbrev ray3595 := rays 10
def bank3595 : Fin 2 → Cell := twoBank p3595 ray3595
theorem signs3595 : ∀ j, Signs p3595 (bank3595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3596 := params 11
abbrev ray3596 := rays 11
def bank3596 : Fin 2 → Cell := twoBank p3596 ray3596
theorem signs3596 : ∀ j, Signs p3596 (bank3596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3597 := params 12
abbrev ray3597 := rays 12
def bank3597 : Fin 2 → Cell := twoBank p3597 ray3597
theorem signs3597 : ∀ j, Signs p3597 (bank3597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3598 := params 13
abbrev ray3598 := rays 13
def bank3598 : Fin 2 → Cell := twoBank p3598 ray3598
theorem signs3598 : ∀ j, Signs p3598 (bank3598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3599 := params 14
abbrev ray3599 := rays 14
def bank3599 : Fin 2 → Cell := twoBank p3599 ray3599
theorem signs3599 : ∀ j, Signs p3599 (bank3599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3600 := params 15
abbrev ray3600 := rays 15
def bank3600 : Fin 2 → Cell := twoBank p3600 ray3600
theorem signs3600 : ∀ j, Signs p3600 (bank3600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3601 := params 16
abbrev ray3601 := rays 16
def bank3601 : Fin 2 → Cell := twoBank p3601 ray3601
theorem signs3601 : ∀ j, Signs p3601 (bank3601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3602 := params 17
abbrev ray3602 := rays 17
def bank3602 : Fin 2 → Cell := twoBank p3602 ray3602
theorem signs3602 : ∀ j, Signs p3602 (bank3602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3603 := params 18
abbrev ray3603 := rays 18
def bank3603 : Fin 2 → Cell := twoBank p3603 ray3603
theorem signs3603 : ∀ j, Signs p3603 (bank3603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3604 := params 19
abbrev ray3604 := rays 19
def bank3604 : Fin 2 → Cell := twoBank p3604 ray3604
theorem signs3604 : ∀ j, Signs p3604 (bank3604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3605 := params 20
abbrev ray3605 := rays 20
def bank3605 : Fin 2 → Cell := twoBank p3605 ray3605
theorem signs3605 : ∀ j, Signs p3605 (bank3605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3606 := params 21
abbrev ray3606 := rays 21
def bank3606 : Fin 2 → Cell := twoBank p3606 ray3606
theorem signs3606 : ∀ j, Signs p3606 (bank3606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3607 := params 22
abbrev ray3607 := rays 22
def bank3607 : Fin 2 → Cell := twoBank p3607 ray3607
theorem signs3607 : ∀ j, Signs p3607 (bank3607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3608 := params 23
abbrev ray3608 := rays 23
def bank3608 : Fin 2 → Cell := twoBank p3608 ray3608
theorem signs3608 : ∀ j, Signs p3608 (bank3608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3609 := params 24
abbrev ray3609 := rays 24
def bank3609 : Fin 2 → Cell := twoBank p3609 ray3609
theorem signs3609 : ∀ j, Signs p3609 (bank3609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3610 := params 25
abbrev ray3610 := rays 25
def bank3610 : Fin 2 → Cell := twoBank p3610 ray3610
theorem signs3610 : ∀ j, Signs p3610 (bank3610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3611 := params 26
abbrev ray3611 := rays 26
def bank3611 : Fin 2 → Cell := twoBank p3611 ray3611
theorem signs3611 : ∀ j, Signs p3611 (bank3611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3612 := params 27
abbrev ray3612 := rays 27
def bank3612 : Fin 2 → Cell := twoBank p3612 ray3612
theorem signs3612 : ∀ j, Signs p3612 (bank3612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3613 := params 28
abbrev ray3613 := rays 28
def bank3613 : Fin 2 → Cell := twoBank p3613 ray3613
theorem signs3613 : ∀ j, Signs p3613 (bank3613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3614 := params 29
abbrev ray3614 := rays 29
def bank3614 : Fin 2 → Cell := twoBank p3614 ray3614
theorem signs3614 : ∀ j, Signs p3614 (bank3614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3615 := params 30
abbrev ray3615 := rays 30
def bank3615 : Fin 2 → Cell := twoBank p3615 ray3615
theorem signs3615 : ∀ j, Signs p3615 (bank3615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3616 := params 31
abbrev ray3616 := rays 31
def bank3616 : Fin 2 → Cell := twoBank p3616 ray3616
theorem signs3616 : ∀ j, Signs p3616 (bank3616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03585_03616
