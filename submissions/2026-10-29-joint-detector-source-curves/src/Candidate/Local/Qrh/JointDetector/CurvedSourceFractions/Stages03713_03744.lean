/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03713_03744
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99345143075393,99344918540055,99344693979226,99344469392907,99344244781099,99344020143803,99343795481020,99343570792752,99343346079000,99343121339765,99342896575048,99342671784850,99342446969172,99342222128016,99341997261382,99341772369272,99341547451687,99341322508628,99341097540096,99340872546093,99340647526620,99340422481677,99340197411266,99339972315389,99339747194046,99339522047238,99339296874967,99339071677234,99338846454040,99338621205386,99338395931273,99338170631702,99337945306675]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3712+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3713 := params 0
abbrev ray3713 := rays 0
def bank3713 : Fin 2 → Cell := twoBank p3713 ray3713
theorem signs3713 : ∀ j, Signs p3713 (bank3713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3714 := params 1
abbrev ray3714 := rays 1
def bank3714 : Fin 2 → Cell := twoBank p3714 ray3714
theorem signs3714 : ∀ j, Signs p3714 (bank3714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3715 := params 2
abbrev ray3715 := rays 2
def bank3715 : Fin 2 → Cell := twoBank p3715 ray3715
theorem signs3715 : ∀ j, Signs p3715 (bank3715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3716 := params 3
abbrev ray3716 := rays 3
def bank3716 : Fin 2 → Cell := twoBank p3716 ray3716
theorem signs3716 : ∀ j, Signs p3716 (bank3716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3717 := params 4
abbrev ray3717 := rays 4
def bank3717 : Fin 2 → Cell := twoBank p3717 ray3717
theorem signs3717 : ∀ j, Signs p3717 (bank3717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3718 := params 5
abbrev ray3718 := rays 5
def bank3718 : Fin 2 → Cell := twoBank p3718 ray3718
theorem signs3718 : ∀ j, Signs p3718 (bank3718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3719 := params 6
abbrev ray3719 := rays 6
def bank3719 : Fin 2 → Cell := twoBank p3719 ray3719
theorem signs3719 : ∀ j, Signs p3719 (bank3719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3720 := params 7
abbrev ray3720 := rays 7
def bank3720 : Fin 2 → Cell := twoBank p3720 ray3720
theorem signs3720 : ∀ j, Signs p3720 (bank3720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3721 := params 8
abbrev ray3721 := rays 8
def bank3721 : Fin 2 → Cell := twoBank p3721 ray3721
theorem signs3721 : ∀ j, Signs p3721 (bank3721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3722 := params 9
abbrev ray3722 := rays 9
def bank3722 : Fin 2 → Cell := twoBank p3722 ray3722
theorem signs3722 : ∀ j, Signs p3722 (bank3722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3723 := params 10
abbrev ray3723 := rays 10
def bank3723 : Fin 2 → Cell := twoBank p3723 ray3723
theorem signs3723 : ∀ j, Signs p3723 (bank3723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3724 := params 11
abbrev ray3724 := rays 11
def bank3724 : Fin 2 → Cell := twoBank p3724 ray3724
theorem signs3724 : ∀ j, Signs p3724 (bank3724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3725 := params 12
abbrev ray3725 := rays 12
def bank3725 : Fin 2 → Cell := twoBank p3725 ray3725
theorem signs3725 : ∀ j, Signs p3725 (bank3725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3726 := params 13
abbrev ray3726 := rays 13
def bank3726 : Fin 2 → Cell := twoBank p3726 ray3726
theorem signs3726 : ∀ j, Signs p3726 (bank3726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3727 := params 14
abbrev ray3727 := rays 14
def bank3727 : Fin 2 → Cell := twoBank p3727 ray3727
theorem signs3727 : ∀ j, Signs p3727 (bank3727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3728 := params 15
abbrev ray3728 := rays 15
def bank3728 : Fin 2 → Cell := twoBank p3728 ray3728
theorem signs3728 : ∀ j, Signs p3728 (bank3728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3729 := params 16
abbrev ray3729 := rays 16
def bank3729 : Fin 2 → Cell := twoBank p3729 ray3729
theorem signs3729 : ∀ j, Signs p3729 (bank3729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3730 := params 17
abbrev ray3730 := rays 17
def bank3730 : Fin 2 → Cell := twoBank p3730 ray3730
theorem signs3730 : ∀ j, Signs p3730 (bank3730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3731 := params 18
abbrev ray3731 := rays 18
def bank3731 : Fin 2 → Cell := twoBank p3731 ray3731
theorem signs3731 : ∀ j, Signs p3731 (bank3731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3732 := params 19
abbrev ray3732 := rays 19
def bank3732 : Fin 2 → Cell := twoBank p3732 ray3732
theorem signs3732 : ∀ j, Signs p3732 (bank3732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3733 := params 20
abbrev ray3733 := rays 20
def bank3733 : Fin 2 → Cell := twoBank p3733 ray3733
theorem signs3733 : ∀ j, Signs p3733 (bank3733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3734 := params 21
abbrev ray3734 := rays 21
def bank3734 : Fin 2 → Cell := twoBank p3734 ray3734
theorem signs3734 : ∀ j, Signs p3734 (bank3734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3735 := params 22
abbrev ray3735 := rays 22
def bank3735 : Fin 2 → Cell := twoBank p3735 ray3735
theorem signs3735 : ∀ j, Signs p3735 (bank3735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3736 := params 23
abbrev ray3736 := rays 23
def bank3736 : Fin 2 → Cell := twoBank p3736 ray3736
theorem signs3736 : ∀ j, Signs p3736 (bank3736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3737 := params 24
abbrev ray3737 := rays 24
def bank3737 : Fin 2 → Cell := twoBank p3737 ray3737
theorem signs3737 : ∀ j, Signs p3737 (bank3737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3738 := params 25
abbrev ray3738 := rays 25
def bank3738 : Fin 2 → Cell := twoBank p3738 ray3738
theorem signs3738 : ∀ j, Signs p3738 (bank3738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3739 := params 26
abbrev ray3739 := rays 26
def bank3739 : Fin 2 → Cell := twoBank p3739 ray3739
theorem signs3739 : ∀ j, Signs p3739 (bank3739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3740 := params 27
abbrev ray3740 := rays 27
def bank3740 : Fin 2 → Cell := twoBank p3740 ray3740
theorem signs3740 : ∀ j, Signs p3740 (bank3740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3741 := params 28
abbrev ray3741 := rays 28
def bank3741 : Fin 2 → Cell := twoBank p3741 ray3741
theorem signs3741 : ∀ j, Signs p3741 (bank3741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3742 := params 29
abbrev ray3742 := rays 29
def bank3742 : Fin 2 → Cell := twoBank p3742 ray3742
theorem signs3742 : ∀ j, Signs p3742 (bank3742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3743 := params 30
abbrev ray3743 := rays 30
def bank3743 : Fin 2 → Cell := twoBank p3743 ray3743
theorem signs3743 : ∀ j, Signs p3743 (bank3743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3744 := params 31
abbrev ray3744 := rays 31
def bank3744 : Fin 2 → Cell := twoBank p3744 ray3744
theorem signs3744 : ∀ j, Signs p3744 (bank3744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03713_03744
