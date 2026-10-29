/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03617_03648
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99366579602423,99366357519700,99366135411374,99365913277445,99365691117914,99365468932783,99365246722053,99365024485725,99364802223800,99364579936279,99364357623164,99364135284456,99363912920156,99363690530265,99363468114784,99363245673714,99363023207057,99362800714814,99362578196986,99362355653574,99362133084579,99361910490003,99361687869846,99361465224110,99361242552796,99361019855906,99360797133440,99360574385399,99360351611785,99360128812599,99359905987842,99359683137515,99359460261620]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3616+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3617 := params 0
abbrev ray3617 := rays 0
def bank3617 : Fin 2 → Cell := twoBank p3617 ray3617
theorem signs3617 : ∀ j, Signs p3617 (bank3617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3618 := params 1
abbrev ray3618 := rays 1
def bank3618 : Fin 2 → Cell := twoBank p3618 ray3618
theorem signs3618 : ∀ j, Signs p3618 (bank3618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3619 := params 2
abbrev ray3619 := rays 2
def bank3619 : Fin 2 → Cell := twoBank p3619 ray3619
theorem signs3619 : ∀ j, Signs p3619 (bank3619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3620 := params 3
abbrev ray3620 := rays 3
def bank3620 : Fin 2 → Cell := twoBank p3620 ray3620
theorem signs3620 : ∀ j, Signs p3620 (bank3620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3621 := params 4
abbrev ray3621 := rays 4
def bank3621 : Fin 2 → Cell := twoBank p3621 ray3621
theorem signs3621 : ∀ j, Signs p3621 (bank3621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3622 := params 5
abbrev ray3622 := rays 5
def bank3622 : Fin 2 → Cell := twoBank p3622 ray3622
theorem signs3622 : ∀ j, Signs p3622 (bank3622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3623 := params 6
abbrev ray3623 := rays 6
def bank3623 : Fin 2 → Cell := twoBank p3623 ray3623
theorem signs3623 : ∀ j, Signs p3623 (bank3623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3624 := params 7
abbrev ray3624 := rays 7
def bank3624 : Fin 2 → Cell := twoBank p3624 ray3624
theorem signs3624 : ∀ j, Signs p3624 (bank3624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3625 := params 8
abbrev ray3625 := rays 8
def bank3625 : Fin 2 → Cell := twoBank p3625 ray3625
theorem signs3625 : ∀ j, Signs p3625 (bank3625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3626 := params 9
abbrev ray3626 := rays 9
def bank3626 : Fin 2 → Cell := twoBank p3626 ray3626
theorem signs3626 : ∀ j, Signs p3626 (bank3626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3627 := params 10
abbrev ray3627 := rays 10
def bank3627 : Fin 2 → Cell := twoBank p3627 ray3627
theorem signs3627 : ∀ j, Signs p3627 (bank3627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3628 := params 11
abbrev ray3628 := rays 11
def bank3628 : Fin 2 → Cell := twoBank p3628 ray3628
theorem signs3628 : ∀ j, Signs p3628 (bank3628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3629 := params 12
abbrev ray3629 := rays 12
def bank3629 : Fin 2 → Cell := twoBank p3629 ray3629
theorem signs3629 : ∀ j, Signs p3629 (bank3629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3630 := params 13
abbrev ray3630 := rays 13
def bank3630 : Fin 2 → Cell := twoBank p3630 ray3630
theorem signs3630 : ∀ j, Signs p3630 (bank3630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3631 := params 14
abbrev ray3631 := rays 14
def bank3631 : Fin 2 → Cell := twoBank p3631 ray3631
theorem signs3631 : ∀ j, Signs p3631 (bank3631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3632 := params 15
abbrev ray3632 := rays 15
def bank3632 : Fin 2 → Cell := twoBank p3632 ray3632
theorem signs3632 : ∀ j, Signs p3632 (bank3632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3633 := params 16
abbrev ray3633 := rays 16
def bank3633 : Fin 2 → Cell := twoBank p3633 ray3633
theorem signs3633 : ∀ j, Signs p3633 (bank3633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3634 := params 17
abbrev ray3634 := rays 17
def bank3634 : Fin 2 → Cell := twoBank p3634 ray3634
theorem signs3634 : ∀ j, Signs p3634 (bank3634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3635 := params 18
abbrev ray3635 := rays 18
def bank3635 : Fin 2 → Cell := twoBank p3635 ray3635
theorem signs3635 : ∀ j, Signs p3635 (bank3635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3636 := params 19
abbrev ray3636 := rays 19
def bank3636 : Fin 2 → Cell := twoBank p3636 ray3636
theorem signs3636 : ∀ j, Signs p3636 (bank3636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3637 := params 20
abbrev ray3637 := rays 20
def bank3637 : Fin 2 → Cell := twoBank p3637 ray3637
theorem signs3637 : ∀ j, Signs p3637 (bank3637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3638 := params 21
abbrev ray3638 := rays 21
def bank3638 : Fin 2 → Cell := twoBank p3638 ray3638
theorem signs3638 : ∀ j, Signs p3638 (bank3638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3639 := params 22
abbrev ray3639 := rays 22
def bank3639 : Fin 2 → Cell := twoBank p3639 ray3639
theorem signs3639 : ∀ j, Signs p3639 (bank3639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3640 := params 23
abbrev ray3640 := rays 23
def bank3640 : Fin 2 → Cell := twoBank p3640 ray3640
theorem signs3640 : ∀ j, Signs p3640 (bank3640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3641 := params 24
abbrev ray3641 := rays 24
def bank3641 : Fin 2 → Cell := twoBank p3641 ray3641
theorem signs3641 : ∀ j, Signs p3641 (bank3641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3642 := params 25
abbrev ray3642 := rays 25
def bank3642 : Fin 2 → Cell := twoBank p3642 ray3642
theorem signs3642 : ∀ j, Signs p3642 (bank3642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3643 := params 26
abbrev ray3643 := rays 26
def bank3643 : Fin 2 → Cell := twoBank p3643 ray3643
theorem signs3643 : ∀ j, Signs p3643 (bank3643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3644 := params 27
abbrev ray3644 := rays 27
def bank3644 : Fin 2 → Cell := twoBank p3644 ray3644
theorem signs3644 : ∀ j, Signs p3644 (bank3644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3645 := params 28
abbrev ray3645 := rays 28
def bank3645 : Fin 2 → Cell := twoBank p3645 ray3645
theorem signs3645 : ∀ j, Signs p3645 (bank3645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3646 := params 29
abbrev ray3646 := rays 29
def bank3646 : Fin 2 → Cell := twoBank p3646 ray3646
theorem signs3646 : ∀ j, Signs p3646 (bank3646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3647 := params 30
abbrev ray3647 := rays 30
def bank3647 : Fin 2 → Cell := twoBank p3647 ray3647
theorem signs3647 : ∀ j, Signs p3647 (bank3647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3648 := params 31
abbrev ray3648 := rays 31
def bank3648 : Fin 2 → Cell := twoBank p3648 ray3648
theorem signs3648 : ∀ j, Signs p3648 (bank3648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03617_03648
