/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03649_03680
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99359460261620,99359237360157,99359014433128,99358791480534,99358568502376,99358345498656,99358122469374,99357899414532,99357676334131,99357453228172,99357230096656,99357006939584,99356783756958,99356560548778,99356337315046,99356114055763,99355890770931,99355667460550,99355444124622,99355220763147,99354997376127,99354773963563,99354550525457,99354327061809,99354103572621,99353880057893,99353656517627,99353432951824,99353209360486,99352985743613,99352762101207,99352538433269,99352314739800]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3648+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3649 := params 0
abbrev ray3649 := rays 0
def bank3649 : Fin 2 → Cell := twoBank p3649 ray3649
theorem signs3649 : ∀ j, Signs p3649 (bank3649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3650 := params 1
abbrev ray3650 := rays 1
def bank3650 : Fin 2 → Cell := twoBank p3650 ray3650
theorem signs3650 : ∀ j, Signs p3650 (bank3650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3651 := params 2
abbrev ray3651 := rays 2
def bank3651 : Fin 2 → Cell := twoBank p3651 ray3651
theorem signs3651 : ∀ j, Signs p3651 (bank3651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3652 := params 3
abbrev ray3652 := rays 3
def bank3652 : Fin 2 → Cell := twoBank p3652 ray3652
theorem signs3652 : ∀ j, Signs p3652 (bank3652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3653 := params 4
abbrev ray3653 := rays 4
def bank3653 : Fin 2 → Cell := twoBank p3653 ray3653
theorem signs3653 : ∀ j, Signs p3653 (bank3653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3654 := params 5
abbrev ray3654 := rays 5
def bank3654 : Fin 2 → Cell := twoBank p3654 ray3654
theorem signs3654 : ∀ j, Signs p3654 (bank3654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3655 := params 6
abbrev ray3655 := rays 6
def bank3655 : Fin 2 → Cell := twoBank p3655 ray3655
theorem signs3655 : ∀ j, Signs p3655 (bank3655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3656 := params 7
abbrev ray3656 := rays 7
def bank3656 : Fin 2 → Cell := twoBank p3656 ray3656
theorem signs3656 : ∀ j, Signs p3656 (bank3656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3657 := params 8
abbrev ray3657 := rays 8
def bank3657 : Fin 2 → Cell := twoBank p3657 ray3657
theorem signs3657 : ∀ j, Signs p3657 (bank3657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3658 := params 9
abbrev ray3658 := rays 9
def bank3658 : Fin 2 → Cell := twoBank p3658 ray3658
theorem signs3658 : ∀ j, Signs p3658 (bank3658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3659 := params 10
abbrev ray3659 := rays 10
def bank3659 : Fin 2 → Cell := twoBank p3659 ray3659
theorem signs3659 : ∀ j, Signs p3659 (bank3659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3660 := params 11
abbrev ray3660 := rays 11
def bank3660 : Fin 2 → Cell := twoBank p3660 ray3660
theorem signs3660 : ∀ j, Signs p3660 (bank3660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3661 := params 12
abbrev ray3661 := rays 12
def bank3661 : Fin 2 → Cell := twoBank p3661 ray3661
theorem signs3661 : ∀ j, Signs p3661 (bank3661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3662 := params 13
abbrev ray3662 := rays 13
def bank3662 : Fin 2 → Cell := twoBank p3662 ray3662
theorem signs3662 : ∀ j, Signs p3662 (bank3662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3663 := params 14
abbrev ray3663 := rays 14
def bank3663 : Fin 2 → Cell := twoBank p3663 ray3663
theorem signs3663 : ∀ j, Signs p3663 (bank3663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3664 := params 15
abbrev ray3664 := rays 15
def bank3664 : Fin 2 → Cell := twoBank p3664 ray3664
theorem signs3664 : ∀ j, Signs p3664 (bank3664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3665 := params 16
abbrev ray3665 := rays 16
def bank3665 : Fin 2 → Cell := twoBank p3665 ray3665
theorem signs3665 : ∀ j, Signs p3665 (bank3665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3666 := params 17
abbrev ray3666 := rays 17
def bank3666 : Fin 2 → Cell := twoBank p3666 ray3666
theorem signs3666 : ∀ j, Signs p3666 (bank3666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3667 := params 18
abbrev ray3667 := rays 18
def bank3667 : Fin 2 → Cell := twoBank p3667 ray3667
theorem signs3667 : ∀ j, Signs p3667 (bank3667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3668 := params 19
abbrev ray3668 := rays 19
def bank3668 : Fin 2 → Cell := twoBank p3668 ray3668
theorem signs3668 : ∀ j, Signs p3668 (bank3668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3669 := params 20
abbrev ray3669 := rays 20
def bank3669 : Fin 2 → Cell := twoBank p3669 ray3669
theorem signs3669 : ∀ j, Signs p3669 (bank3669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3670 := params 21
abbrev ray3670 := rays 21
def bank3670 : Fin 2 → Cell := twoBank p3670 ray3670
theorem signs3670 : ∀ j, Signs p3670 (bank3670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3671 := params 22
abbrev ray3671 := rays 22
def bank3671 : Fin 2 → Cell := twoBank p3671 ray3671
theorem signs3671 : ∀ j, Signs p3671 (bank3671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3672 := params 23
abbrev ray3672 := rays 23
def bank3672 : Fin 2 → Cell := twoBank p3672 ray3672
theorem signs3672 : ∀ j, Signs p3672 (bank3672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3673 := params 24
abbrev ray3673 := rays 24
def bank3673 : Fin 2 → Cell := twoBank p3673 ray3673
theorem signs3673 : ∀ j, Signs p3673 (bank3673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3674 := params 25
abbrev ray3674 := rays 25
def bank3674 : Fin 2 → Cell := twoBank p3674 ray3674
theorem signs3674 : ∀ j, Signs p3674 (bank3674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3675 := params 26
abbrev ray3675 := rays 26
def bank3675 : Fin 2 → Cell := twoBank p3675 ray3675
theorem signs3675 : ∀ j, Signs p3675 (bank3675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3676 := params 27
abbrev ray3676 := rays 27
def bank3676 : Fin 2 → Cell := twoBank p3676 ray3676
theorem signs3676 : ∀ j, Signs p3676 (bank3676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3677 := params 28
abbrev ray3677 := rays 28
def bank3677 : Fin 2 → Cell := twoBank p3677 ray3677
theorem signs3677 : ∀ j, Signs p3677 (bank3677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3678 := params 29
abbrev ray3678 := rays 29
def bank3678 : Fin 2 → Cell := twoBank p3678 ray3678
theorem signs3678 : ∀ j, Signs p3678 (bank3678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3679 := params 30
abbrev ray3679 := rays 30
def bank3679 : Fin 2 → Cell := twoBank p3679 ray3679
theorem signs3679 : ∀ j, Signs p3679 (bank3679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3680 := params 31
abbrev ray3680 := rays 31
def bank3680 : Fin 2 → Cell := twoBank p3680 ray3680
theorem signs3680 : ∀ j, Signs p3680 (bank3680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03649_03680
