/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03777_03808
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99330721471773,99330495307335,99330269117480,99330042902209,99329816661524,99329590395425,99329364103914,99329137786991,99328911444658,99328685076916,99328458683767,99328232265211,99328005821250,99327779351884,99327552857115,99327326336944,99327099791372,99326873220401,99326646624031,99326420002264,99326193355101,99325966682543,99325739984591,99325513261246,99325286512509,99325059738382,99324832938866,99324606113961,99324379263669,99324152387992,99323925486930,99323698560484,99323471608656]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3776+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3777 := params 0
abbrev ray3777 := rays 0
def bank3777 : Fin 2 → Cell := twoBank p3777 ray3777
theorem signs3777 : ∀ j, Signs p3777 (bank3777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3778 := params 1
abbrev ray3778 := rays 1
def bank3778 : Fin 2 → Cell := twoBank p3778 ray3778
theorem signs3778 : ∀ j, Signs p3778 (bank3778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3779 := params 2
abbrev ray3779 := rays 2
def bank3779 : Fin 2 → Cell := twoBank p3779 ray3779
theorem signs3779 : ∀ j, Signs p3779 (bank3779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3780 := params 3
abbrev ray3780 := rays 3
def bank3780 : Fin 2 → Cell := twoBank p3780 ray3780
theorem signs3780 : ∀ j, Signs p3780 (bank3780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3781 := params 4
abbrev ray3781 := rays 4
def bank3781 : Fin 2 → Cell := twoBank p3781 ray3781
theorem signs3781 : ∀ j, Signs p3781 (bank3781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3782 := params 5
abbrev ray3782 := rays 5
def bank3782 : Fin 2 → Cell := twoBank p3782 ray3782
theorem signs3782 : ∀ j, Signs p3782 (bank3782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3783 := params 6
abbrev ray3783 := rays 6
def bank3783 : Fin 2 → Cell := twoBank p3783 ray3783
theorem signs3783 : ∀ j, Signs p3783 (bank3783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3784 := params 7
abbrev ray3784 := rays 7
def bank3784 : Fin 2 → Cell := twoBank p3784 ray3784
theorem signs3784 : ∀ j, Signs p3784 (bank3784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3785 := params 8
abbrev ray3785 := rays 8
def bank3785 : Fin 2 → Cell := twoBank p3785 ray3785
theorem signs3785 : ∀ j, Signs p3785 (bank3785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3786 := params 9
abbrev ray3786 := rays 9
def bank3786 : Fin 2 → Cell := twoBank p3786 ray3786
theorem signs3786 : ∀ j, Signs p3786 (bank3786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3787 := params 10
abbrev ray3787 := rays 10
def bank3787 : Fin 2 → Cell := twoBank p3787 ray3787
theorem signs3787 : ∀ j, Signs p3787 (bank3787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3788 := params 11
abbrev ray3788 := rays 11
def bank3788 : Fin 2 → Cell := twoBank p3788 ray3788
theorem signs3788 : ∀ j, Signs p3788 (bank3788 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3789 := params 12
abbrev ray3789 := rays 12
def bank3789 : Fin 2 → Cell := twoBank p3789 ray3789
theorem signs3789 : ∀ j, Signs p3789 (bank3789 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3790 := params 13
abbrev ray3790 := rays 13
def bank3790 : Fin 2 → Cell := twoBank p3790 ray3790
theorem signs3790 : ∀ j, Signs p3790 (bank3790 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3791 := params 14
abbrev ray3791 := rays 14
def bank3791 : Fin 2 → Cell := twoBank p3791 ray3791
theorem signs3791 : ∀ j, Signs p3791 (bank3791 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3792 := params 15
abbrev ray3792 := rays 15
def bank3792 : Fin 2 → Cell := twoBank p3792 ray3792
theorem signs3792 : ∀ j, Signs p3792 (bank3792 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3793 := params 16
abbrev ray3793 := rays 16
def bank3793 : Fin 2 → Cell := twoBank p3793 ray3793
theorem signs3793 : ∀ j, Signs p3793 (bank3793 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3794 := params 17
abbrev ray3794 := rays 17
def bank3794 : Fin 2 → Cell := twoBank p3794 ray3794
theorem signs3794 : ∀ j, Signs p3794 (bank3794 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3795 := params 18
abbrev ray3795 := rays 18
def bank3795 : Fin 2 → Cell := twoBank p3795 ray3795
theorem signs3795 : ∀ j, Signs p3795 (bank3795 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3796 := params 19
abbrev ray3796 := rays 19
def bank3796 : Fin 2 → Cell := twoBank p3796 ray3796
theorem signs3796 : ∀ j, Signs p3796 (bank3796 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3797 := params 20
abbrev ray3797 := rays 20
def bank3797 : Fin 2 → Cell := twoBank p3797 ray3797
theorem signs3797 : ∀ j, Signs p3797 (bank3797 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3798 := params 21
abbrev ray3798 := rays 21
def bank3798 : Fin 2 → Cell := twoBank p3798 ray3798
theorem signs3798 : ∀ j, Signs p3798 (bank3798 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3799 := params 22
abbrev ray3799 := rays 22
def bank3799 : Fin 2 → Cell := twoBank p3799 ray3799
theorem signs3799 : ∀ j, Signs p3799 (bank3799 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3800 := params 23
abbrev ray3800 := rays 23
def bank3800 : Fin 2 → Cell := twoBank p3800 ray3800
theorem signs3800 : ∀ j, Signs p3800 (bank3800 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3801 := params 24
abbrev ray3801 := rays 24
def bank3801 : Fin 2 → Cell := twoBank p3801 ray3801
theorem signs3801 : ∀ j, Signs p3801 (bank3801 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3802 := params 25
abbrev ray3802 := rays 25
def bank3802 : Fin 2 → Cell := twoBank p3802 ray3802
theorem signs3802 : ∀ j, Signs p3802 (bank3802 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3803 := params 26
abbrev ray3803 := rays 26
def bank3803 : Fin 2 → Cell := twoBank p3803 ray3803
theorem signs3803 : ∀ j, Signs p3803 (bank3803 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3804 := params 27
abbrev ray3804 := rays 27
def bank3804 : Fin 2 → Cell := twoBank p3804 ray3804
theorem signs3804 : ∀ j, Signs p3804 (bank3804 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3805 := params 28
abbrev ray3805 := rays 28
def bank3805 : Fin 2 → Cell := twoBank p3805 ray3805
theorem signs3805 : ∀ j, Signs p3805 (bank3805 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3806 := params 29
abbrev ray3806 := rays 29
def bank3806 : Fin 2 → Cell := twoBank p3806 ray3806
theorem signs3806 : ∀ j, Signs p3806 (bank3806 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3807 := params 30
abbrev ray3807 := rays 30
def bank3807 : Fin 2 → Cell := twoBank p3807 ray3807
theorem signs3807 : ∀ j, Signs p3807 (bank3807 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3808 := params 31
abbrev ray3808 := rays 31
def bank3808 : Fin 2 → Cell := twoBank p3808 ray3808
theorem signs3808 : ∀ j, Signs p3808 (bank3808 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03777_03808
