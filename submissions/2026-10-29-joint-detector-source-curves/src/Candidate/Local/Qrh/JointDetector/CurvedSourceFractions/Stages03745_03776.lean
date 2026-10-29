/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03745_03776
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99337945306675,99337719956193,99337494580257,99337269178868,99337043752027,99336818299735,99336592821994,99336367318805,99336141790169,99335916236087,99335690656560,99335465051589,99335239421176,99335013765321,99334788084026,99334562377292,99334336645120,99334110887512,99333885104468,99333659295990,99333433462079,99333207602735,99332981717961,99332755807757,99332529872124,99332303911064,99332077924578,99331851912666,99331625875331,99331399812573,99331173724393,99330947610793,99330721471773]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3744+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3745 := params 0
abbrev ray3745 := rays 0
def bank3745 : Fin 2 → Cell := twoBank p3745 ray3745
theorem signs3745 : ∀ j, Signs p3745 (bank3745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3746 := params 1
abbrev ray3746 := rays 1
def bank3746 : Fin 2 → Cell := twoBank p3746 ray3746
theorem signs3746 : ∀ j, Signs p3746 (bank3746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3747 := params 2
abbrev ray3747 := rays 2
def bank3747 : Fin 2 → Cell := twoBank p3747 ray3747
theorem signs3747 : ∀ j, Signs p3747 (bank3747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3748 := params 3
abbrev ray3748 := rays 3
def bank3748 : Fin 2 → Cell := twoBank p3748 ray3748
theorem signs3748 : ∀ j, Signs p3748 (bank3748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3749 := params 4
abbrev ray3749 := rays 4
def bank3749 : Fin 2 → Cell := twoBank p3749 ray3749
theorem signs3749 : ∀ j, Signs p3749 (bank3749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3750 := params 5
abbrev ray3750 := rays 5
def bank3750 : Fin 2 → Cell := twoBank p3750 ray3750
theorem signs3750 : ∀ j, Signs p3750 (bank3750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3751 := params 6
abbrev ray3751 := rays 6
def bank3751 : Fin 2 → Cell := twoBank p3751 ray3751
theorem signs3751 : ∀ j, Signs p3751 (bank3751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3752 := params 7
abbrev ray3752 := rays 7
def bank3752 : Fin 2 → Cell := twoBank p3752 ray3752
theorem signs3752 : ∀ j, Signs p3752 (bank3752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3753 := params 8
abbrev ray3753 := rays 8
def bank3753 : Fin 2 → Cell := twoBank p3753 ray3753
theorem signs3753 : ∀ j, Signs p3753 (bank3753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3754 := params 9
abbrev ray3754 := rays 9
def bank3754 : Fin 2 → Cell := twoBank p3754 ray3754
theorem signs3754 : ∀ j, Signs p3754 (bank3754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3755 := params 10
abbrev ray3755 := rays 10
def bank3755 : Fin 2 → Cell := twoBank p3755 ray3755
theorem signs3755 : ∀ j, Signs p3755 (bank3755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3756 := params 11
abbrev ray3756 := rays 11
def bank3756 : Fin 2 → Cell := twoBank p3756 ray3756
theorem signs3756 : ∀ j, Signs p3756 (bank3756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3757 := params 12
abbrev ray3757 := rays 12
def bank3757 : Fin 2 → Cell := twoBank p3757 ray3757
theorem signs3757 : ∀ j, Signs p3757 (bank3757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3758 := params 13
abbrev ray3758 := rays 13
def bank3758 : Fin 2 → Cell := twoBank p3758 ray3758
theorem signs3758 : ∀ j, Signs p3758 (bank3758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3759 := params 14
abbrev ray3759 := rays 14
def bank3759 : Fin 2 → Cell := twoBank p3759 ray3759
theorem signs3759 : ∀ j, Signs p3759 (bank3759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3760 := params 15
abbrev ray3760 := rays 15
def bank3760 : Fin 2 → Cell := twoBank p3760 ray3760
theorem signs3760 : ∀ j, Signs p3760 (bank3760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3761 := params 16
abbrev ray3761 := rays 16
def bank3761 : Fin 2 → Cell := twoBank p3761 ray3761
theorem signs3761 : ∀ j, Signs p3761 (bank3761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3762 := params 17
abbrev ray3762 := rays 17
def bank3762 : Fin 2 → Cell := twoBank p3762 ray3762
theorem signs3762 : ∀ j, Signs p3762 (bank3762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3763 := params 18
abbrev ray3763 := rays 18
def bank3763 : Fin 2 → Cell := twoBank p3763 ray3763
theorem signs3763 : ∀ j, Signs p3763 (bank3763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3764 := params 19
abbrev ray3764 := rays 19
def bank3764 : Fin 2 → Cell := twoBank p3764 ray3764
theorem signs3764 : ∀ j, Signs p3764 (bank3764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3765 := params 20
abbrev ray3765 := rays 20
def bank3765 : Fin 2 → Cell := twoBank p3765 ray3765
theorem signs3765 : ∀ j, Signs p3765 (bank3765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3766 := params 21
abbrev ray3766 := rays 21
def bank3766 : Fin 2 → Cell := twoBank p3766 ray3766
theorem signs3766 : ∀ j, Signs p3766 (bank3766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3767 := params 22
abbrev ray3767 := rays 22
def bank3767 : Fin 2 → Cell := twoBank p3767 ray3767
theorem signs3767 : ∀ j, Signs p3767 (bank3767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3768 := params 23
abbrev ray3768 := rays 23
def bank3768 : Fin 2 → Cell := twoBank p3768 ray3768
theorem signs3768 : ∀ j, Signs p3768 (bank3768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3769 := params 24
abbrev ray3769 := rays 24
def bank3769 : Fin 2 → Cell := twoBank p3769 ray3769
theorem signs3769 : ∀ j, Signs p3769 (bank3769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3770 := params 25
abbrev ray3770 := rays 25
def bank3770 : Fin 2 → Cell := twoBank p3770 ray3770
theorem signs3770 : ∀ j, Signs p3770 (bank3770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3771 := params 26
abbrev ray3771 := rays 26
def bank3771 : Fin 2 → Cell := twoBank p3771 ray3771
theorem signs3771 : ∀ j, Signs p3771 (bank3771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3772 := params 27
abbrev ray3772 := rays 27
def bank3772 : Fin 2 → Cell := twoBank p3772 ray3772
theorem signs3772 : ∀ j, Signs p3772 (bank3772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3773 := params 28
abbrev ray3773 := rays 28
def bank3773 : Fin 2 → Cell := twoBank p3773 ray3773
theorem signs3773 : ∀ j, Signs p3773 (bank3773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3774 := params 29
abbrev ray3774 := rays 29
def bank3774 : Fin 2 → Cell := twoBank p3774 ray3774
theorem signs3774 : ∀ j, Signs p3774 (bank3774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3775 := params 30
abbrev ray3775 := rays 30
def bank3775 : Fin 2 → Cell := twoBank p3775 ray3775
theorem signs3775 : ∀ j, Signs p3775 (bank3775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3776 := params 31
abbrev ray3776 := rays 31
def bank3776 : Fin 2 → Cell := twoBank p3776 ray3776
theorem signs3776 : ∀ j, Signs p3776 (bank3776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03745_03776
