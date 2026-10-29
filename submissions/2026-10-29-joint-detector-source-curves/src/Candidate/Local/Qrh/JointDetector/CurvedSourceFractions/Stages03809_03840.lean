/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03809_03840
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99323471608656,99323244631447,99323017628858,99322790600890,99322563547544,99322336468821,99322109364723,99321882235251,99321655080405,99321427900187,99321200694599,99320973463641,99320746207314,99320518925620,99320291618560,99320064286135,99319836928346,99319609545194,99319382136680,99319154702806,99318927243572,99318699758980,99318472249031,99318244713726,99318017153066,99317789567053,99317561955687,99317334318970,99317106656903,99316878969487,99316651256723,99316423518612,99316195755156]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3808+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3809 := params 0
abbrev ray3809 := rays 0
def bank3809 : Fin 2 → Cell := twoBank p3809 ray3809
theorem signs3809 : ∀ j, Signs p3809 (bank3809 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3810 := params 1
abbrev ray3810 := rays 1
def bank3810 : Fin 2 → Cell := twoBank p3810 ray3810
theorem signs3810 : ∀ j, Signs p3810 (bank3810 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3811 := params 2
abbrev ray3811 := rays 2
def bank3811 : Fin 2 → Cell := twoBank p3811 ray3811
theorem signs3811 : ∀ j, Signs p3811 (bank3811 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3812 := params 3
abbrev ray3812 := rays 3
def bank3812 : Fin 2 → Cell := twoBank p3812 ray3812
theorem signs3812 : ∀ j, Signs p3812 (bank3812 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3813 := params 4
abbrev ray3813 := rays 4
def bank3813 : Fin 2 → Cell := twoBank p3813 ray3813
theorem signs3813 : ∀ j, Signs p3813 (bank3813 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3814 := params 5
abbrev ray3814 := rays 5
def bank3814 : Fin 2 → Cell := twoBank p3814 ray3814
theorem signs3814 : ∀ j, Signs p3814 (bank3814 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3815 := params 6
abbrev ray3815 := rays 6
def bank3815 : Fin 2 → Cell := twoBank p3815 ray3815
theorem signs3815 : ∀ j, Signs p3815 (bank3815 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3816 := params 7
abbrev ray3816 := rays 7
def bank3816 : Fin 2 → Cell := twoBank p3816 ray3816
theorem signs3816 : ∀ j, Signs p3816 (bank3816 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3817 := params 8
abbrev ray3817 := rays 8
def bank3817 : Fin 2 → Cell := twoBank p3817 ray3817
theorem signs3817 : ∀ j, Signs p3817 (bank3817 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3818 := params 9
abbrev ray3818 := rays 9
def bank3818 : Fin 2 → Cell := twoBank p3818 ray3818
theorem signs3818 : ∀ j, Signs p3818 (bank3818 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3819 := params 10
abbrev ray3819 := rays 10
def bank3819 : Fin 2 → Cell := twoBank p3819 ray3819
theorem signs3819 : ∀ j, Signs p3819 (bank3819 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3820 := params 11
abbrev ray3820 := rays 11
def bank3820 : Fin 2 → Cell := twoBank p3820 ray3820
theorem signs3820 : ∀ j, Signs p3820 (bank3820 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3821 := params 12
abbrev ray3821 := rays 12
def bank3821 : Fin 2 → Cell := twoBank p3821 ray3821
theorem signs3821 : ∀ j, Signs p3821 (bank3821 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3822 := params 13
abbrev ray3822 := rays 13
def bank3822 : Fin 2 → Cell := twoBank p3822 ray3822
theorem signs3822 : ∀ j, Signs p3822 (bank3822 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3823 := params 14
abbrev ray3823 := rays 14
def bank3823 : Fin 2 → Cell := twoBank p3823 ray3823
theorem signs3823 : ∀ j, Signs p3823 (bank3823 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3824 := params 15
abbrev ray3824 := rays 15
def bank3824 : Fin 2 → Cell := twoBank p3824 ray3824
theorem signs3824 : ∀ j, Signs p3824 (bank3824 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3825 := params 16
abbrev ray3825 := rays 16
def bank3825 : Fin 2 → Cell := twoBank p3825 ray3825
theorem signs3825 : ∀ j, Signs p3825 (bank3825 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3826 := params 17
abbrev ray3826 := rays 17
def bank3826 : Fin 2 → Cell := twoBank p3826 ray3826
theorem signs3826 : ∀ j, Signs p3826 (bank3826 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3827 := params 18
abbrev ray3827 := rays 18
def bank3827 : Fin 2 → Cell := twoBank p3827 ray3827
theorem signs3827 : ∀ j, Signs p3827 (bank3827 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3828 := params 19
abbrev ray3828 := rays 19
def bank3828 : Fin 2 → Cell := twoBank p3828 ray3828
theorem signs3828 : ∀ j, Signs p3828 (bank3828 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3829 := params 20
abbrev ray3829 := rays 20
def bank3829 : Fin 2 → Cell := twoBank p3829 ray3829
theorem signs3829 : ∀ j, Signs p3829 (bank3829 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3830 := params 21
abbrev ray3830 := rays 21
def bank3830 : Fin 2 → Cell := twoBank p3830 ray3830
theorem signs3830 : ∀ j, Signs p3830 (bank3830 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3831 := params 22
abbrev ray3831 := rays 22
def bank3831 : Fin 2 → Cell := twoBank p3831 ray3831
theorem signs3831 : ∀ j, Signs p3831 (bank3831 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3832 := params 23
abbrev ray3832 := rays 23
def bank3832 : Fin 2 → Cell := twoBank p3832 ray3832
theorem signs3832 : ∀ j, Signs p3832 (bank3832 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3833 := params 24
abbrev ray3833 := rays 24
def bank3833 : Fin 2 → Cell := twoBank p3833 ray3833
theorem signs3833 : ∀ j, Signs p3833 (bank3833 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3834 := params 25
abbrev ray3834 := rays 25
def bank3834 : Fin 2 → Cell := twoBank p3834 ray3834
theorem signs3834 : ∀ j, Signs p3834 (bank3834 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3835 := params 26
abbrev ray3835 := rays 26
def bank3835 : Fin 2 → Cell := twoBank p3835 ray3835
theorem signs3835 : ∀ j, Signs p3835 (bank3835 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3836 := params 27
abbrev ray3836 := rays 27
def bank3836 : Fin 2 → Cell := twoBank p3836 ray3836
theorem signs3836 : ∀ j, Signs p3836 (bank3836 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3837 := params 28
abbrev ray3837 := rays 28
def bank3837 : Fin 2 → Cell := twoBank p3837 ray3837
theorem signs3837 : ∀ j, Signs p3837 (bank3837 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3838 := params 29
abbrev ray3838 := rays 29
def bank3838 : Fin 2 → Cell := twoBank p3838 ray3838
theorem signs3838 : ∀ j, Signs p3838 (bank3838 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3839 := params 30
abbrev ray3839 := rays 30
def bank3839 : Fin 2 → Cell := twoBank p3839 ray3839
theorem signs3839 : ∀ j, Signs p3839 (bank3839 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3840 := params 31
abbrev ray3840 := rays 31
def bank3840 : Fin 2 → Cell := twoBank p3840 ray3840
theorem signs3840 : ∀ j, Signs p3840 (bank3840 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03809_03840
