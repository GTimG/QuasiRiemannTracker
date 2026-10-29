/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03841_03872
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99316195755156,99315967966355,99315740152211,99315512312725,99315284447898,99315056557731,99314828642225,99314600701382,99314372735202,99314144743687,99313916726838,99313688684656,99313460617142,99313232524297,99313004406123,99312776262621,99312548093791,99312319899635,99312091680154,99311863435349,99311635165222,99311406869773,99311178549004,99310950202916,99310721831510,99310493434787,99310265012748,99310036565394,99309808092727,99309579594747,99309351071456,99309122522855,99308893948945]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3840+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3841 := params 0
abbrev ray3841 := rays 0
def bank3841 : Fin 2 → Cell := twoBank p3841 ray3841
theorem signs3841 : ∀ j, Signs p3841 (bank3841 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3842 := params 1
abbrev ray3842 := rays 1
def bank3842 : Fin 2 → Cell := twoBank p3842 ray3842
theorem signs3842 : ∀ j, Signs p3842 (bank3842 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3843 := params 2
abbrev ray3843 := rays 2
def bank3843 : Fin 2 → Cell := twoBank p3843 ray3843
theorem signs3843 : ∀ j, Signs p3843 (bank3843 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3844 := params 3
abbrev ray3844 := rays 3
def bank3844 : Fin 2 → Cell := twoBank p3844 ray3844
theorem signs3844 : ∀ j, Signs p3844 (bank3844 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3845 := params 4
abbrev ray3845 := rays 4
def bank3845 : Fin 2 → Cell := twoBank p3845 ray3845
theorem signs3845 : ∀ j, Signs p3845 (bank3845 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3846 := params 5
abbrev ray3846 := rays 5
def bank3846 : Fin 2 → Cell := twoBank p3846 ray3846
theorem signs3846 : ∀ j, Signs p3846 (bank3846 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3847 := params 6
abbrev ray3847 := rays 6
def bank3847 : Fin 2 → Cell := twoBank p3847 ray3847
theorem signs3847 : ∀ j, Signs p3847 (bank3847 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3848 := params 7
abbrev ray3848 := rays 7
def bank3848 : Fin 2 → Cell := twoBank p3848 ray3848
theorem signs3848 : ∀ j, Signs p3848 (bank3848 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3849 := params 8
abbrev ray3849 := rays 8
def bank3849 : Fin 2 → Cell := twoBank p3849 ray3849
theorem signs3849 : ∀ j, Signs p3849 (bank3849 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3850 := params 9
abbrev ray3850 := rays 9
def bank3850 : Fin 2 → Cell := twoBank p3850 ray3850
theorem signs3850 : ∀ j, Signs p3850 (bank3850 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3851 := params 10
abbrev ray3851 := rays 10
def bank3851 : Fin 2 → Cell := twoBank p3851 ray3851
theorem signs3851 : ∀ j, Signs p3851 (bank3851 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3852 := params 11
abbrev ray3852 := rays 11
def bank3852 : Fin 2 → Cell := twoBank p3852 ray3852
theorem signs3852 : ∀ j, Signs p3852 (bank3852 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3853 := params 12
abbrev ray3853 := rays 12
def bank3853 : Fin 2 → Cell := twoBank p3853 ray3853
theorem signs3853 : ∀ j, Signs p3853 (bank3853 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3854 := params 13
abbrev ray3854 := rays 13
def bank3854 : Fin 2 → Cell := twoBank p3854 ray3854
theorem signs3854 : ∀ j, Signs p3854 (bank3854 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3855 := params 14
abbrev ray3855 := rays 14
def bank3855 : Fin 2 → Cell := twoBank p3855 ray3855
theorem signs3855 : ∀ j, Signs p3855 (bank3855 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3856 := params 15
abbrev ray3856 := rays 15
def bank3856 : Fin 2 → Cell := twoBank p3856 ray3856
theorem signs3856 : ∀ j, Signs p3856 (bank3856 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3857 := params 16
abbrev ray3857 := rays 16
def bank3857 : Fin 2 → Cell := twoBank p3857 ray3857
theorem signs3857 : ∀ j, Signs p3857 (bank3857 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3858 := params 17
abbrev ray3858 := rays 17
def bank3858 : Fin 2 → Cell := twoBank p3858 ray3858
theorem signs3858 : ∀ j, Signs p3858 (bank3858 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3859 := params 18
abbrev ray3859 := rays 18
def bank3859 : Fin 2 → Cell := twoBank p3859 ray3859
theorem signs3859 : ∀ j, Signs p3859 (bank3859 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3860 := params 19
abbrev ray3860 := rays 19
def bank3860 : Fin 2 → Cell := twoBank p3860 ray3860
theorem signs3860 : ∀ j, Signs p3860 (bank3860 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3861 := params 20
abbrev ray3861 := rays 20
def bank3861 : Fin 2 → Cell := twoBank p3861 ray3861
theorem signs3861 : ∀ j, Signs p3861 (bank3861 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3862 := params 21
abbrev ray3862 := rays 21
def bank3862 : Fin 2 → Cell := twoBank p3862 ray3862
theorem signs3862 : ∀ j, Signs p3862 (bank3862 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3863 := params 22
abbrev ray3863 := rays 22
def bank3863 : Fin 2 → Cell := twoBank p3863 ray3863
theorem signs3863 : ∀ j, Signs p3863 (bank3863 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3864 := params 23
abbrev ray3864 := rays 23
def bank3864 : Fin 2 → Cell := twoBank p3864 ray3864
theorem signs3864 : ∀ j, Signs p3864 (bank3864 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3865 := params 24
abbrev ray3865 := rays 24
def bank3865 : Fin 2 → Cell := twoBank p3865 ray3865
theorem signs3865 : ∀ j, Signs p3865 (bank3865 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3866 := params 25
abbrev ray3866 := rays 25
def bank3866 : Fin 2 → Cell := twoBank p3866 ray3866
theorem signs3866 : ∀ j, Signs p3866 (bank3866 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3867 := params 26
abbrev ray3867 := rays 26
def bank3867 : Fin 2 → Cell := twoBank p3867 ray3867
theorem signs3867 : ∀ j, Signs p3867 (bank3867 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3868 := params 27
abbrev ray3868 := rays 27
def bank3868 : Fin 2 → Cell := twoBank p3868 ray3868
theorem signs3868 : ∀ j, Signs p3868 (bank3868 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3869 := params 28
abbrev ray3869 := rays 28
def bank3869 : Fin 2 → Cell := twoBank p3869 ray3869
theorem signs3869 : ∀ j, Signs p3869 (bank3869 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3870 := params 29
abbrev ray3870 := rays 29
def bank3870 : Fin 2 → Cell := twoBank p3870 ray3870
theorem signs3870 : ∀ j, Signs p3870 (bank3870 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3871 := params 30
abbrev ray3871 := rays 30
def bank3871 : Fin 2 → Cell := twoBank p3871 ray3871
theorem signs3871 : ∀ j, Signs p3871 (bank3871 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3872 := params 31
abbrev ray3872 := rays 31
def bank3872 : Fin 2 → Cell := twoBank p3872 ray3872
theorem signs3872 : ∀ j, Signs p3872 (bank3872 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03841_03872
