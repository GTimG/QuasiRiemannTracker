/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03873_03904
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99308893948945,99308665349727,99308436725203,99308208075373,99307979400239,99307750699802,99307521974063,99307293223023,99307064446683,99306835645044,99306606818108,99306377965875,99306149088347,99305920185525,99305691257410,99305462304003,99305233325306,99305004321319,99304775292044,99304546237482,99304317157634,99304088052501,99303858922084,99303629766384,99303400585403,99303171379141,99302942147600,99302712890781,99302483608685,99302254301313,99302024968666,99301795610746,99301566227553]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3872+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3873 := params 0
abbrev ray3873 := rays 0
def bank3873 : Fin 2 → Cell := twoBank p3873 ray3873
theorem signs3873 : ∀ j, Signs p3873 (bank3873 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3874 := params 1
abbrev ray3874 := rays 1
def bank3874 : Fin 2 → Cell := twoBank p3874 ray3874
theorem signs3874 : ∀ j, Signs p3874 (bank3874 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3875 := params 2
abbrev ray3875 := rays 2
def bank3875 : Fin 2 → Cell := twoBank p3875 ray3875
theorem signs3875 : ∀ j, Signs p3875 (bank3875 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3876 := params 3
abbrev ray3876 := rays 3
def bank3876 : Fin 2 → Cell := twoBank p3876 ray3876
theorem signs3876 : ∀ j, Signs p3876 (bank3876 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3877 := params 4
abbrev ray3877 := rays 4
def bank3877 : Fin 2 → Cell := twoBank p3877 ray3877
theorem signs3877 : ∀ j, Signs p3877 (bank3877 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3878 := params 5
abbrev ray3878 := rays 5
def bank3878 : Fin 2 → Cell := twoBank p3878 ray3878
theorem signs3878 : ∀ j, Signs p3878 (bank3878 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3879 := params 6
abbrev ray3879 := rays 6
def bank3879 : Fin 2 → Cell := twoBank p3879 ray3879
theorem signs3879 : ∀ j, Signs p3879 (bank3879 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3880 := params 7
abbrev ray3880 := rays 7
def bank3880 : Fin 2 → Cell := twoBank p3880 ray3880
theorem signs3880 : ∀ j, Signs p3880 (bank3880 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3881 := params 8
abbrev ray3881 := rays 8
def bank3881 : Fin 2 → Cell := twoBank p3881 ray3881
theorem signs3881 : ∀ j, Signs p3881 (bank3881 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3882 := params 9
abbrev ray3882 := rays 9
def bank3882 : Fin 2 → Cell := twoBank p3882 ray3882
theorem signs3882 : ∀ j, Signs p3882 (bank3882 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3883 := params 10
abbrev ray3883 := rays 10
def bank3883 : Fin 2 → Cell := twoBank p3883 ray3883
theorem signs3883 : ∀ j, Signs p3883 (bank3883 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3884 := params 11
abbrev ray3884 := rays 11
def bank3884 : Fin 2 → Cell := twoBank p3884 ray3884
theorem signs3884 : ∀ j, Signs p3884 (bank3884 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3885 := params 12
abbrev ray3885 := rays 12
def bank3885 : Fin 2 → Cell := twoBank p3885 ray3885
theorem signs3885 : ∀ j, Signs p3885 (bank3885 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3886 := params 13
abbrev ray3886 := rays 13
def bank3886 : Fin 2 → Cell := twoBank p3886 ray3886
theorem signs3886 : ∀ j, Signs p3886 (bank3886 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3887 := params 14
abbrev ray3887 := rays 14
def bank3887 : Fin 2 → Cell := twoBank p3887 ray3887
theorem signs3887 : ∀ j, Signs p3887 (bank3887 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3888 := params 15
abbrev ray3888 := rays 15
def bank3888 : Fin 2 → Cell := twoBank p3888 ray3888
theorem signs3888 : ∀ j, Signs p3888 (bank3888 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3889 := params 16
abbrev ray3889 := rays 16
def bank3889 : Fin 2 → Cell := twoBank p3889 ray3889
theorem signs3889 : ∀ j, Signs p3889 (bank3889 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3890 := params 17
abbrev ray3890 := rays 17
def bank3890 : Fin 2 → Cell := twoBank p3890 ray3890
theorem signs3890 : ∀ j, Signs p3890 (bank3890 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3891 := params 18
abbrev ray3891 := rays 18
def bank3891 : Fin 2 → Cell := twoBank p3891 ray3891
theorem signs3891 : ∀ j, Signs p3891 (bank3891 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3892 := params 19
abbrev ray3892 := rays 19
def bank3892 : Fin 2 → Cell := twoBank p3892 ray3892
theorem signs3892 : ∀ j, Signs p3892 (bank3892 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3893 := params 20
abbrev ray3893 := rays 20
def bank3893 : Fin 2 → Cell := twoBank p3893 ray3893
theorem signs3893 : ∀ j, Signs p3893 (bank3893 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3894 := params 21
abbrev ray3894 := rays 21
def bank3894 : Fin 2 → Cell := twoBank p3894 ray3894
theorem signs3894 : ∀ j, Signs p3894 (bank3894 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3895 := params 22
abbrev ray3895 := rays 22
def bank3895 : Fin 2 → Cell := twoBank p3895 ray3895
theorem signs3895 : ∀ j, Signs p3895 (bank3895 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3896 := params 23
abbrev ray3896 := rays 23
def bank3896 : Fin 2 → Cell := twoBank p3896 ray3896
theorem signs3896 : ∀ j, Signs p3896 (bank3896 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3897 := params 24
abbrev ray3897 := rays 24
def bank3897 : Fin 2 → Cell := twoBank p3897 ray3897
theorem signs3897 : ∀ j, Signs p3897 (bank3897 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3898 := params 25
abbrev ray3898 := rays 25
def bank3898 : Fin 2 → Cell := twoBank p3898 ray3898
theorem signs3898 : ∀ j, Signs p3898 (bank3898 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3899 := params 26
abbrev ray3899 := rays 26
def bank3899 : Fin 2 → Cell := twoBank p3899 ray3899
theorem signs3899 : ∀ j, Signs p3899 (bank3899 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3900 := params 27
abbrev ray3900 := rays 27
def bank3900 : Fin 2 → Cell := twoBank p3900 ray3900
theorem signs3900 : ∀ j, Signs p3900 (bank3900 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3901 := params 28
abbrev ray3901 := rays 28
def bank3901 : Fin 2 → Cell := twoBank p3901 ray3901
theorem signs3901 : ∀ j, Signs p3901 (bank3901 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3902 := params 29
abbrev ray3902 := rays 29
def bank3902 : Fin 2 → Cell := twoBank p3902 ray3902
theorem signs3902 : ∀ j, Signs p3902 (bank3902 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3903 := params 30
abbrev ray3903 := rays 30
def bank3903 : Fin 2 → Cell := twoBank p3903 ray3903
theorem signs3903 : ∀ j, Signs p3903 (bank3903 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3904 := params 31
abbrev ray3904 := rays 31
def bank3904 : Fin 2 → Cell := twoBank p3904 ray3904
theorem signs3904 : ∀ j, Signs p3904 (bank3904 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03873_03904
