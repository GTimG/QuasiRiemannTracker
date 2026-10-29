/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13889_13920
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95896931838716,95896492435936,95896053016921,95895613581672,95895174130188,95894734662470,95894295178517,95893855678331,95893416161911,95892976629257,95892537080370,95892097515250,95891657933897,95891218336311,95890778722492,95890339092441,95889899446158,95889459783643,95889020104896,95888580409917,95888140698707,95887700971265,95887261227592,95886821467688,95886381691554,95885941899189,95885502090594,95885062265769,95884622424714,95884182567429,95883742693915,95883302804171,95882862898198]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13888+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13889 := params 0
abbrev ray13889 := rays 0
def bank13889 : Fin 1 → Cell := oneBank p13889 ray13889
theorem signs13889 : ∀ j, Signs p13889 (bank13889 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13890 := params 1
abbrev ray13890 := rays 1
def bank13890 : Fin 1 → Cell := oneBank p13890 ray13890
theorem signs13890 : ∀ j, Signs p13890 (bank13890 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13891 := params 2
abbrev ray13891 := rays 2
def bank13891 : Fin 1 → Cell := oneBank p13891 ray13891
theorem signs13891 : ∀ j, Signs p13891 (bank13891 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13892 := params 3
abbrev ray13892 := rays 3
def bank13892 : Fin 1 → Cell := oneBank p13892 ray13892
theorem signs13892 : ∀ j, Signs p13892 (bank13892 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13893 := params 4
abbrev ray13893 := rays 4
def bank13893 : Fin 1 → Cell := oneBank p13893 ray13893
theorem signs13893 : ∀ j, Signs p13893 (bank13893 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13894 := params 5
abbrev ray13894 := rays 5
def bank13894 : Fin 1 → Cell := oneBank p13894 ray13894
theorem signs13894 : ∀ j, Signs p13894 (bank13894 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13895 := params 6
abbrev ray13895 := rays 6
def bank13895 : Fin 1 → Cell := oneBank p13895 ray13895
theorem signs13895 : ∀ j, Signs p13895 (bank13895 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13896 := params 7
abbrev ray13896 := rays 7
def bank13896 : Fin 1 → Cell := oneBank p13896 ray13896
theorem signs13896 : ∀ j, Signs p13896 (bank13896 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13897 := params 8
abbrev ray13897 := rays 8
def bank13897 : Fin 1 → Cell := oneBank p13897 ray13897
theorem signs13897 : ∀ j, Signs p13897 (bank13897 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13898 := params 9
abbrev ray13898 := rays 9
def bank13898 : Fin 1 → Cell := oneBank p13898 ray13898
theorem signs13898 : ∀ j, Signs p13898 (bank13898 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13899 := params 10
abbrev ray13899 := rays 10
def bank13899 : Fin 1 → Cell := oneBank p13899 ray13899
theorem signs13899 : ∀ j, Signs p13899 (bank13899 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13900 := params 11
abbrev ray13900 := rays 11
def bank13900 : Fin 1 → Cell := oneBank p13900 ray13900
theorem signs13900 : ∀ j, Signs p13900 (bank13900 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13901 := params 12
abbrev ray13901 := rays 12
def bank13901 : Fin 1 → Cell := oneBank p13901 ray13901
theorem signs13901 : ∀ j, Signs p13901 (bank13901 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13902 := params 13
abbrev ray13902 := rays 13
def bank13902 : Fin 1 → Cell := oneBank p13902 ray13902
theorem signs13902 : ∀ j, Signs p13902 (bank13902 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13903 := params 14
abbrev ray13903 := rays 14
def bank13903 : Fin 1 → Cell := oneBank p13903 ray13903
theorem signs13903 : ∀ j, Signs p13903 (bank13903 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13904 := params 15
abbrev ray13904 := rays 15
def bank13904 : Fin 1 → Cell := oneBank p13904 ray13904
theorem signs13904 : ∀ j, Signs p13904 (bank13904 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13905 := params 16
abbrev ray13905 := rays 16
def bank13905 : Fin 1 → Cell := oneBank p13905 ray13905
theorem signs13905 : ∀ j, Signs p13905 (bank13905 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13906 := params 17
abbrev ray13906 := rays 17
def bank13906 : Fin 1 → Cell := oneBank p13906 ray13906
theorem signs13906 : ∀ j, Signs p13906 (bank13906 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13907 := params 18
abbrev ray13907 := rays 18
def bank13907 : Fin 1 → Cell := oneBank p13907 ray13907
theorem signs13907 : ∀ j, Signs p13907 (bank13907 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13908 := params 19
abbrev ray13908 := rays 19
def bank13908 : Fin 1 → Cell := oneBank p13908 ray13908
theorem signs13908 : ∀ j, Signs p13908 (bank13908 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13909 := params 20
abbrev ray13909 := rays 20
def bank13909 : Fin 1 → Cell := oneBank p13909 ray13909
theorem signs13909 : ∀ j, Signs p13909 (bank13909 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13910 := params 21
abbrev ray13910 := rays 21
def bank13910 : Fin 1 → Cell := oneBank p13910 ray13910
theorem signs13910 : ∀ j, Signs p13910 (bank13910 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13911 := params 22
abbrev ray13911 := rays 22
def bank13911 : Fin 1 → Cell := oneBank p13911 ray13911
theorem signs13911 : ∀ j, Signs p13911 (bank13911 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13912 := params 23
abbrev ray13912 := rays 23
def bank13912 : Fin 1 → Cell := oneBank p13912 ray13912
theorem signs13912 : ∀ j, Signs p13912 (bank13912 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13913 := params 24
abbrev ray13913 := rays 24
def bank13913 : Fin 1 → Cell := oneBank p13913 ray13913
theorem signs13913 : ∀ j, Signs p13913 (bank13913 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13914 := params 25
abbrev ray13914 := rays 25
def bank13914 : Fin 1 → Cell := oneBank p13914 ray13914
theorem signs13914 : ∀ j, Signs p13914 (bank13914 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13915 := params 26
abbrev ray13915 := rays 26
def bank13915 : Fin 1 → Cell := oneBank p13915 ray13915
theorem signs13915 : ∀ j, Signs p13915 (bank13915 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13916 := params 27
abbrev ray13916 := rays 27
def bank13916 : Fin 1 → Cell := oneBank p13916 ray13916
theorem signs13916 : ∀ j, Signs p13916 (bank13916 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13917 := params 28
abbrev ray13917 := rays 28
def bank13917 : Fin 1 → Cell := oneBank p13917 ray13917
theorem signs13917 : ∀ j, Signs p13917 (bank13917 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13918 := params 29
abbrev ray13918 := rays 29
def bank13918 : Fin 1 → Cell := oneBank p13918 ray13918
theorem signs13918 : ∀ j, Signs p13918 (bank13918 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13919 := params 30
abbrev ray13919 := rays 30
def bank13919 : Fin 1 → Cell := oneBank p13919 ray13919
theorem signs13919 : ∀ j, Signs p13919 (bank13919 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13920 := params 31
abbrev ray13920 := rays 31
def bank13920 : Fin 1 → Cell := oneBank p13920 ray13920
theorem signs13920 : ∀ j, Signs p13920 (bank13920 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13889_13920
