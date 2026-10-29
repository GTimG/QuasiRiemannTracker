/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04897_04928
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99061751031756,99061497092918,99061243129874,99060989142624,99060735131169,99060481095511,99060227035650,99059972951588,99059718843325,99059464710863,99059210554202,99058956373344,99058702168289,99058447939039,99058193685595,99057939407957,99057685106127,99057430780105,99057176429893,99056922055491,99056667656901,99056413234124,99056158787160,99055904316011,99055649820677,99055395301160,99055140757461,99054886189580,99054631597519,99054376981278,99054122340859,99053867676263,99053612987490]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4896+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4897 := params 0
abbrev ray4897 := rays 0
def bank4897 : Fin 2 → Cell := twoBank p4897 ray4897
theorem signs4897 : ∀ j, Signs p4897 (bank4897 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4898 := params 1
abbrev ray4898 := rays 1
def bank4898 : Fin 2 → Cell := twoBank p4898 ray4898
theorem signs4898 : ∀ j, Signs p4898 (bank4898 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4899 := params 2
abbrev ray4899 := rays 2
def bank4899 : Fin 2 → Cell := twoBank p4899 ray4899
theorem signs4899 : ∀ j, Signs p4899 (bank4899 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4900 := params 3
abbrev ray4900 := rays 3
def bank4900 : Fin 2 → Cell := twoBank p4900 ray4900
theorem signs4900 : ∀ j, Signs p4900 (bank4900 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4901 := params 4
abbrev ray4901 := rays 4
def bank4901 : Fin 2 → Cell := twoBank p4901 ray4901
theorem signs4901 : ∀ j, Signs p4901 (bank4901 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4902 := params 5
abbrev ray4902 := rays 5
def bank4902 : Fin 2 → Cell := twoBank p4902 ray4902
theorem signs4902 : ∀ j, Signs p4902 (bank4902 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4903 := params 6
abbrev ray4903 := rays 6
def bank4903 : Fin 2 → Cell := twoBank p4903 ray4903
theorem signs4903 : ∀ j, Signs p4903 (bank4903 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4904 := params 7
abbrev ray4904 := rays 7
def bank4904 : Fin 2 → Cell := twoBank p4904 ray4904
theorem signs4904 : ∀ j, Signs p4904 (bank4904 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4905 := params 8
abbrev ray4905 := rays 8
def bank4905 : Fin 2 → Cell := twoBank p4905 ray4905
theorem signs4905 : ∀ j, Signs p4905 (bank4905 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4906 := params 9
abbrev ray4906 := rays 9
def bank4906 : Fin 2 → Cell := twoBank p4906 ray4906
theorem signs4906 : ∀ j, Signs p4906 (bank4906 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4907 := params 10
abbrev ray4907 := rays 10
def bank4907 : Fin 2 → Cell := twoBank p4907 ray4907
theorem signs4907 : ∀ j, Signs p4907 (bank4907 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4908 := params 11
abbrev ray4908 := rays 11
def bank4908 : Fin 2 → Cell := twoBank p4908 ray4908
theorem signs4908 : ∀ j, Signs p4908 (bank4908 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4909 := params 12
abbrev ray4909 := rays 12
def bank4909 : Fin 2 → Cell := twoBank p4909 ray4909
theorem signs4909 : ∀ j, Signs p4909 (bank4909 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4910 := params 13
abbrev ray4910 := rays 13
def bank4910 : Fin 2 → Cell := twoBank p4910 ray4910
theorem signs4910 : ∀ j, Signs p4910 (bank4910 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4911 := params 14
abbrev ray4911 := rays 14
def bank4911 : Fin 2 → Cell := twoBank p4911 ray4911
theorem signs4911 : ∀ j, Signs p4911 (bank4911 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4912 := params 15
abbrev ray4912 := rays 15
def bank4912 : Fin 2 → Cell := twoBank p4912 ray4912
theorem signs4912 : ∀ j, Signs p4912 (bank4912 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4913 := params 16
abbrev ray4913 := rays 16
def bank4913 : Fin 2 → Cell := twoBank p4913 ray4913
theorem signs4913 : ∀ j, Signs p4913 (bank4913 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4914 := params 17
abbrev ray4914 := rays 17
def bank4914 : Fin 2 → Cell := twoBank p4914 ray4914
theorem signs4914 : ∀ j, Signs p4914 (bank4914 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4915 := params 18
abbrev ray4915 := rays 18
def bank4915 : Fin 2 → Cell := twoBank p4915 ray4915
theorem signs4915 : ∀ j, Signs p4915 (bank4915 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4916 := params 19
abbrev ray4916 := rays 19
def bank4916 : Fin 2 → Cell := twoBank p4916 ray4916
theorem signs4916 : ∀ j, Signs p4916 (bank4916 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4917 := params 20
abbrev ray4917 := rays 20
def bank4917 : Fin 2 → Cell := twoBank p4917 ray4917
theorem signs4917 : ∀ j, Signs p4917 (bank4917 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4918 := params 21
abbrev ray4918 := rays 21
def bank4918 : Fin 2 → Cell := twoBank p4918 ray4918
theorem signs4918 : ∀ j, Signs p4918 (bank4918 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4919 := params 22
abbrev ray4919 := rays 22
def bank4919 : Fin 2 → Cell := twoBank p4919 ray4919
theorem signs4919 : ∀ j, Signs p4919 (bank4919 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4920 := params 23
abbrev ray4920 := rays 23
def bank4920 : Fin 2 → Cell := twoBank p4920 ray4920
theorem signs4920 : ∀ j, Signs p4920 (bank4920 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4921 := params 24
abbrev ray4921 := rays 24
def bank4921 : Fin 2 → Cell := twoBank p4921 ray4921
theorem signs4921 : ∀ j, Signs p4921 (bank4921 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4922 := params 25
abbrev ray4922 := rays 25
def bank4922 : Fin 2 → Cell := twoBank p4922 ray4922
theorem signs4922 : ∀ j, Signs p4922 (bank4922 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4923 := params 26
abbrev ray4923 := rays 26
def bank4923 : Fin 2 → Cell := twoBank p4923 ray4923
theorem signs4923 : ∀ j, Signs p4923 (bank4923 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4924 := params 27
abbrev ray4924 := rays 27
def bank4924 : Fin 2 → Cell := twoBank p4924 ray4924
theorem signs4924 : ∀ j, Signs p4924 (bank4924 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4925 := params 28
abbrev ray4925 := rays 28
def bank4925 : Fin 2 → Cell := twoBank p4925 ray4925
theorem signs4925 : ∀ j, Signs p4925 (bank4925 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4926 := params 29
abbrev ray4926 := rays 29
def bank4926 : Fin 2 → Cell := twoBank p4926 ray4926
theorem signs4926 : ∀ j, Signs p4926 (bank4926 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4927 := params 30
abbrev ray4927 := rays 30
def bank4927 : Fin 2 → Cell := twoBank p4927 ray4927
theorem signs4927 : ∀ j, Signs p4927 (bank4927 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4928 := params 31
abbrev ray4928 := rays 31
def bank4928 : Fin 2 → Cell := twoBank p4928 ray4928
theorem signs4928 : ∀ j, Signs p4928 (bank4928 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04897_04928
