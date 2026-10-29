/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16929_16960
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94486794435819,94486306224371,94485817996932,94485329753502,94484841494081,94484353218669,94483864927265,94483376619870,94482888296484,94482399957106,94481911601737,94481423230377,94480934843025,94480446439682,94479958020347,94479469585021,94478981133703,94478492666394,94478004183093,94477515683800,94477027168516,94476538637240,94476050089972,94475561526712,94475072947460,94474584352216,94474095740980,94473607113752,94473118470532,94472629811320,94472141136116,94471652444920,94471163737732]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16928+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16929 := params 0
abbrev ray16929 := rays 0
def bank16929 : Fin 1 → Cell := oneBank p16929 ray16929
theorem signs16929 : ∀ j, Signs p16929 (bank16929 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16930 := params 1
abbrev ray16930 := rays 1
def bank16930 : Fin 1 → Cell := oneBank p16930 ray16930
theorem signs16930 : ∀ j, Signs p16930 (bank16930 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16931 := params 2
abbrev ray16931 := rays 2
def bank16931 : Fin 1 → Cell := oneBank p16931 ray16931
theorem signs16931 : ∀ j, Signs p16931 (bank16931 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16932 := params 3
abbrev ray16932 := rays 3
def bank16932 : Fin 1 → Cell := oneBank p16932 ray16932
theorem signs16932 : ∀ j, Signs p16932 (bank16932 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16933 := params 4
abbrev ray16933 := rays 4
def bank16933 : Fin 1 → Cell := oneBank p16933 ray16933
theorem signs16933 : ∀ j, Signs p16933 (bank16933 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16934 := params 5
abbrev ray16934 := rays 5
def bank16934 : Fin 1 → Cell := oneBank p16934 ray16934
theorem signs16934 : ∀ j, Signs p16934 (bank16934 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16935 := params 6
abbrev ray16935 := rays 6
def bank16935 : Fin 1 → Cell := oneBank p16935 ray16935
theorem signs16935 : ∀ j, Signs p16935 (bank16935 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16936 := params 7
abbrev ray16936 := rays 7
def bank16936 : Fin 1 → Cell := oneBank p16936 ray16936
theorem signs16936 : ∀ j, Signs p16936 (bank16936 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16937 := params 8
abbrev ray16937 := rays 8
def bank16937 : Fin 1 → Cell := oneBank p16937 ray16937
theorem signs16937 : ∀ j, Signs p16937 (bank16937 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16938 := params 9
abbrev ray16938 := rays 9
def bank16938 : Fin 1 → Cell := oneBank p16938 ray16938
theorem signs16938 : ∀ j, Signs p16938 (bank16938 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16939 := params 10
abbrev ray16939 := rays 10
def bank16939 : Fin 1 → Cell := oneBank p16939 ray16939
theorem signs16939 : ∀ j, Signs p16939 (bank16939 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16940 := params 11
abbrev ray16940 := rays 11
def bank16940 : Fin 1 → Cell := oneBank p16940 ray16940
theorem signs16940 : ∀ j, Signs p16940 (bank16940 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16941 := params 12
abbrev ray16941 := rays 12
def bank16941 : Fin 1 → Cell := oneBank p16941 ray16941
theorem signs16941 : ∀ j, Signs p16941 (bank16941 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16942 := params 13
abbrev ray16942 := rays 13
def bank16942 : Fin 1 → Cell := oneBank p16942 ray16942
theorem signs16942 : ∀ j, Signs p16942 (bank16942 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16943 := params 14
abbrev ray16943 := rays 14
def bank16943 : Fin 1 → Cell := oneBank p16943 ray16943
theorem signs16943 : ∀ j, Signs p16943 (bank16943 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16944 := params 15
abbrev ray16944 := rays 15
def bank16944 : Fin 1 → Cell := oneBank p16944 ray16944
theorem signs16944 : ∀ j, Signs p16944 (bank16944 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16945 := params 16
abbrev ray16945 := rays 16
def bank16945 : Fin 1 → Cell := oneBank p16945 ray16945
theorem signs16945 : ∀ j, Signs p16945 (bank16945 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16946 := params 17
abbrev ray16946 := rays 17
def bank16946 : Fin 1 → Cell := oneBank p16946 ray16946
theorem signs16946 : ∀ j, Signs p16946 (bank16946 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16947 := params 18
abbrev ray16947 := rays 18
def bank16947 : Fin 1 → Cell := oneBank p16947 ray16947
theorem signs16947 : ∀ j, Signs p16947 (bank16947 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16948 := params 19
abbrev ray16948 := rays 19
def bank16948 : Fin 1 → Cell := oneBank p16948 ray16948
theorem signs16948 : ∀ j, Signs p16948 (bank16948 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16949 := params 20
abbrev ray16949 := rays 20
def bank16949 : Fin 1 → Cell := oneBank p16949 ray16949
theorem signs16949 : ∀ j, Signs p16949 (bank16949 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16950 := params 21
abbrev ray16950 := rays 21
def bank16950 : Fin 1 → Cell := oneBank p16950 ray16950
theorem signs16950 : ∀ j, Signs p16950 (bank16950 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16951 := params 22
abbrev ray16951 := rays 22
def bank16951 : Fin 1 → Cell := oneBank p16951 ray16951
theorem signs16951 : ∀ j, Signs p16951 (bank16951 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16952 := params 23
abbrev ray16952 := rays 23
def bank16952 : Fin 1 → Cell := oneBank p16952 ray16952
theorem signs16952 : ∀ j, Signs p16952 (bank16952 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16953 := params 24
abbrev ray16953 := rays 24
def bank16953 : Fin 1 → Cell := oneBank p16953 ray16953
theorem signs16953 : ∀ j, Signs p16953 (bank16953 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16954 := params 25
abbrev ray16954 := rays 25
def bank16954 : Fin 1 → Cell := oneBank p16954 ray16954
theorem signs16954 : ∀ j, Signs p16954 (bank16954 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16955 := params 26
abbrev ray16955 := rays 26
def bank16955 : Fin 1 → Cell := oneBank p16955 ray16955
theorem signs16955 : ∀ j, Signs p16955 (bank16955 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16956 := params 27
abbrev ray16956 := rays 27
def bank16956 : Fin 1 → Cell := oneBank p16956 ray16956
theorem signs16956 : ∀ j, Signs p16956 (bank16956 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16957 := params 28
abbrev ray16957 := rays 28
def bank16957 : Fin 1 → Cell := oneBank p16957 ray16957
theorem signs16957 : ∀ j, Signs p16957 (bank16957 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16958 := params 29
abbrev ray16958 := rays 29
def bank16958 : Fin 1 → Cell := oneBank p16958 ray16958
theorem signs16958 : ∀ j, Signs p16958 (bank16958 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16959 := params 30
abbrev ray16959 := rays 30
def bank16959 : Fin 1 → Cell := oneBank p16959 ray16959
theorem signs16959 : ∀ j, Signs p16959 (bank16959 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16960 := params 31
abbrev ray16960 := rays 31
def bank16960 : Fin 1 → Cell := oneBank p16960 ray16960
theorem signs16960 : ∀ j, Signs p16960 (bank16960 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16929_16960
