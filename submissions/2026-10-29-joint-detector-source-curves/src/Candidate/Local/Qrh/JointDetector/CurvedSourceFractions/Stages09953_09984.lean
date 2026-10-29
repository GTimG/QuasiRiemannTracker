/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09953_09984
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97487324001177,97486958341897,97486592662253,97486226962247,97485861241878,97485495501148,97485129740056,97484763958604,97484398156792,97484032334620,97483666492089,97483300629200,97482934745953,97482568842349,97482202918388,97481836974071,97481471009398,97481105024370,97480739018988,97480372993252,97480006947163,97479640880721,97479274793927,97478908686781,97478542559284,97478176411436,97477810243238,97477444054691,97477077845795,97476711616550,97476345366957,97475979097017,97475612806730]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9952+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9953 := params 0
abbrev ray9953 := rays 0
def bank9953 : Fin 2 → Cell := twoBank p9953 ray9953
theorem signs9953 : ∀ j, Signs p9953 (bank9953 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9954 := params 1
abbrev ray9954 := rays 1
def bank9954 : Fin 2 → Cell := twoBank p9954 ray9954
theorem signs9954 : ∀ j, Signs p9954 (bank9954 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9955 := params 2
abbrev ray9955 := rays 2
def bank9955 : Fin 2 → Cell := twoBank p9955 ray9955
theorem signs9955 : ∀ j, Signs p9955 (bank9955 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9956 := params 3
abbrev ray9956 := rays 3
def bank9956 : Fin 2 → Cell := twoBank p9956 ray9956
theorem signs9956 : ∀ j, Signs p9956 (bank9956 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9957 := params 4
abbrev ray9957 := rays 4
def bank9957 : Fin 2 → Cell := twoBank p9957 ray9957
theorem signs9957 : ∀ j, Signs p9957 (bank9957 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9958 := params 5
abbrev ray9958 := rays 5
def bank9958 : Fin 2 → Cell := twoBank p9958 ray9958
theorem signs9958 : ∀ j, Signs p9958 (bank9958 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9959 := params 6
abbrev ray9959 := rays 6
def bank9959 : Fin 2 → Cell := twoBank p9959 ray9959
theorem signs9959 : ∀ j, Signs p9959 (bank9959 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9960 := params 7
abbrev ray9960 := rays 7
def bank9960 : Fin 2 → Cell := twoBank p9960 ray9960
theorem signs9960 : ∀ j, Signs p9960 (bank9960 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9961 := params 8
abbrev ray9961 := rays 8
def bank9961 : Fin 2 → Cell := twoBank p9961 ray9961
theorem signs9961 : ∀ j, Signs p9961 (bank9961 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9962 := params 9
abbrev ray9962 := rays 9
def bank9962 : Fin 2 → Cell := twoBank p9962 ray9962
theorem signs9962 : ∀ j, Signs p9962 (bank9962 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9963 := params 10
abbrev ray9963 := rays 10
def bank9963 : Fin 2 → Cell := twoBank p9963 ray9963
theorem signs9963 : ∀ j, Signs p9963 (bank9963 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9964 := params 11
abbrev ray9964 := rays 11
def bank9964 : Fin 2 → Cell := twoBank p9964 ray9964
theorem signs9964 : ∀ j, Signs p9964 (bank9964 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9965 := params 12
abbrev ray9965 := rays 12
def bank9965 : Fin 2 → Cell := twoBank p9965 ray9965
theorem signs9965 : ∀ j, Signs p9965 (bank9965 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9966 := params 13
abbrev ray9966 := rays 13
def bank9966 : Fin 2 → Cell := twoBank p9966 ray9966
theorem signs9966 : ∀ j, Signs p9966 (bank9966 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9967 := params 14
abbrev ray9967 := rays 14
def bank9967 : Fin 2 → Cell := twoBank p9967 ray9967
theorem signs9967 : ∀ j, Signs p9967 (bank9967 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9968 := params 15
abbrev ray9968 := rays 15
def bank9968 : Fin 2 → Cell := twoBank p9968 ray9968
theorem signs9968 : ∀ j, Signs p9968 (bank9968 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9969 := params 16
abbrev ray9969 := rays 16
def bank9969 : Fin 2 → Cell := twoBank p9969 ray9969
theorem signs9969 : ∀ j, Signs p9969 (bank9969 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9970 := params 17
abbrev ray9970 := rays 17
def bank9970 : Fin 2 → Cell := twoBank p9970 ray9970
theorem signs9970 : ∀ j, Signs p9970 (bank9970 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9971 := params 18
abbrev ray9971 := rays 18
def bank9971 : Fin 2 → Cell := twoBank p9971 ray9971
theorem signs9971 : ∀ j, Signs p9971 (bank9971 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9972 := params 19
abbrev ray9972 := rays 19
def bank9972 : Fin 2 → Cell := twoBank p9972 ray9972
theorem signs9972 : ∀ j, Signs p9972 (bank9972 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9973 := params 20
abbrev ray9973 := rays 20
def bank9973 : Fin 2 → Cell := twoBank p9973 ray9973
theorem signs9973 : ∀ j, Signs p9973 (bank9973 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9974 := params 21
abbrev ray9974 := rays 21
def bank9974 : Fin 2 → Cell := twoBank p9974 ray9974
theorem signs9974 : ∀ j, Signs p9974 (bank9974 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9975 := params 22
abbrev ray9975 := rays 22
def bank9975 : Fin 2 → Cell := twoBank p9975 ray9975
theorem signs9975 : ∀ j, Signs p9975 (bank9975 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9976 := params 23
abbrev ray9976 := rays 23
def bank9976 : Fin 2 → Cell := twoBank p9976 ray9976
theorem signs9976 : ∀ j, Signs p9976 (bank9976 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9977 := params 24
abbrev ray9977 := rays 24
def bank9977 : Fin 2 → Cell := twoBank p9977 ray9977
theorem signs9977 : ∀ j, Signs p9977 (bank9977 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9978 := params 25
abbrev ray9978 := rays 25
def bank9978 : Fin 2 → Cell := twoBank p9978 ray9978
theorem signs9978 : ∀ j, Signs p9978 (bank9978 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9979 := params 26
abbrev ray9979 := rays 26
def bank9979 : Fin 2 → Cell := twoBank p9979 ray9979
theorem signs9979 : ∀ j, Signs p9979 (bank9979 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9980 := params 27
abbrev ray9980 := rays 27
def bank9980 : Fin 2 → Cell := twoBank p9980 ray9980
theorem signs9980 : ∀ j, Signs p9980 (bank9980 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9981 := params 28
abbrev ray9981 := rays 28
def bank9981 : Fin 2 → Cell := twoBank p9981 ray9981
theorem signs9981 : ∀ j, Signs p9981 (bank9981 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9982 := params 29
abbrev ray9982 := rays 29
def bank9982 : Fin 2 → Cell := twoBank p9982 ray9982
theorem signs9982 : ∀ j, Signs p9982 (bank9982 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9983 := params 30
abbrev ray9983 := rays 30
def bank9983 : Fin 2 → Cell := twoBank p9983 ray9983
theorem signs9983 : ∀ j, Signs p9983 (bank9983 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9984 := params 31
abbrev ray9984 := rays 31
def bank9984 : Fin 2 → Cell := twoBank p9984 ray9984
theorem signs9984 : ∀ j, Signs p9984 (bank9984 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09953_09984
