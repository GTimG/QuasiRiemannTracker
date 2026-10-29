/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10945_10976
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97114668321668,97114282724942,97113897108373,97113511471962,97113125815709,97112740139614,97112354443678,97111968727902,97111582992286,97111197236830,97110811461535,97110425666402,97110039851431,97109654016622,97109268161976,97108882287493,97108496393174,97108110479020,97107724545031,97107338591207,97106952617549,97106566624057,97106180610732,97105794577574,97105408524584,97105022451763,97104636359110,97104250246627,97103864114314,97103477962171,97103091790199,97102705598398,97102319386769]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10944+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10945 := params 0
abbrev ray10945 := rays 0
def bank10945 : Fin 2 → Cell := twoBank p10945 ray10945
theorem signs10945 : ∀ j, Signs p10945 (bank10945 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10946 := params 1
abbrev ray10946 := rays 1
def bank10946 : Fin 2 → Cell := twoBank p10946 ray10946
theorem signs10946 : ∀ j, Signs p10946 (bank10946 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10947 := params 2
abbrev ray10947 := rays 2
def bank10947 : Fin 2 → Cell := twoBank p10947 ray10947
theorem signs10947 : ∀ j, Signs p10947 (bank10947 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10948 := params 3
abbrev ray10948 := rays 3
def bank10948 : Fin 2 → Cell := twoBank p10948 ray10948
theorem signs10948 : ∀ j, Signs p10948 (bank10948 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10949 := params 4
abbrev ray10949 := rays 4
def bank10949 : Fin 2 → Cell := twoBank p10949 ray10949
theorem signs10949 : ∀ j, Signs p10949 (bank10949 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10950 := params 5
abbrev ray10950 := rays 5
def bank10950 : Fin 2 → Cell := twoBank p10950 ray10950
theorem signs10950 : ∀ j, Signs p10950 (bank10950 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10951 := params 6
abbrev ray10951 := rays 6
def bank10951 : Fin 2 → Cell := twoBank p10951 ray10951
theorem signs10951 : ∀ j, Signs p10951 (bank10951 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10952 := params 7
abbrev ray10952 := rays 7
def bank10952 : Fin 2 → Cell := twoBank p10952 ray10952
theorem signs10952 : ∀ j, Signs p10952 (bank10952 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10953 := params 8
abbrev ray10953 := rays 8
def bank10953 : Fin 2 → Cell := twoBank p10953 ray10953
theorem signs10953 : ∀ j, Signs p10953 (bank10953 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10954 := params 9
abbrev ray10954 := rays 9
def bank10954 : Fin 2 → Cell := twoBank p10954 ray10954
theorem signs10954 : ∀ j, Signs p10954 (bank10954 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10955 := params 10
abbrev ray10955 := rays 10
def bank10955 : Fin 2 → Cell := twoBank p10955 ray10955
theorem signs10955 : ∀ j, Signs p10955 (bank10955 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10956 := params 11
abbrev ray10956 := rays 11
def bank10956 : Fin 2 → Cell := twoBank p10956 ray10956
theorem signs10956 : ∀ j, Signs p10956 (bank10956 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10957 := params 12
abbrev ray10957 := rays 12
def bank10957 : Fin 2 → Cell := twoBank p10957 ray10957
theorem signs10957 : ∀ j, Signs p10957 (bank10957 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10958 := params 13
abbrev ray10958 := rays 13
def bank10958 : Fin 2 → Cell := twoBank p10958 ray10958
theorem signs10958 : ∀ j, Signs p10958 (bank10958 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10959 := params 14
abbrev ray10959 := rays 14
def bank10959 : Fin 2 → Cell := twoBank p10959 ray10959
theorem signs10959 : ∀ j, Signs p10959 (bank10959 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10960 := params 15
abbrev ray10960 := rays 15
def bank10960 : Fin 2 → Cell := twoBank p10960 ray10960
theorem signs10960 : ∀ j, Signs p10960 (bank10960 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10961 := params 16
abbrev ray10961 := rays 16
def bank10961 : Fin 2 → Cell := twoBank p10961 ray10961
theorem signs10961 : ∀ j, Signs p10961 (bank10961 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10962 := params 17
abbrev ray10962 := rays 17
def bank10962 : Fin 2 → Cell := twoBank p10962 ray10962
theorem signs10962 : ∀ j, Signs p10962 (bank10962 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10963 := params 18
abbrev ray10963 := rays 18
def bank10963 : Fin 2 → Cell := twoBank p10963 ray10963
theorem signs10963 : ∀ j, Signs p10963 (bank10963 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10964 := params 19
abbrev ray10964 := rays 19
def bank10964 : Fin 2 → Cell := twoBank p10964 ray10964
theorem signs10964 : ∀ j, Signs p10964 (bank10964 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10965 := params 20
abbrev ray10965 := rays 20
def bank10965 : Fin 2 → Cell := twoBank p10965 ray10965
theorem signs10965 : ∀ j, Signs p10965 (bank10965 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10966 := params 21
abbrev ray10966 := rays 21
def bank10966 : Fin 2 → Cell := twoBank p10966 ray10966
theorem signs10966 : ∀ j, Signs p10966 (bank10966 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10967 := params 22
abbrev ray10967 := rays 22
def bank10967 : Fin 2 → Cell := twoBank p10967 ray10967
theorem signs10967 : ∀ j, Signs p10967 (bank10967 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10968 := params 23
abbrev ray10968 := rays 23
def bank10968 : Fin 2 → Cell := twoBank p10968 ray10968
theorem signs10968 : ∀ j, Signs p10968 (bank10968 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10969 := params 24
abbrev ray10969 := rays 24
def bank10969 : Fin 2 → Cell := twoBank p10969 ray10969
theorem signs10969 : ∀ j, Signs p10969 (bank10969 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10970 := params 25
abbrev ray10970 := rays 25
def bank10970 : Fin 2 → Cell := twoBank p10970 ray10970
theorem signs10970 : ∀ j, Signs p10970 (bank10970 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10971 := params 26
abbrev ray10971 := rays 26
def bank10971 : Fin 2 → Cell := twoBank p10971 ray10971
theorem signs10971 : ∀ j, Signs p10971 (bank10971 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10972 := params 27
abbrev ray10972 := rays 27
def bank10972 : Fin 2 → Cell := twoBank p10972 ray10972
theorem signs10972 : ∀ j, Signs p10972 (bank10972 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10973 := params 28
abbrev ray10973 := rays 28
def bank10973 : Fin 2 → Cell := twoBank p10973 ray10973
theorem signs10973 : ∀ j, Signs p10973 (bank10973 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10974 := params 29
abbrev ray10974 := rays 29
def bank10974 : Fin 2 → Cell := twoBank p10974 ray10974
theorem signs10974 : ∀ j, Signs p10974 (bank10974 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10975 := params 30
abbrev ray10975 := rays 30
def bank10975 : Fin 2 → Cell := twoBank p10975 ray10975
theorem signs10975 : ∀ j, Signs p10975 (bank10975 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10976 := params 31
abbrev ray10976 := rays 31
def bank10976 : Fin 2 → Cell := twoBank p10976 ray10976
theorem signs10976 : ∀ j, Signs p10976 (bank10976 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10945_10976
