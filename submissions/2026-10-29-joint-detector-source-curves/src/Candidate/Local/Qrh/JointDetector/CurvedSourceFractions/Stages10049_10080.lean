/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10049_10080
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97452127932564,97451760320928,97451392688981,97451025036725,97450657364160,97450289671286,97449921958104,97449554224614,97449186470818,97448818696715,97448450902306,97448083087592,97447715252573,97447347397250,97446979521623,97446611625693,97446243709461,97445875772927,97445507816091,97445139838954,97444771841517,97444403823780,97444035785744,97443667727409,97443299648776,97442931549845,97442563430617,97442195291093,97441827131273,97441458951157,97441090750747,97440722530042,97440354289044]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10048+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10049 := params 0
abbrev ray10049 := rays 0
def bank10049 : Fin 2 → Cell := twoBank p10049 ray10049
theorem signs10049 : ∀ j, Signs p10049 (bank10049 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10050 := params 1
abbrev ray10050 := rays 1
def bank10050 : Fin 2 → Cell := twoBank p10050 ray10050
theorem signs10050 : ∀ j, Signs p10050 (bank10050 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10051 := params 2
abbrev ray10051 := rays 2
def bank10051 : Fin 2 → Cell := twoBank p10051 ray10051
theorem signs10051 : ∀ j, Signs p10051 (bank10051 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10052 := params 3
abbrev ray10052 := rays 3
def bank10052 : Fin 2 → Cell := twoBank p10052 ray10052
theorem signs10052 : ∀ j, Signs p10052 (bank10052 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10053 := params 4
abbrev ray10053 := rays 4
def bank10053 : Fin 2 → Cell := twoBank p10053 ray10053
theorem signs10053 : ∀ j, Signs p10053 (bank10053 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10054 := params 5
abbrev ray10054 := rays 5
def bank10054 : Fin 2 → Cell := twoBank p10054 ray10054
theorem signs10054 : ∀ j, Signs p10054 (bank10054 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10055 := params 6
abbrev ray10055 := rays 6
def bank10055 : Fin 2 → Cell := twoBank p10055 ray10055
theorem signs10055 : ∀ j, Signs p10055 (bank10055 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10056 := params 7
abbrev ray10056 := rays 7
def bank10056 : Fin 2 → Cell := twoBank p10056 ray10056
theorem signs10056 : ∀ j, Signs p10056 (bank10056 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10057 := params 8
abbrev ray10057 := rays 8
def bank10057 : Fin 2 → Cell := twoBank p10057 ray10057
theorem signs10057 : ∀ j, Signs p10057 (bank10057 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10058 := params 9
abbrev ray10058 := rays 9
def bank10058 : Fin 2 → Cell := twoBank p10058 ray10058
theorem signs10058 : ∀ j, Signs p10058 (bank10058 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10059 := params 10
abbrev ray10059 := rays 10
def bank10059 : Fin 2 → Cell := twoBank p10059 ray10059
theorem signs10059 : ∀ j, Signs p10059 (bank10059 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10060 := params 11
abbrev ray10060 := rays 11
def bank10060 : Fin 2 → Cell := twoBank p10060 ray10060
theorem signs10060 : ∀ j, Signs p10060 (bank10060 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10061 := params 12
abbrev ray10061 := rays 12
def bank10061 : Fin 2 → Cell := twoBank p10061 ray10061
theorem signs10061 : ∀ j, Signs p10061 (bank10061 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10062 := params 13
abbrev ray10062 := rays 13
def bank10062 : Fin 2 → Cell := twoBank p10062 ray10062
theorem signs10062 : ∀ j, Signs p10062 (bank10062 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10063 := params 14
abbrev ray10063 := rays 14
def bank10063 : Fin 2 → Cell := twoBank p10063 ray10063
theorem signs10063 : ∀ j, Signs p10063 (bank10063 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10064 := params 15
abbrev ray10064 := rays 15
def bank10064 : Fin 2 → Cell := twoBank p10064 ray10064
theorem signs10064 : ∀ j, Signs p10064 (bank10064 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10065 := params 16
abbrev ray10065 := rays 16
def bank10065 : Fin 2 → Cell := twoBank p10065 ray10065
theorem signs10065 : ∀ j, Signs p10065 (bank10065 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10066 := params 17
abbrev ray10066 := rays 17
def bank10066 : Fin 2 → Cell := twoBank p10066 ray10066
theorem signs10066 : ∀ j, Signs p10066 (bank10066 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10067 := params 18
abbrev ray10067 := rays 18
def bank10067 : Fin 2 → Cell := twoBank p10067 ray10067
theorem signs10067 : ∀ j, Signs p10067 (bank10067 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10068 := params 19
abbrev ray10068 := rays 19
def bank10068 : Fin 2 → Cell := twoBank p10068 ray10068
theorem signs10068 : ∀ j, Signs p10068 (bank10068 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10069 := params 20
abbrev ray10069 := rays 20
def bank10069 : Fin 2 → Cell := twoBank p10069 ray10069
theorem signs10069 : ∀ j, Signs p10069 (bank10069 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10070 := params 21
abbrev ray10070 := rays 21
def bank10070 : Fin 2 → Cell := twoBank p10070 ray10070
theorem signs10070 : ∀ j, Signs p10070 (bank10070 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10071 := params 22
abbrev ray10071 := rays 22
def bank10071 : Fin 2 → Cell := twoBank p10071 ray10071
theorem signs10071 : ∀ j, Signs p10071 (bank10071 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10072 := params 23
abbrev ray10072 := rays 23
def bank10072 : Fin 2 → Cell := twoBank p10072 ray10072
theorem signs10072 : ∀ j, Signs p10072 (bank10072 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10073 := params 24
abbrev ray10073 := rays 24
def bank10073 : Fin 2 → Cell := twoBank p10073 ray10073
theorem signs10073 : ∀ j, Signs p10073 (bank10073 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10074 := params 25
abbrev ray10074 := rays 25
def bank10074 : Fin 2 → Cell := twoBank p10074 ray10074
theorem signs10074 : ∀ j, Signs p10074 (bank10074 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10075 := params 26
abbrev ray10075 := rays 26
def bank10075 : Fin 2 → Cell := twoBank p10075 ray10075
theorem signs10075 : ∀ j, Signs p10075 (bank10075 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10076 := params 27
abbrev ray10076 := rays 27
def bank10076 : Fin 2 → Cell := twoBank p10076 ray10076
theorem signs10076 : ∀ j, Signs p10076 (bank10076 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10077 := params 28
abbrev ray10077 := rays 28
def bank10077 : Fin 2 → Cell := twoBank p10077 ray10077
theorem signs10077 : ∀ j, Signs p10077 (bank10077 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10078 := params 29
abbrev ray10078 := rays 29
def bank10078 : Fin 2 → Cell := twoBank p10078 ray10078
theorem signs10078 : ∀ j, Signs p10078 (bank10078 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10079 := params 30
abbrev ray10079 := rays 30
def bank10079 : Fin 2 → Cell := twoBank p10079 ray10079
theorem signs10079 : ∀ j, Signs p10079 (bank10079 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10080 := params 31
abbrev ray10080 := rays 31
def bank10080 : Fin 2 → Cell := twoBank p10080 ray10080
theorem signs10080 : ∀ j, Signs p10080 (bank10080 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10049_10080
