/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04033_04064
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99271996935580,99271764301743,99271531642780,99271298958693,99271066249482,99270833515149,99270600755695,99270367971121,99270135161428,99269902326618,99269669466691,99269436581648,99269203671491,99268970736221,99268737775839,99268504790346,99268271779743,99268038744031,99267805683211,99267572597285,99267339486253,99267106350117,99266873188878,99266640002537,99266406791095,99266173554553,99265940292912,99265707006174,99265473694339,99265240357409,99265006995385,99264773608268,99264540196059]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4032+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4033 := params 0
abbrev ray4033 := rays 0
def bank4033 : Fin 2 → Cell := twoBank p4033 ray4033
theorem signs4033 : ∀ j, Signs p4033 (bank4033 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4034 := params 1
abbrev ray4034 := rays 1
def bank4034 : Fin 2 → Cell := twoBank p4034 ray4034
theorem signs4034 : ∀ j, Signs p4034 (bank4034 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4035 := params 2
abbrev ray4035 := rays 2
def bank4035 : Fin 2 → Cell := twoBank p4035 ray4035
theorem signs4035 : ∀ j, Signs p4035 (bank4035 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4036 := params 3
abbrev ray4036 := rays 3
def bank4036 : Fin 2 → Cell := twoBank p4036 ray4036
theorem signs4036 : ∀ j, Signs p4036 (bank4036 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4037 := params 4
abbrev ray4037 := rays 4
def bank4037 : Fin 2 → Cell := twoBank p4037 ray4037
theorem signs4037 : ∀ j, Signs p4037 (bank4037 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4038 := params 5
abbrev ray4038 := rays 5
def bank4038 : Fin 2 → Cell := twoBank p4038 ray4038
theorem signs4038 : ∀ j, Signs p4038 (bank4038 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4039 := params 6
abbrev ray4039 := rays 6
def bank4039 : Fin 2 → Cell := twoBank p4039 ray4039
theorem signs4039 : ∀ j, Signs p4039 (bank4039 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4040 := params 7
abbrev ray4040 := rays 7
def bank4040 : Fin 2 → Cell := twoBank p4040 ray4040
theorem signs4040 : ∀ j, Signs p4040 (bank4040 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4041 := params 8
abbrev ray4041 := rays 8
def bank4041 : Fin 2 → Cell := twoBank p4041 ray4041
theorem signs4041 : ∀ j, Signs p4041 (bank4041 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4042 := params 9
abbrev ray4042 := rays 9
def bank4042 : Fin 2 → Cell := twoBank p4042 ray4042
theorem signs4042 : ∀ j, Signs p4042 (bank4042 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4043 := params 10
abbrev ray4043 := rays 10
def bank4043 : Fin 2 → Cell := twoBank p4043 ray4043
theorem signs4043 : ∀ j, Signs p4043 (bank4043 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4044 := params 11
abbrev ray4044 := rays 11
def bank4044 : Fin 2 → Cell := twoBank p4044 ray4044
theorem signs4044 : ∀ j, Signs p4044 (bank4044 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4045 := params 12
abbrev ray4045 := rays 12
def bank4045 : Fin 2 → Cell := twoBank p4045 ray4045
theorem signs4045 : ∀ j, Signs p4045 (bank4045 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4046 := params 13
abbrev ray4046 := rays 13
def bank4046 : Fin 2 → Cell := twoBank p4046 ray4046
theorem signs4046 : ∀ j, Signs p4046 (bank4046 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4047 := params 14
abbrev ray4047 := rays 14
def bank4047 : Fin 2 → Cell := twoBank p4047 ray4047
theorem signs4047 : ∀ j, Signs p4047 (bank4047 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4048 := params 15
abbrev ray4048 := rays 15
def bank4048 : Fin 2 → Cell := twoBank p4048 ray4048
theorem signs4048 : ∀ j, Signs p4048 (bank4048 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4049 := params 16
abbrev ray4049 := rays 16
def bank4049 : Fin 2 → Cell := twoBank p4049 ray4049
theorem signs4049 : ∀ j, Signs p4049 (bank4049 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4050 := params 17
abbrev ray4050 := rays 17
def bank4050 : Fin 2 → Cell := twoBank p4050 ray4050
theorem signs4050 : ∀ j, Signs p4050 (bank4050 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4051 := params 18
abbrev ray4051 := rays 18
def bank4051 : Fin 2 → Cell := twoBank p4051 ray4051
theorem signs4051 : ∀ j, Signs p4051 (bank4051 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4052 := params 19
abbrev ray4052 := rays 19
def bank4052 : Fin 2 → Cell := twoBank p4052 ray4052
theorem signs4052 : ∀ j, Signs p4052 (bank4052 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4053 := params 20
abbrev ray4053 := rays 20
def bank4053 : Fin 2 → Cell := twoBank p4053 ray4053
theorem signs4053 : ∀ j, Signs p4053 (bank4053 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4054 := params 21
abbrev ray4054 := rays 21
def bank4054 : Fin 2 → Cell := twoBank p4054 ray4054
theorem signs4054 : ∀ j, Signs p4054 (bank4054 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4055 := params 22
abbrev ray4055 := rays 22
def bank4055 : Fin 2 → Cell := twoBank p4055 ray4055
theorem signs4055 : ∀ j, Signs p4055 (bank4055 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4056 := params 23
abbrev ray4056 := rays 23
def bank4056 : Fin 2 → Cell := twoBank p4056 ray4056
theorem signs4056 : ∀ j, Signs p4056 (bank4056 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4057 := params 24
abbrev ray4057 := rays 24
def bank4057 : Fin 2 → Cell := twoBank p4057 ray4057
theorem signs4057 : ∀ j, Signs p4057 (bank4057 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4058 := params 25
abbrev ray4058 := rays 25
def bank4058 : Fin 2 → Cell := twoBank p4058 ray4058
theorem signs4058 : ∀ j, Signs p4058 (bank4058 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4059 := params 26
abbrev ray4059 := rays 26
def bank4059 : Fin 2 → Cell := twoBank p4059 ray4059
theorem signs4059 : ∀ j, Signs p4059 (bank4059 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4060 := params 27
abbrev ray4060 := rays 27
def bank4060 : Fin 2 → Cell := twoBank p4060 ray4060
theorem signs4060 : ∀ j, Signs p4060 (bank4060 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4061 := params 28
abbrev ray4061 := rays 28
def bank4061 : Fin 2 → Cell := twoBank p4061 ray4061
theorem signs4061 : ∀ j, Signs p4061 (bank4061 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4062 := params 29
abbrev ray4062 := rays 29
def bank4062 : Fin 2 → Cell := twoBank p4062 ray4062
theorem signs4062 : ∀ j, Signs p4062 (bank4062 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4063 := params 30
abbrev ray4063 := rays 30
def bank4063 : Fin 2 → Cell := twoBank p4063 ray4063
theorem signs4063 : ∀ j, Signs p4063 (bank4063 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4064 := params 31
abbrev ray4064 := rays 31
def bank4064 : Fin 2 → Cell := twoBank p4064 ray4064
theorem signs4064 : ∀ j, Signs p4064 (bank4064 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04033_04064
