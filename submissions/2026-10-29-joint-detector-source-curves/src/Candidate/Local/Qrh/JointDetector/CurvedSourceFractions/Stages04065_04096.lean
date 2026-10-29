/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04065_04096
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99264540196059,99264306758759,99264073296369,99263839808890,99263606296324,99263372758671,99263139195933,99262905608111,99262671995206,99262438357219,99262204694151,99261971006003,99261737292776,99261503554472,99261269791092,99261036002636,99260802189106,99260568350503,99260334486828,99260100598082,99259866684267,99259632745383,99259398781432,99259164792414,99258930778331,99258696739184,99258462674974,99258228585702,99257994471369,99257760331976,99257526167525,99257291978016,99257057763451]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4064+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4065 := params 0
abbrev ray4065 := rays 0
def bank4065 : Fin 2 → Cell := twoBank p4065 ray4065
theorem signs4065 : ∀ j, Signs p4065 (bank4065 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4066 := params 1
abbrev ray4066 := rays 1
def bank4066 : Fin 2 → Cell := twoBank p4066 ray4066
theorem signs4066 : ∀ j, Signs p4066 (bank4066 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4067 := params 2
abbrev ray4067 := rays 2
def bank4067 : Fin 2 → Cell := twoBank p4067 ray4067
theorem signs4067 : ∀ j, Signs p4067 (bank4067 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4068 := params 3
abbrev ray4068 := rays 3
def bank4068 : Fin 2 → Cell := twoBank p4068 ray4068
theorem signs4068 : ∀ j, Signs p4068 (bank4068 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4069 := params 4
abbrev ray4069 := rays 4
def bank4069 : Fin 2 → Cell := twoBank p4069 ray4069
theorem signs4069 : ∀ j, Signs p4069 (bank4069 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4070 := params 5
abbrev ray4070 := rays 5
def bank4070 : Fin 2 → Cell := twoBank p4070 ray4070
theorem signs4070 : ∀ j, Signs p4070 (bank4070 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4071 := params 6
abbrev ray4071 := rays 6
def bank4071 : Fin 2 → Cell := twoBank p4071 ray4071
theorem signs4071 : ∀ j, Signs p4071 (bank4071 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4072 := params 7
abbrev ray4072 := rays 7
def bank4072 : Fin 2 → Cell := twoBank p4072 ray4072
theorem signs4072 : ∀ j, Signs p4072 (bank4072 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4073 := params 8
abbrev ray4073 := rays 8
def bank4073 : Fin 2 → Cell := twoBank p4073 ray4073
theorem signs4073 : ∀ j, Signs p4073 (bank4073 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4074 := params 9
abbrev ray4074 := rays 9
def bank4074 : Fin 2 → Cell := twoBank p4074 ray4074
theorem signs4074 : ∀ j, Signs p4074 (bank4074 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4075 := params 10
abbrev ray4075 := rays 10
def bank4075 : Fin 2 → Cell := twoBank p4075 ray4075
theorem signs4075 : ∀ j, Signs p4075 (bank4075 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4076 := params 11
abbrev ray4076 := rays 11
def bank4076 : Fin 2 → Cell := twoBank p4076 ray4076
theorem signs4076 : ∀ j, Signs p4076 (bank4076 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4077 := params 12
abbrev ray4077 := rays 12
def bank4077 : Fin 2 → Cell := twoBank p4077 ray4077
theorem signs4077 : ∀ j, Signs p4077 (bank4077 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4078 := params 13
abbrev ray4078 := rays 13
def bank4078 : Fin 2 → Cell := twoBank p4078 ray4078
theorem signs4078 : ∀ j, Signs p4078 (bank4078 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4079 := params 14
abbrev ray4079 := rays 14
def bank4079 : Fin 2 → Cell := twoBank p4079 ray4079
theorem signs4079 : ∀ j, Signs p4079 (bank4079 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4080 := params 15
abbrev ray4080 := rays 15
def bank4080 : Fin 2 → Cell := twoBank p4080 ray4080
theorem signs4080 : ∀ j, Signs p4080 (bank4080 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4081 := params 16
abbrev ray4081 := rays 16
def bank4081 : Fin 2 → Cell := twoBank p4081 ray4081
theorem signs4081 : ∀ j, Signs p4081 (bank4081 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4082 := params 17
abbrev ray4082 := rays 17
def bank4082 : Fin 2 → Cell := twoBank p4082 ray4082
theorem signs4082 : ∀ j, Signs p4082 (bank4082 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4083 := params 18
abbrev ray4083 := rays 18
def bank4083 : Fin 2 → Cell := twoBank p4083 ray4083
theorem signs4083 : ∀ j, Signs p4083 (bank4083 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4084 := params 19
abbrev ray4084 := rays 19
def bank4084 : Fin 2 → Cell := twoBank p4084 ray4084
theorem signs4084 : ∀ j, Signs p4084 (bank4084 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4085 := params 20
abbrev ray4085 := rays 20
def bank4085 : Fin 2 → Cell := twoBank p4085 ray4085
theorem signs4085 : ∀ j, Signs p4085 (bank4085 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4086 := params 21
abbrev ray4086 := rays 21
def bank4086 : Fin 2 → Cell := twoBank p4086 ray4086
theorem signs4086 : ∀ j, Signs p4086 (bank4086 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4087 := params 22
abbrev ray4087 := rays 22
def bank4087 : Fin 2 → Cell := twoBank p4087 ray4087
theorem signs4087 : ∀ j, Signs p4087 (bank4087 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4088 := params 23
abbrev ray4088 := rays 23
def bank4088 : Fin 2 → Cell := twoBank p4088 ray4088
theorem signs4088 : ∀ j, Signs p4088 (bank4088 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4089 := params 24
abbrev ray4089 := rays 24
def bank4089 : Fin 2 → Cell := twoBank p4089 ray4089
theorem signs4089 : ∀ j, Signs p4089 (bank4089 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4090 := params 25
abbrev ray4090 := rays 25
def bank4090 : Fin 2 → Cell := twoBank p4090 ray4090
theorem signs4090 : ∀ j, Signs p4090 (bank4090 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4091 := params 26
abbrev ray4091 := rays 26
def bank4091 : Fin 2 → Cell := twoBank p4091 ray4091
theorem signs4091 : ∀ j, Signs p4091 (bank4091 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4092 := params 27
abbrev ray4092 := rays 27
def bank4092 : Fin 2 → Cell := twoBank p4092 ray4092
theorem signs4092 : ∀ j, Signs p4092 (bank4092 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4093 := params 28
abbrev ray4093 := rays 28
def bank4093 : Fin 2 → Cell := twoBank p4093 ray4093
theorem signs4093 : ∀ j, Signs p4093 (bank4093 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4094 := params 29
abbrev ray4094 := rays 29
def bank4094 : Fin 2 → Cell := twoBank p4094 ray4094
theorem signs4094 : ∀ j, Signs p4094 (bank4094 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4095 := params 30
abbrev ray4095 := rays 30
def bank4095 : Fin 2 → Cell := twoBank p4095 ray4095
theorem signs4095 : ∀ j, Signs p4095 (bank4095 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4096 := params 31
abbrev ray4096 := rays 31
def bank4096 : Fin 2 → Cell := twoBank p4096 ray4096
theorem signs4096 : ∀ j, Signs p4096 (bank4096 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04065_04096
