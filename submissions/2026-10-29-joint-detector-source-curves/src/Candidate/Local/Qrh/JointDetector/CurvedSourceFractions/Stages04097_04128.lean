/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04097_04128
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99257057763451,99256823523831,99256589259157,99256354969430,99256120654651,99255886314821,99255651949941,99255417560013,99255183145037,99254948705015,99254714239948,99254479749836,99254245234681,99254010694484,99253776129247,99253541538970,99253306923654,99253072283301,99252837617912,99252602927487,99252368212028,99252133471536,99251898706012,99251663915457,99251429099873,99251194259260,99250959393620,99250724502953,99250489587261,99250254646545,99250019680806,99249784690045,99249549674263]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4096+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4097 := params 0
abbrev ray4097 := rays 0
def bank4097 : Fin 2 → Cell := twoBank p4097 ray4097
theorem signs4097 : ∀ j, Signs p4097 (bank4097 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4098 := params 1
abbrev ray4098 := rays 1
def bank4098 : Fin 2 → Cell := twoBank p4098 ray4098
theorem signs4098 : ∀ j, Signs p4098 (bank4098 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4099 := params 2
abbrev ray4099 := rays 2
def bank4099 : Fin 2 → Cell := twoBank p4099 ray4099
theorem signs4099 : ∀ j, Signs p4099 (bank4099 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4100 := params 3
abbrev ray4100 := rays 3
def bank4100 : Fin 2 → Cell := twoBank p4100 ray4100
theorem signs4100 : ∀ j, Signs p4100 (bank4100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4101 := params 4
abbrev ray4101 := rays 4
def bank4101 : Fin 2 → Cell := twoBank p4101 ray4101
theorem signs4101 : ∀ j, Signs p4101 (bank4101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4102 := params 5
abbrev ray4102 := rays 5
def bank4102 : Fin 2 → Cell := twoBank p4102 ray4102
theorem signs4102 : ∀ j, Signs p4102 (bank4102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4103 := params 6
abbrev ray4103 := rays 6
def bank4103 : Fin 2 → Cell := twoBank p4103 ray4103
theorem signs4103 : ∀ j, Signs p4103 (bank4103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4104 := params 7
abbrev ray4104 := rays 7
def bank4104 : Fin 2 → Cell := twoBank p4104 ray4104
theorem signs4104 : ∀ j, Signs p4104 (bank4104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4105 := params 8
abbrev ray4105 := rays 8
def bank4105 : Fin 2 → Cell := twoBank p4105 ray4105
theorem signs4105 : ∀ j, Signs p4105 (bank4105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4106 := params 9
abbrev ray4106 := rays 9
def bank4106 : Fin 2 → Cell := twoBank p4106 ray4106
theorem signs4106 : ∀ j, Signs p4106 (bank4106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4107 := params 10
abbrev ray4107 := rays 10
def bank4107 : Fin 2 → Cell := twoBank p4107 ray4107
theorem signs4107 : ∀ j, Signs p4107 (bank4107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4108 := params 11
abbrev ray4108 := rays 11
def bank4108 : Fin 2 → Cell := twoBank p4108 ray4108
theorem signs4108 : ∀ j, Signs p4108 (bank4108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4109 := params 12
abbrev ray4109 := rays 12
def bank4109 : Fin 2 → Cell := twoBank p4109 ray4109
theorem signs4109 : ∀ j, Signs p4109 (bank4109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4110 := params 13
abbrev ray4110 := rays 13
def bank4110 : Fin 2 → Cell := twoBank p4110 ray4110
theorem signs4110 : ∀ j, Signs p4110 (bank4110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4111 := params 14
abbrev ray4111 := rays 14
def bank4111 : Fin 2 → Cell := twoBank p4111 ray4111
theorem signs4111 : ∀ j, Signs p4111 (bank4111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4112 := params 15
abbrev ray4112 := rays 15
def bank4112 : Fin 2 → Cell := twoBank p4112 ray4112
theorem signs4112 : ∀ j, Signs p4112 (bank4112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4113 := params 16
abbrev ray4113 := rays 16
def bank4113 : Fin 2 → Cell := twoBank p4113 ray4113
theorem signs4113 : ∀ j, Signs p4113 (bank4113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4114 := params 17
abbrev ray4114 := rays 17
def bank4114 : Fin 2 → Cell := twoBank p4114 ray4114
theorem signs4114 : ∀ j, Signs p4114 (bank4114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4115 := params 18
abbrev ray4115 := rays 18
def bank4115 : Fin 2 → Cell := twoBank p4115 ray4115
theorem signs4115 : ∀ j, Signs p4115 (bank4115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4116 := params 19
abbrev ray4116 := rays 19
def bank4116 : Fin 2 → Cell := twoBank p4116 ray4116
theorem signs4116 : ∀ j, Signs p4116 (bank4116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4117 := params 20
abbrev ray4117 := rays 20
def bank4117 : Fin 2 → Cell := twoBank p4117 ray4117
theorem signs4117 : ∀ j, Signs p4117 (bank4117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4118 := params 21
abbrev ray4118 := rays 21
def bank4118 : Fin 2 → Cell := twoBank p4118 ray4118
theorem signs4118 : ∀ j, Signs p4118 (bank4118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4119 := params 22
abbrev ray4119 := rays 22
def bank4119 : Fin 2 → Cell := twoBank p4119 ray4119
theorem signs4119 : ∀ j, Signs p4119 (bank4119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4120 := params 23
abbrev ray4120 := rays 23
def bank4120 : Fin 2 → Cell := twoBank p4120 ray4120
theorem signs4120 : ∀ j, Signs p4120 (bank4120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4121 := params 24
abbrev ray4121 := rays 24
def bank4121 : Fin 2 → Cell := twoBank p4121 ray4121
theorem signs4121 : ∀ j, Signs p4121 (bank4121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4122 := params 25
abbrev ray4122 := rays 25
def bank4122 : Fin 2 → Cell := twoBank p4122 ray4122
theorem signs4122 : ∀ j, Signs p4122 (bank4122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4123 := params 26
abbrev ray4123 := rays 26
def bank4123 : Fin 2 → Cell := twoBank p4123 ray4123
theorem signs4123 : ∀ j, Signs p4123 (bank4123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4124 := params 27
abbrev ray4124 := rays 27
def bank4124 : Fin 2 → Cell := twoBank p4124 ray4124
theorem signs4124 : ∀ j, Signs p4124 (bank4124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4125 := params 28
abbrev ray4125 := rays 28
def bank4125 : Fin 2 → Cell := twoBank p4125 ray4125
theorem signs4125 : ∀ j, Signs p4125 (bank4125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4126 := params 29
abbrev ray4126 := rays 29
def bank4126 : Fin 2 → Cell := twoBank p4126 ray4126
theorem signs4126 : ∀ j, Signs p4126 (bank4126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4127 := params 30
abbrev ray4127 := rays 30
def bank4127 : Fin 2 → Cell := twoBank p4127 ray4127
theorem signs4127 : ∀ j, Signs p4127 (bank4127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4128 := params 31
abbrev ray4128 := rays 31
def bank4128 : Fin 2 → Cell := twoBank p4128 ray4128
theorem signs4128 : ∀ j, Signs p4128 (bank4128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04097_04128
