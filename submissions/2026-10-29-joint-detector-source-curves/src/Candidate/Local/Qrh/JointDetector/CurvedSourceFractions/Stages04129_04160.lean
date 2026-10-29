/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04129_04160
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99249549674263,99249314633461,99249079567641,99248844476803,99248609360949,99248374220079,99248139054195,99247903863298,99247668647389,99247433406469,99247198140540,99246962849602,99246727533656,99246492192704,99246256826747,99246021435785,99245786019820,99245550578853,99245315112885,99245079621917,99244844105951,99244608564987,99244372999027,99244137408071,99243901792121,99243666151178,99243430485243,99243194794317,99242959078401,99242723337496,99242487571603,99242251780724,99242015964859]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4128+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4129 := params 0
abbrev ray4129 := rays 0
def bank4129 : Fin 2 → Cell := twoBank p4129 ray4129
theorem signs4129 : ∀ j, Signs p4129 (bank4129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4130 := params 1
abbrev ray4130 := rays 1
def bank4130 : Fin 2 → Cell := twoBank p4130 ray4130
theorem signs4130 : ∀ j, Signs p4130 (bank4130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4131 := params 2
abbrev ray4131 := rays 2
def bank4131 : Fin 2 → Cell := twoBank p4131 ray4131
theorem signs4131 : ∀ j, Signs p4131 (bank4131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4132 := params 3
abbrev ray4132 := rays 3
def bank4132 : Fin 2 → Cell := twoBank p4132 ray4132
theorem signs4132 : ∀ j, Signs p4132 (bank4132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4133 := params 4
abbrev ray4133 := rays 4
def bank4133 : Fin 2 → Cell := twoBank p4133 ray4133
theorem signs4133 : ∀ j, Signs p4133 (bank4133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4134 := params 5
abbrev ray4134 := rays 5
def bank4134 : Fin 2 → Cell := twoBank p4134 ray4134
theorem signs4134 : ∀ j, Signs p4134 (bank4134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4135 := params 6
abbrev ray4135 := rays 6
def bank4135 : Fin 2 → Cell := twoBank p4135 ray4135
theorem signs4135 : ∀ j, Signs p4135 (bank4135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4136 := params 7
abbrev ray4136 := rays 7
def bank4136 : Fin 2 → Cell := twoBank p4136 ray4136
theorem signs4136 : ∀ j, Signs p4136 (bank4136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4137 := params 8
abbrev ray4137 := rays 8
def bank4137 : Fin 2 → Cell := twoBank p4137 ray4137
theorem signs4137 : ∀ j, Signs p4137 (bank4137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4138 := params 9
abbrev ray4138 := rays 9
def bank4138 : Fin 2 → Cell := twoBank p4138 ray4138
theorem signs4138 : ∀ j, Signs p4138 (bank4138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4139 := params 10
abbrev ray4139 := rays 10
def bank4139 : Fin 2 → Cell := twoBank p4139 ray4139
theorem signs4139 : ∀ j, Signs p4139 (bank4139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4140 := params 11
abbrev ray4140 := rays 11
def bank4140 : Fin 2 → Cell := twoBank p4140 ray4140
theorem signs4140 : ∀ j, Signs p4140 (bank4140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4141 := params 12
abbrev ray4141 := rays 12
def bank4141 : Fin 2 → Cell := twoBank p4141 ray4141
theorem signs4141 : ∀ j, Signs p4141 (bank4141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4142 := params 13
abbrev ray4142 := rays 13
def bank4142 : Fin 2 → Cell := twoBank p4142 ray4142
theorem signs4142 : ∀ j, Signs p4142 (bank4142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4143 := params 14
abbrev ray4143 := rays 14
def bank4143 : Fin 2 → Cell := twoBank p4143 ray4143
theorem signs4143 : ∀ j, Signs p4143 (bank4143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4144 := params 15
abbrev ray4144 := rays 15
def bank4144 : Fin 2 → Cell := twoBank p4144 ray4144
theorem signs4144 : ∀ j, Signs p4144 (bank4144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4145 := params 16
abbrev ray4145 := rays 16
def bank4145 : Fin 2 → Cell := twoBank p4145 ray4145
theorem signs4145 : ∀ j, Signs p4145 (bank4145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4146 := params 17
abbrev ray4146 := rays 17
def bank4146 : Fin 2 → Cell := twoBank p4146 ray4146
theorem signs4146 : ∀ j, Signs p4146 (bank4146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4147 := params 18
abbrev ray4147 := rays 18
def bank4147 : Fin 2 → Cell := twoBank p4147 ray4147
theorem signs4147 : ∀ j, Signs p4147 (bank4147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4148 := params 19
abbrev ray4148 := rays 19
def bank4148 : Fin 2 → Cell := twoBank p4148 ray4148
theorem signs4148 : ∀ j, Signs p4148 (bank4148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4149 := params 20
abbrev ray4149 := rays 20
def bank4149 : Fin 2 → Cell := twoBank p4149 ray4149
theorem signs4149 : ∀ j, Signs p4149 (bank4149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4150 := params 21
abbrev ray4150 := rays 21
def bank4150 : Fin 2 → Cell := twoBank p4150 ray4150
theorem signs4150 : ∀ j, Signs p4150 (bank4150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4151 := params 22
abbrev ray4151 := rays 22
def bank4151 : Fin 2 → Cell := twoBank p4151 ray4151
theorem signs4151 : ∀ j, Signs p4151 (bank4151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4152 := params 23
abbrev ray4152 := rays 23
def bank4152 : Fin 2 → Cell := twoBank p4152 ray4152
theorem signs4152 : ∀ j, Signs p4152 (bank4152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4153 := params 24
abbrev ray4153 := rays 24
def bank4153 : Fin 2 → Cell := twoBank p4153 ray4153
theorem signs4153 : ∀ j, Signs p4153 (bank4153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4154 := params 25
abbrev ray4154 := rays 25
def bank4154 : Fin 2 → Cell := twoBank p4154 ray4154
theorem signs4154 : ∀ j, Signs p4154 (bank4154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4155 := params 26
abbrev ray4155 := rays 26
def bank4155 : Fin 2 → Cell := twoBank p4155 ray4155
theorem signs4155 : ∀ j, Signs p4155 (bank4155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4156 := params 27
abbrev ray4156 := rays 27
def bank4156 : Fin 2 → Cell := twoBank p4156 ray4156
theorem signs4156 : ∀ j, Signs p4156 (bank4156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4157 := params 28
abbrev ray4157 := rays 28
def bank4157 : Fin 2 → Cell := twoBank p4157 ray4157
theorem signs4157 : ∀ j, Signs p4157 (bank4157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4158 := params 29
abbrev ray4158 := rays 29
def bank4158 : Fin 2 → Cell := twoBank p4158 ray4158
theorem signs4158 : ∀ j, Signs p4158 (bank4158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4159 := params 30
abbrev ray4159 := rays 30
def bank4159 : Fin 2 → Cell := twoBank p4159 ray4159
theorem signs4159 : ∀ j, Signs p4159 (bank4159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4160 := params 31
abbrev ray4160 := rays 31
def bank4160 : Fin 2 → Cell := twoBank p4160 ray4160
theorem signs4160 : ∀ j, Signs p4160 (bank4160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04129_04160
