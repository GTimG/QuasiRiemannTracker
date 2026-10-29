/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16129_16160
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94872241680847,94871766257806,94871290818777,94870815363760,94870339892755,94869864405762,94869388902781,94868913383812,94868437848855,94867962297910,94867486730977,94867011148056,94866535549148,94866059934252,94865584303368,94865108656496,94864632993637,94864157314790,94863681619955,94863205909133,94862730182323,94862254439525,94861778680740,94861302905967,94860827115207,94860351308459,94859875485724,94859399647001,94858923792291,94858447921593,94857972034908,94857496132236,94857020213576]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16128+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16129 := params 0
abbrev ray16129 := rays 0
def bank16129 : Fin 1 → Cell := oneBank p16129 ray16129
theorem signs16129 : ∀ j, Signs p16129 (bank16129 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16130 := params 1
abbrev ray16130 := rays 1
def bank16130 : Fin 1 → Cell := oneBank p16130 ray16130
theorem signs16130 : ∀ j, Signs p16130 (bank16130 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16131 := params 2
abbrev ray16131 := rays 2
def bank16131 : Fin 1 → Cell := oneBank p16131 ray16131
theorem signs16131 : ∀ j, Signs p16131 (bank16131 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16132 := params 3
abbrev ray16132 := rays 3
def bank16132 : Fin 1 → Cell := oneBank p16132 ray16132
theorem signs16132 : ∀ j, Signs p16132 (bank16132 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16133 := params 4
abbrev ray16133 := rays 4
def bank16133 : Fin 1 → Cell := oneBank p16133 ray16133
theorem signs16133 : ∀ j, Signs p16133 (bank16133 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16134 := params 5
abbrev ray16134 := rays 5
def bank16134 : Fin 1 → Cell := oneBank p16134 ray16134
theorem signs16134 : ∀ j, Signs p16134 (bank16134 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16135 := params 6
abbrev ray16135 := rays 6
def bank16135 : Fin 1 → Cell := oneBank p16135 ray16135
theorem signs16135 : ∀ j, Signs p16135 (bank16135 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16136 := params 7
abbrev ray16136 := rays 7
def bank16136 : Fin 1 → Cell := oneBank p16136 ray16136
theorem signs16136 : ∀ j, Signs p16136 (bank16136 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16137 := params 8
abbrev ray16137 := rays 8
def bank16137 : Fin 1 → Cell := oneBank p16137 ray16137
theorem signs16137 : ∀ j, Signs p16137 (bank16137 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16138 := params 9
abbrev ray16138 := rays 9
def bank16138 : Fin 1 → Cell := oneBank p16138 ray16138
theorem signs16138 : ∀ j, Signs p16138 (bank16138 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16139 := params 10
abbrev ray16139 := rays 10
def bank16139 : Fin 1 → Cell := oneBank p16139 ray16139
theorem signs16139 : ∀ j, Signs p16139 (bank16139 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16140 := params 11
abbrev ray16140 := rays 11
def bank16140 : Fin 1 → Cell := oneBank p16140 ray16140
theorem signs16140 : ∀ j, Signs p16140 (bank16140 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16141 := params 12
abbrev ray16141 := rays 12
def bank16141 : Fin 1 → Cell := oneBank p16141 ray16141
theorem signs16141 : ∀ j, Signs p16141 (bank16141 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16142 := params 13
abbrev ray16142 := rays 13
def bank16142 : Fin 1 → Cell := oneBank p16142 ray16142
theorem signs16142 : ∀ j, Signs p16142 (bank16142 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16143 := params 14
abbrev ray16143 := rays 14
def bank16143 : Fin 1 → Cell := oneBank p16143 ray16143
theorem signs16143 : ∀ j, Signs p16143 (bank16143 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16144 := params 15
abbrev ray16144 := rays 15
def bank16144 : Fin 1 → Cell := oneBank p16144 ray16144
theorem signs16144 : ∀ j, Signs p16144 (bank16144 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16145 := params 16
abbrev ray16145 := rays 16
def bank16145 : Fin 1 → Cell := oneBank p16145 ray16145
theorem signs16145 : ∀ j, Signs p16145 (bank16145 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16146 := params 17
abbrev ray16146 := rays 17
def bank16146 : Fin 1 → Cell := oneBank p16146 ray16146
theorem signs16146 : ∀ j, Signs p16146 (bank16146 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16147 := params 18
abbrev ray16147 := rays 18
def bank16147 : Fin 1 → Cell := oneBank p16147 ray16147
theorem signs16147 : ∀ j, Signs p16147 (bank16147 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16148 := params 19
abbrev ray16148 := rays 19
def bank16148 : Fin 1 → Cell := oneBank p16148 ray16148
theorem signs16148 : ∀ j, Signs p16148 (bank16148 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16149 := params 20
abbrev ray16149 := rays 20
def bank16149 : Fin 1 → Cell := oneBank p16149 ray16149
theorem signs16149 : ∀ j, Signs p16149 (bank16149 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16150 := params 21
abbrev ray16150 := rays 21
def bank16150 : Fin 1 → Cell := oneBank p16150 ray16150
theorem signs16150 : ∀ j, Signs p16150 (bank16150 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16151 := params 22
abbrev ray16151 := rays 22
def bank16151 : Fin 1 → Cell := oneBank p16151 ray16151
theorem signs16151 : ∀ j, Signs p16151 (bank16151 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16152 := params 23
abbrev ray16152 := rays 23
def bank16152 : Fin 1 → Cell := oneBank p16152 ray16152
theorem signs16152 : ∀ j, Signs p16152 (bank16152 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16153 := params 24
abbrev ray16153 := rays 24
def bank16153 : Fin 1 → Cell := oneBank p16153 ray16153
theorem signs16153 : ∀ j, Signs p16153 (bank16153 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16154 := params 25
abbrev ray16154 := rays 25
def bank16154 : Fin 1 → Cell := oneBank p16154 ray16154
theorem signs16154 : ∀ j, Signs p16154 (bank16154 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16155 := params 26
abbrev ray16155 := rays 26
def bank16155 : Fin 1 → Cell := oneBank p16155 ray16155
theorem signs16155 : ∀ j, Signs p16155 (bank16155 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16156 := params 27
abbrev ray16156 := rays 27
def bank16156 : Fin 1 → Cell := oneBank p16156 ray16156
theorem signs16156 : ∀ j, Signs p16156 (bank16156 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16157 := params 28
abbrev ray16157 := rays 28
def bank16157 : Fin 1 → Cell := oneBank p16157 ray16157
theorem signs16157 : ∀ j, Signs p16157 (bank16157 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16158 := params 29
abbrev ray16158 := rays 29
def bank16158 : Fin 1 → Cell := oneBank p16158 ray16158
theorem signs16158 : ∀ j, Signs p16158 (bank16158 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16159 := params 30
abbrev ray16159 := rays 30
def bank16159 : Fin 1 → Cell := oneBank p16159 ray16159
theorem signs16159 : ∀ j, Signs p16159 (bank16159 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16160 := params 31
abbrev ray16160 := rays 31
def bank16160 : Fin 1 → Cell := oneBank p16160 ray16160
theorem signs16160 : ∀ j, Signs p16160 (bank16160 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16129_16160
