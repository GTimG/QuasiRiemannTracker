/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15137_15168
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95335979355933,95335519818445,95335060264906,95334600695316,95334141109674,95333681507981,95333221890237,95332762256442,95332302606597,95331842940701,95331383258754,95330923560757,95330463846709,95330004116611,95329544370463,95329084608265,95328624830017,95328165035719,95327705225371,95327245398973,95326785556526,95326325698029,95325865823483,95325405932888,95324946026243,95324486103549,95324026164806,95323566210014,95323106239174,95322646252285,95322186249347,95321726230361,95321266195326]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15136+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15137 := params 0
abbrev ray15137 := rays 0
def bank15137 : Fin 1 → Cell := oneBank p15137 ray15137
theorem signs15137 : ∀ j, Signs p15137 (bank15137 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15138 := params 1
abbrev ray15138 := rays 1
def bank15138 : Fin 1 → Cell := oneBank p15138 ray15138
theorem signs15138 : ∀ j, Signs p15138 (bank15138 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15139 := params 2
abbrev ray15139 := rays 2
def bank15139 : Fin 1 → Cell := oneBank p15139 ray15139
theorem signs15139 : ∀ j, Signs p15139 (bank15139 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15140 := params 3
abbrev ray15140 := rays 3
def bank15140 : Fin 1 → Cell := oneBank p15140 ray15140
theorem signs15140 : ∀ j, Signs p15140 (bank15140 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15141 := params 4
abbrev ray15141 := rays 4
def bank15141 : Fin 1 → Cell := oneBank p15141 ray15141
theorem signs15141 : ∀ j, Signs p15141 (bank15141 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15142 := params 5
abbrev ray15142 := rays 5
def bank15142 : Fin 1 → Cell := oneBank p15142 ray15142
theorem signs15142 : ∀ j, Signs p15142 (bank15142 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15143 := params 6
abbrev ray15143 := rays 6
def bank15143 : Fin 1 → Cell := oneBank p15143 ray15143
theorem signs15143 : ∀ j, Signs p15143 (bank15143 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15144 := params 7
abbrev ray15144 := rays 7
def bank15144 : Fin 1 → Cell := oneBank p15144 ray15144
theorem signs15144 : ∀ j, Signs p15144 (bank15144 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15145 := params 8
abbrev ray15145 := rays 8
def bank15145 : Fin 1 → Cell := oneBank p15145 ray15145
theorem signs15145 : ∀ j, Signs p15145 (bank15145 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15146 := params 9
abbrev ray15146 := rays 9
def bank15146 : Fin 1 → Cell := oneBank p15146 ray15146
theorem signs15146 : ∀ j, Signs p15146 (bank15146 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15147 := params 10
abbrev ray15147 := rays 10
def bank15147 : Fin 1 → Cell := oneBank p15147 ray15147
theorem signs15147 : ∀ j, Signs p15147 (bank15147 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15148 := params 11
abbrev ray15148 := rays 11
def bank15148 : Fin 1 → Cell := oneBank p15148 ray15148
theorem signs15148 : ∀ j, Signs p15148 (bank15148 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15149 := params 12
abbrev ray15149 := rays 12
def bank15149 : Fin 1 → Cell := oneBank p15149 ray15149
theorem signs15149 : ∀ j, Signs p15149 (bank15149 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15150 := params 13
abbrev ray15150 := rays 13
def bank15150 : Fin 1 → Cell := oneBank p15150 ray15150
theorem signs15150 : ∀ j, Signs p15150 (bank15150 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15151 := params 14
abbrev ray15151 := rays 14
def bank15151 : Fin 1 → Cell := oneBank p15151 ray15151
theorem signs15151 : ∀ j, Signs p15151 (bank15151 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15152 := params 15
abbrev ray15152 := rays 15
def bank15152 : Fin 1 → Cell := oneBank p15152 ray15152
theorem signs15152 : ∀ j, Signs p15152 (bank15152 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15153 := params 16
abbrev ray15153 := rays 16
def bank15153 : Fin 1 → Cell := oneBank p15153 ray15153
theorem signs15153 : ∀ j, Signs p15153 (bank15153 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15154 := params 17
abbrev ray15154 := rays 17
def bank15154 : Fin 1 → Cell := oneBank p15154 ray15154
theorem signs15154 : ∀ j, Signs p15154 (bank15154 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15155 := params 18
abbrev ray15155 := rays 18
def bank15155 : Fin 1 → Cell := oneBank p15155 ray15155
theorem signs15155 : ∀ j, Signs p15155 (bank15155 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15156 := params 19
abbrev ray15156 := rays 19
def bank15156 : Fin 1 → Cell := oneBank p15156 ray15156
theorem signs15156 : ∀ j, Signs p15156 (bank15156 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15157 := params 20
abbrev ray15157 := rays 20
def bank15157 : Fin 1 → Cell := oneBank p15157 ray15157
theorem signs15157 : ∀ j, Signs p15157 (bank15157 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15158 := params 21
abbrev ray15158 := rays 21
def bank15158 : Fin 1 → Cell := oneBank p15158 ray15158
theorem signs15158 : ∀ j, Signs p15158 (bank15158 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15159 := params 22
abbrev ray15159 := rays 22
def bank15159 : Fin 1 → Cell := oneBank p15159 ray15159
theorem signs15159 : ∀ j, Signs p15159 (bank15159 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15160 := params 23
abbrev ray15160 := rays 23
def bank15160 : Fin 1 → Cell := oneBank p15160 ray15160
theorem signs15160 : ∀ j, Signs p15160 (bank15160 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15161 := params 24
abbrev ray15161 := rays 24
def bank15161 : Fin 1 → Cell := oneBank p15161 ray15161
theorem signs15161 : ∀ j, Signs p15161 (bank15161 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15162 := params 25
abbrev ray15162 := rays 25
def bank15162 : Fin 1 → Cell := oneBank p15162 ray15162
theorem signs15162 : ∀ j, Signs p15162 (bank15162 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15163 := params 26
abbrev ray15163 := rays 26
def bank15163 : Fin 1 → Cell := oneBank p15163 ray15163
theorem signs15163 : ∀ j, Signs p15163 (bank15163 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15164 := params 27
abbrev ray15164 := rays 27
def bank15164 : Fin 1 → Cell := oneBank p15164 ray15164
theorem signs15164 : ∀ j, Signs p15164 (bank15164 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15165 := params 28
abbrev ray15165 := rays 28
def bank15165 : Fin 1 → Cell := oneBank p15165 ray15165
theorem signs15165 : ∀ j, Signs p15165 (bank15165 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15166 := params 29
abbrev ray15166 := rays 29
def bank15166 : Fin 1 → Cell := oneBank p15166 ray15166
theorem signs15166 : ∀ j, Signs p15166 (bank15166 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15167 := params 30
abbrev ray15167 := rays 30
def bank15167 : Fin 1 → Cell := oneBank p15167 ray15167
theorem signs15167 : ∀ j, Signs p15167 (bank15167 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15168 := params 31
abbrev ray15168 := rays 31
def bank15168 : Fin 1 → Cell := oneBank p15168 ray15168
theorem signs15168 : ∀ j, Signs p15168 (bank15168 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15137_15168
