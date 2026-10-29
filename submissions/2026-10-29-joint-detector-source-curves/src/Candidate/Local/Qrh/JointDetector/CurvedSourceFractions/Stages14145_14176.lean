/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14145_14176
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95783915340912,95783471788102,95783028219104,95782584633918,95782141032545,95781697414985,95781253781238,95780810131304,95780366465183,95779922782875,95779479084381,95779035369701,95778591638834,95778147891782,95777704128544,95777260349120,95776816553511,95776372741717,95775928913738,95775485069574,95775041209225,95774597332692,95774153439974,95773709531072,95773265605986,95772821664716,95772377707263,95771933733626,95771489743806,95771045737803,95770601715617,95770157677248,95769713622696]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14144+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14145 := params 0
abbrev ray14145 := rays 0
def bank14145 : Fin 1 → Cell := oneBank p14145 ray14145
theorem signs14145 : ∀ j, Signs p14145 (bank14145 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14146 := params 1
abbrev ray14146 := rays 1
def bank14146 : Fin 1 → Cell := oneBank p14146 ray14146
theorem signs14146 : ∀ j, Signs p14146 (bank14146 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14147 := params 2
abbrev ray14147 := rays 2
def bank14147 : Fin 1 → Cell := oneBank p14147 ray14147
theorem signs14147 : ∀ j, Signs p14147 (bank14147 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14148 := params 3
abbrev ray14148 := rays 3
def bank14148 : Fin 1 → Cell := oneBank p14148 ray14148
theorem signs14148 : ∀ j, Signs p14148 (bank14148 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14149 := params 4
abbrev ray14149 := rays 4
def bank14149 : Fin 1 → Cell := oneBank p14149 ray14149
theorem signs14149 : ∀ j, Signs p14149 (bank14149 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14150 := params 5
abbrev ray14150 := rays 5
def bank14150 : Fin 1 → Cell := oneBank p14150 ray14150
theorem signs14150 : ∀ j, Signs p14150 (bank14150 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14151 := params 6
abbrev ray14151 := rays 6
def bank14151 : Fin 1 → Cell := oneBank p14151 ray14151
theorem signs14151 : ∀ j, Signs p14151 (bank14151 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14152 := params 7
abbrev ray14152 := rays 7
def bank14152 : Fin 1 → Cell := oneBank p14152 ray14152
theorem signs14152 : ∀ j, Signs p14152 (bank14152 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14153 := params 8
abbrev ray14153 := rays 8
def bank14153 : Fin 1 → Cell := oneBank p14153 ray14153
theorem signs14153 : ∀ j, Signs p14153 (bank14153 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14154 := params 9
abbrev ray14154 := rays 9
def bank14154 : Fin 1 → Cell := oneBank p14154 ray14154
theorem signs14154 : ∀ j, Signs p14154 (bank14154 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14155 := params 10
abbrev ray14155 := rays 10
def bank14155 : Fin 1 → Cell := oneBank p14155 ray14155
theorem signs14155 : ∀ j, Signs p14155 (bank14155 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14156 := params 11
abbrev ray14156 := rays 11
def bank14156 : Fin 1 → Cell := oneBank p14156 ray14156
theorem signs14156 : ∀ j, Signs p14156 (bank14156 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14157 := params 12
abbrev ray14157 := rays 12
def bank14157 : Fin 1 → Cell := oneBank p14157 ray14157
theorem signs14157 : ∀ j, Signs p14157 (bank14157 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14158 := params 13
abbrev ray14158 := rays 13
def bank14158 : Fin 1 → Cell := oneBank p14158 ray14158
theorem signs14158 : ∀ j, Signs p14158 (bank14158 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14159 := params 14
abbrev ray14159 := rays 14
def bank14159 : Fin 1 → Cell := oneBank p14159 ray14159
theorem signs14159 : ∀ j, Signs p14159 (bank14159 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14160 := params 15
abbrev ray14160 := rays 15
def bank14160 : Fin 1 → Cell := oneBank p14160 ray14160
theorem signs14160 : ∀ j, Signs p14160 (bank14160 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14161 := params 16
abbrev ray14161 := rays 16
def bank14161 : Fin 1 → Cell := oneBank p14161 ray14161
theorem signs14161 : ∀ j, Signs p14161 (bank14161 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14162 := params 17
abbrev ray14162 := rays 17
def bank14162 : Fin 1 → Cell := oneBank p14162 ray14162
theorem signs14162 : ∀ j, Signs p14162 (bank14162 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14163 := params 18
abbrev ray14163 := rays 18
def bank14163 : Fin 1 → Cell := oneBank p14163 ray14163
theorem signs14163 : ∀ j, Signs p14163 (bank14163 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14164 := params 19
abbrev ray14164 := rays 19
def bank14164 : Fin 1 → Cell := oneBank p14164 ray14164
theorem signs14164 : ∀ j, Signs p14164 (bank14164 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14165 := params 20
abbrev ray14165 := rays 20
def bank14165 : Fin 1 → Cell := oneBank p14165 ray14165
theorem signs14165 : ∀ j, Signs p14165 (bank14165 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14166 := params 21
abbrev ray14166 := rays 21
def bank14166 : Fin 1 → Cell := oneBank p14166 ray14166
theorem signs14166 : ∀ j, Signs p14166 (bank14166 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14167 := params 22
abbrev ray14167 := rays 22
def bank14167 : Fin 1 → Cell := oneBank p14167 ray14167
theorem signs14167 : ∀ j, Signs p14167 (bank14167 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14168 := params 23
abbrev ray14168 := rays 23
def bank14168 : Fin 1 → Cell := oneBank p14168 ray14168
theorem signs14168 : ∀ j, Signs p14168 (bank14168 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14169 := params 24
abbrev ray14169 := rays 24
def bank14169 : Fin 1 → Cell := oneBank p14169 ray14169
theorem signs14169 : ∀ j, Signs p14169 (bank14169 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14170 := params 25
abbrev ray14170 := rays 25
def bank14170 : Fin 1 → Cell := oneBank p14170 ray14170
theorem signs14170 : ∀ j, Signs p14170 (bank14170 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14171 := params 26
abbrev ray14171 := rays 26
def bank14171 : Fin 1 → Cell := oneBank p14171 ray14171
theorem signs14171 : ∀ j, Signs p14171 (bank14171 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14172 := params 27
abbrev ray14172 := rays 27
def bank14172 : Fin 1 → Cell := oneBank p14172 ray14172
theorem signs14172 : ∀ j, Signs p14172 (bank14172 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14173 := params 28
abbrev ray14173 := rays 28
def bank14173 : Fin 1 → Cell := oneBank p14173 ray14173
theorem signs14173 : ∀ j, Signs p14173 (bank14173 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14174 := params 29
abbrev ray14174 := rays 29
def bank14174 : Fin 1 → Cell := oneBank p14174 ray14174
theorem signs14174 : ∀ j, Signs p14174 (bank14174 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14175 := params 30
abbrev ray14175 := rays 30
def bank14175 : Fin 1 → Cell := oneBank p14175 ray14175
theorem signs14175 : ∀ j, Signs p14175 (bank14175 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14176 := params 31
abbrev ray14176 := rays 31
def bank14176 : Fin 1 → Cell := oneBank p14176 ray14176
theorem signs14176 : ∀ j, Signs p14176 (bank14176 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14145_14176
