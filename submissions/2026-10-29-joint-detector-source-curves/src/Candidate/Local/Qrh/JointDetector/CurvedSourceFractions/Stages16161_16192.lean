/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16161_16192
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94857020213576,94856544278929,94856068328295,94855592361673,94855116379064,94854640380468,94854164365885,94853688335315,94853212288758,94852736226213,94852260147681,94851784053162,94851307942656,94850831816163,94850355673683,94849879515216,94849403340762,94848927150321,94848450943894,94847974721480,94847498483079,94847022228691,94846545958316,94846069671954,94845593369606,94845117051271,94844640716949,94844164366640,94843688000345,94843211618063,94842735219794,94842258805539,94841782375297]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16160+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16161 := params 0
abbrev ray16161 := rays 0
def bank16161 : Fin 1 → Cell := oneBank p16161 ray16161
theorem signs16161 : ∀ j, Signs p16161 (bank16161 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16162 := params 1
abbrev ray16162 := rays 1
def bank16162 : Fin 1 → Cell := oneBank p16162 ray16162
theorem signs16162 : ∀ j, Signs p16162 (bank16162 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16163 := params 2
abbrev ray16163 := rays 2
def bank16163 : Fin 1 → Cell := oneBank p16163 ray16163
theorem signs16163 : ∀ j, Signs p16163 (bank16163 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16164 := params 3
abbrev ray16164 := rays 3
def bank16164 : Fin 1 → Cell := oneBank p16164 ray16164
theorem signs16164 : ∀ j, Signs p16164 (bank16164 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16165 := params 4
abbrev ray16165 := rays 4
def bank16165 : Fin 1 → Cell := oneBank p16165 ray16165
theorem signs16165 : ∀ j, Signs p16165 (bank16165 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16166 := params 5
abbrev ray16166 := rays 5
def bank16166 : Fin 1 → Cell := oneBank p16166 ray16166
theorem signs16166 : ∀ j, Signs p16166 (bank16166 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16167 := params 6
abbrev ray16167 := rays 6
def bank16167 : Fin 1 → Cell := oneBank p16167 ray16167
theorem signs16167 : ∀ j, Signs p16167 (bank16167 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16168 := params 7
abbrev ray16168 := rays 7
def bank16168 : Fin 1 → Cell := oneBank p16168 ray16168
theorem signs16168 : ∀ j, Signs p16168 (bank16168 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16169 := params 8
abbrev ray16169 := rays 8
def bank16169 : Fin 1 → Cell := oneBank p16169 ray16169
theorem signs16169 : ∀ j, Signs p16169 (bank16169 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16170 := params 9
abbrev ray16170 := rays 9
def bank16170 : Fin 1 → Cell := oneBank p16170 ray16170
theorem signs16170 : ∀ j, Signs p16170 (bank16170 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16171 := params 10
abbrev ray16171 := rays 10
def bank16171 : Fin 1 → Cell := oneBank p16171 ray16171
theorem signs16171 : ∀ j, Signs p16171 (bank16171 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16172 := params 11
abbrev ray16172 := rays 11
def bank16172 : Fin 1 → Cell := oneBank p16172 ray16172
theorem signs16172 : ∀ j, Signs p16172 (bank16172 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16173 := params 12
abbrev ray16173 := rays 12
def bank16173 : Fin 1 → Cell := oneBank p16173 ray16173
theorem signs16173 : ∀ j, Signs p16173 (bank16173 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16174 := params 13
abbrev ray16174 := rays 13
def bank16174 : Fin 1 → Cell := oneBank p16174 ray16174
theorem signs16174 : ∀ j, Signs p16174 (bank16174 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16175 := params 14
abbrev ray16175 := rays 14
def bank16175 : Fin 1 → Cell := oneBank p16175 ray16175
theorem signs16175 : ∀ j, Signs p16175 (bank16175 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16176 := params 15
abbrev ray16176 := rays 15
def bank16176 : Fin 1 → Cell := oneBank p16176 ray16176
theorem signs16176 : ∀ j, Signs p16176 (bank16176 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16177 := params 16
abbrev ray16177 := rays 16
def bank16177 : Fin 1 → Cell := oneBank p16177 ray16177
theorem signs16177 : ∀ j, Signs p16177 (bank16177 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16178 := params 17
abbrev ray16178 := rays 17
def bank16178 : Fin 1 → Cell := oneBank p16178 ray16178
theorem signs16178 : ∀ j, Signs p16178 (bank16178 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16179 := params 18
abbrev ray16179 := rays 18
def bank16179 : Fin 1 → Cell := oneBank p16179 ray16179
theorem signs16179 : ∀ j, Signs p16179 (bank16179 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16180 := params 19
abbrev ray16180 := rays 19
def bank16180 : Fin 1 → Cell := oneBank p16180 ray16180
theorem signs16180 : ∀ j, Signs p16180 (bank16180 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16181 := params 20
abbrev ray16181 := rays 20
def bank16181 : Fin 1 → Cell := oneBank p16181 ray16181
theorem signs16181 : ∀ j, Signs p16181 (bank16181 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16182 := params 21
abbrev ray16182 := rays 21
def bank16182 : Fin 1 → Cell := oneBank p16182 ray16182
theorem signs16182 : ∀ j, Signs p16182 (bank16182 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16183 := params 22
abbrev ray16183 := rays 22
def bank16183 : Fin 1 → Cell := oneBank p16183 ray16183
theorem signs16183 : ∀ j, Signs p16183 (bank16183 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16184 := params 23
abbrev ray16184 := rays 23
def bank16184 : Fin 1 → Cell := oneBank p16184 ray16184
theorem signs16184 : ∀ j, Signs p16184 (bank16184 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16185 := params 24
abbrev ray16185 := rays 24
def bank16185 : Fin 1 → Cell := oneBank p16185 ray16185
theorem signs16185 : ∀ j, Signs p16185 (bank16185 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16186 := params 25
abbrev ray16186 := rays 25
def bank16186 : Fin 1 → Cell := oneBank p16186 ray16186
theorem signs16186 : ∀ j, Signs p16186 (bank16186 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16187 := params 26
abbrev ray16187 := rays 26
def bank16187 : Fin 1 → Cell := oneBank p16187 ray16187
theorem signs16187 : ∀ j, Signs p16187 (bank16187 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16188 := params 27
abbrev ray16188 := rays 27
def bank16188 : Fin 1 → Cell := oneBank p16188 ray16188
theorem signs16188 : ∀ j, Signs p16188 (bank16188 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16189 := params 28
abbrev ray16189 := rays 28
def bank16189 : Fin 1 → Cell := oneBank p16189 ray16189
theorem signs16189 : ∀ j, Signs p16189 (bank16189 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16190 := params 29
abbrev ray16190 := rays 29
def bank16190 : Fin 1 → Cell := oneBank p16190 ray16190
theorem signs16190 : ∀ j, Signs p16190 (bank16190 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16191 := params 30
abbrev ray16191 := rays 30
def bank16191 : Fin 1 → Cell := oneBank p16191 ray16191
theorem signs16191 : ∀ j, Signs p16191 (bank16191 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16192 := params 31
abbrev ray16192 := rays 31
def bank16192 : Fin 1 → Cell := oneBank p16192 ray16192
theorem signs16192 : ∀ j, Signs p16192 (bank16192 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16161_16192
