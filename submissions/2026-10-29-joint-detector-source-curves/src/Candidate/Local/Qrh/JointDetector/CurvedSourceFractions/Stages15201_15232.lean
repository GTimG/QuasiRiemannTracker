/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15201_15232
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95306536601244,95306076036667,95305615456045,95305154859378,95304694246666,95304233617909,95303772973107,95303312312261,95302851635370,95302390942435,95301930233455,95301469508431,95301008767363,95300548010251,95300087237095,95299626447895,95299165642651,95298704821364,95298243984033,95297783130658,95297322261240,95296861375779,95296400474275,95295939556727,95295478623136,95295017673503,95294556707827,95294095726108,95293634728346,95293173714542,95292712684695,95292251638806,95291790576875]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15200+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15201 := params 0
abbrev ray15201 := rays 0
def bank15201 : Fin 1 → Cell := oneBank p15201 ray15201
theorem signs15201 : ∀ j, Signs p15201 (bank15201 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15202 := params 1
abbrev ray15202 := rays 1
def bank15202 : Fin 1 → Cell := oneBank p15202 ray15202
theorem signs15202 : ∀ j, Signs p15202 (bank15202 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15203 := params 2
abbrev ray15203 := rays 2
def bank15203 : Fin 1 → Cell := oneBank p15203 ray15203
theorem signs15203 : ∀ j, Signs p15203 (bank15203 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15204 := params 3
abbrev ray15204 := rays 3
def bank15204 : Fin 1 → Cell := oneBank p15204 ray15204
theorem signs15204 : ∀ j, Signs p15204 (bank15204 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15205 := params 4
abbrev ray15205 := rays 4
def bank15205 : Fin 1 → Cell := oneBank p15205 ray15205
theorem signs15205 : ∀ j, Signs p15205 (bank15205 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15206 := params 5
abbrev ray15206 := rays 5
def bank15206 : Fin 1 → Cell := oneBank p15206 ray15206
theorem signs15206 : ∀ j, Signs p15206 (bank15206 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15207 := params 6
abbrev ray15207 := rays 6
def bank15207 : Fin 1 → Cell := oneBank p15207 ray15207
theorem signs15207 : ∀ j, Signs p15207 (bank15207 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15208 := params 7
abbrev ray15208 := rays 7
def bank15208 : Fin 1 → Cell := oneBank p15208 ray15208
theorem signs15208 : ∀ j, Signs p15208 (bank15208 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15209 := params 8
abbrev ray15209 := rays 8
def bank15209 : Fin 1 → Cell := oneBank p15209 ray15209
theorem signs15209 : ∀ j, Signs p15209 (bank15209 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15210 := params 9
abbrev ray15210 := rays 9
def bank15210 : Fin 1 → Cell := oneBank p15210 ray15210
theorem signs15210 : ∀ j, Signs p15210 (bank15210 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15211 := params 10
abbrev ray15211 := rays 10
def bank15211 : Fin 1 → Cell := oneBank p15211 ray15211
theorem signs15211 : ∀ j, Signs p15211 (bank15211 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15212 := params 11
abbrev ray15212 := rays 11
def bank15212 : Fin 1 → Cell := oneBank p15212 ray15212
theorem signs15212 : ∀ j, Signs p15212 (bank15212 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15213 := params 12
abbrev ray15213 := rays 12
def bank15213 : Fin 1 → Cell := oneBank p15213 ray15213
theorem signs15213 : ∀ j, Signs p15213 (bank15213 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15214 := params 13
abbrev ray15214 := rays 13
def bank15214 : Fin 1 → Cell := oneBank p15214 ray15214
theorem signs15214 : ∀ j, Signs p15214 (bank15214 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15215 := params 14
abbrev ray15215 := rays 14
def bank15215 : Fin 1 → Cell := oneBank p15215 ray15215
theorem signs15215 : ∀ j, Signs p15215 (bank15215 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15216 := params 15
abbrev ray15216 := rays 15
def bank15216 : Fin 1 → Cell := oneBank p15216 ray15216
theorem signs15216 : ∀ j, Signs p15216 (bank15216 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15217 := params 16
abbrev ray15217 := rays 16
def bank15217 : Fin 1 → Cell := oneBank p15217 ray15217
theorem signs15217 : ∀ j, Signs p15217 (bank15217 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15218 := params 17
abbrev ray15218 := rays 17
def bank15218 : Fin 1 → Cell := oneBank p15218 ray15218
theorem signs15218 : ∀ j, Signs p15218 (bank15218 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15219 := params 18
abbrev ray15219 := rays 18
def bank15219 : Fin 1 → Cell := oneBank p15219 ray15219
theorem signs15219 : ∀ j, Signs p15219 (bank15219 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15220 := params 19
abbrev ray15220 := rays 19
def bank15220 : Fin 1 → Cell := oneBank p15220 ray15220
theorem signs15220 : ∀ j, Signs p15220 (bank15220 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15221 := params 20
abbrev ray15221 := rays 20
def bank15221 : Fin 1 → Cell := oneBank p15221 ray15221
theorem signs15221 : ∀ j, Signs p15221 (bank15221 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15222 := params 21
abbrev ray15222 := rays 21
def bank15222 : Fin 1 → Cell := oneBank p15222 ray15222
theorem signs15222 : ∀ j, Signs p15222 (bank15222 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15223 := params 22
abbrev ray15223 := rays 22
def bank15223 : Fin 1 → Cell := oneBank p15223 ray15223
theorem signs15223 : ∀ j, Signs p15223 (bank15223 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15224 := params 23
abbrev ray15224 := rays 23
def bank15224 : Fin 1 → Cell := oneBank p15224 ray15224
theorem signs15224 : ∀ j, Signs p15224 (bank15224 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15225 := params 24
abbrev ray15225 := rays 24
def bank15225 : Fin 1 → Cell := oneBank p15225 ray15225
theorem signs15225 : ∀ j, Signs p15225 (bank15225 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15226 := params 25
abbrev ray15226 := rays 25
def bank15226 : Fin 1 → Cell := oneBank p15226 ray15226
theorem signs15226 : ∀ j, Signs p15226 (bank15226 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15227 := params 26
abbrev ray15227 := rays 26
def bank15227 : Fin 1 → Cell := oneBank p15227 ray15227
theorem signs15227 : ∀ j, Signs p15227 (bank15227 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15228 := params 27
abbrev ray15228 := rays 27
def bank15228 : Fin 1 → Cell := oneBank p15228 ray15228
theorem signs15228 : ∀ j, Signs p15228 (bank15228 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15229 := params 28
abbrev ray15229 := rays 28
def bank15229 : Fin 1 → Cell := oneBank p15229 ray15229
theorem signs15229 : ∀ j, Signs p15229 (bank15229 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15230 := params 29
abbrev ray15230 := rays 29
def bank15230 : Fin 1 → Cell := oneBank p15230 ray15230
theorem signs15230 : ∀ j, Signs p15230 (bank15230 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15231 := params 30
abbrev ray15231 := rays 30
def bank15231 : Fin 1 → Cell := oneBank p15231 ray15231
theorem signs15231 : ∀ j, Signs p15231 (bank15231 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15232 := params 31
abbrev ray15232 := rays 31
def bank15232 : Fin 1 → Cell := oneBank p15232 ray15232
theorem signs15232 : ∀ j, Signs p15232 (bank15232 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15201_15232
