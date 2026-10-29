/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15233_15264
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95291790576875,95291329498902,95290868404887,95290407294830,95289946168731,95289485026590,95289023868407,95288562694183,95288101503917,95287640297610,95287179075261,95286717836871,95286256582440,95285795311968,95285334025455,95284872722901,95284411404306,95283950069671,95283488718995,95283027352279,95282565969522,95282104570725,95281643155888,95281181725011,95280720278094,95280258815137,95279797336140,95279335841103,95278874330026,95278412802910,95277951259754,95277489700559,95277028125325]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15232+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15233 := params 0
abbrev ray15233 := rays 0
def bank15233 : Fin 1 → Cell := oneBank p15233 ray15233
theorem signs15233 : ∀ j, Signs p15233 (bank15233 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15234 := params 1
abbrev ray15234 := rays 1
def bank15234 : Fin 1 → Cell := oneBank p15234 ray15234
theorem signs15234 : ∀ j, Signs p15234 (bank15234 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15235 := params 2
abbrev ray15235 := rays 2
def bank15235 : Fin 1 → Cell := oneBank p15235 ray15235
theorem signs15235 : ∀ j, Signs p15235 (bank15235 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15236 := params 3
abbrev ray15236 := rays 3
def bank15236 : Fin 1 → Cell := oneBank p15236 ray15236
theorem signs15236 : ∀ j, Signs p15236 (bank15236 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15237 := params 4
abbrev ray15237 := rays 4
def bank15237 : Fin 1 → Cell := oneBank p15237 ray15237
theorem signs15237 : ∀ j, Signs p15237 (bank15237 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15238 := params 5
abbrev ray15238 := rays 5
def bank15238 : Fin 1 → Cell := oneBank p15238 ray15238
theorem signs15238 : ∀ j, Signs p15238 (bank15238 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15239 := params 6
abbrev ray15239 := rays 6
def bank15239 : Fin 1 → Cell := oneBank p15239 ray15239
theorem signs15239 : ∀ j, Signs p15239 (bank15239 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15240 := params 7
abbrev ray15240 := rays 7
def bank15240 : Fin 1 → Cell := oneBank p15240 ray15240
theorem signs15240 : ∀ j, Signs p15240 (bank15240 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15241 := params 8
abbrev ray15241 := rays 8
def bank15241 : Fin 1 → Cell := oneBank p15241 ray15241
theorem signs15241 : ∀ j, Signs p15241 (bank15241 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15242 := params 9
abbrev ray15242 := rays 9
def bank15242 : Fin 1 → Cell := oneBank p15242 ray15242
theorem signs15242 : ∀ j, Signs p15242 (bank15242 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15243 := params 10
abbrev ray15243 := rays 10
def bank15243 : Fin 1 → Cell := oneBank p15243 ray15243
theorem signs15243 : ∀ j, Signs p15243 (bank15243 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15244 := params 11
abbrev ray15244 := rays 11
def bank15244 : Fin 1 → Cell := oneBank p15244 ray15244
theorem signs15244 : ∀ j, Signs p15244 (bank15244 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15245 := params 12
abbrev ray15245 := rays 12
def bank15245 : Fin 1 → Cell := oneBank p15245 ray15245
theorem signs15245 : ∀ j, Signs p15245 (bank15245 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15246 := params 13
abbrev ray15246 := rays 13
def bank15246 : Fin 1 → Cell := oneBank p15246 ray15246
theorem signs15246 : ∀ j, Signs p15246 (bank15246 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15247 := params 14
abbrev ray15247 := rays 14
def bank15247 : Fin 1 → Cell := oneBank p15247 ray15247
theorem signs15247 : ∀ j, Signs p15247 (bank15247 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15248 := params 15
abbrev ray15248 := rays 15
def bank15248 : Fin 1 → Cell := oneBank p15248 ray15248
theorem signs15248 : ∀ j, Signs p15248 (bank15248 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15249 := params 16
abbrev ray15249 := rays 16
def bank15249 : Fin 1 → Cell := oneBank p15249 ray15249
theorem signs15249 : ∀ j, Signs p15249 (bank15249 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15250 := params 17
abbrev ray15250 := rays 17
def bank15250 : Fin 1 → Cell := oneBank p15250 ray15250
theorem signs15250 : ∀ j, Signs p15250 (bank15250 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15251 := params 18
abbrev ray15251 := rays 18
def bank15251 : Fin 1 → Cell := oneBank p15251 ray15251
theorem signs15251 : ∀ j, Signs p15251 (bank15251 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15252 := params 19
abbrev ray15252 := rays 19
def bank15252 : Fin 1 → Cell := oneBank p15252 ray15252
theorem signs15252 : ∀ j, Signs p15252 (bank15252 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15253 := params 20
abbrev ray15253 := rays 20
def bank15253 : Fin 1 → Cell := oneBank p15253 ray15253
theorem signs15253 : ∀ j, Signs p15253 (bank15253 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15254 := params 21
abbrev ray15254 := rays 21
def bank15254 : Fin 1 → Cell := oneBank p15254 ray15254
theorem signs15254 : ∀ j, Signs p15254 (bank15254 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15255 := params 22
abbrev ray15255 := rays 22
def bank15255 : Fin 1 → Cell := oneBank p15255 ray15255
theorem signs15255 : ∀ j, Signs p15255 (bank15255 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15256 := params 23
abbrev ray15256 := rays 23
def bank15256 : Fin 1 → Cell := oneBank p15256 ray15256
theorem signs15256 : ∀ j, Signs p15256 (bank15256 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15257 := params 24
abbrev ray15257 := rays 24
def bank15257 : Fin 1 → Cell := oneBank p15257 ray15257
theorem signs15257 : ∀ j, Signs p15257 (bank15257 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15258 := params 25
abbrev ray15258 := rays 25
def bank15258 : Fin 1 → Cell := oneBank p15258 ray15258
theorem signs15258 : ∀ j, Signs p15258 (bank15258 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15259 := params 26
abbrev ray15259 := rays 26
def bank15259 : Fin 1 → Cell := oneBank p15259 ray15259
theorem signs15259 : ∀ j, Signs p15259 (bank15259 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15260 := params 27
abbrev ray15260 := rays 27
def bank15260 : Fin 1 → Cell := oneBank p15260 ray15260
theorem signs15260 : ∀ j, Signs p15260 (bank15260 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15261 := params 28
abbrev ray15261 := rays 28
def bank15261 : Fin 1 → Cell := oneBank p15261 ray15261
theorem signs15261 : ∀ j, Signs p15261 (bank15261 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15262 := params 29
abbrev ray15262 := rays 29
def bank15262 : Fin 1 → Cell := oneBank p15262 ray15262
theorem signs15262 : ∀ j, Signs p15262 (bank15262 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15263 := params 30
abbrev ray15263 := rays 30
def bank15263 : Fin 1 → Cell := oneBank p15263 ray15263
theorem signs15263 : ∀ j, Signs p15263 (bank15263 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15264 := params 31
abbrev ray15264 := rays 31
def bank15264 : Fin 1 → Cell := oneBank p15264 ray15264
theorem signs15264 : ∀ j, Signs p15264 (bank15264 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15233_15264
