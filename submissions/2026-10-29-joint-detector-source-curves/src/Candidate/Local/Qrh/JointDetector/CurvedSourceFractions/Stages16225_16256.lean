/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16225_16256
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94826528166777,94826051208990,94825574235217,94825097245458,94824620239713,94824143217982,94823666180266,94823189126564,94822712056876,94822234971202,94821757869543,94821280751898,94820803618267,94820326468651,94819849303049,94819372121461,94818894923888,94818417710329,94817940480784,94817463235254,94816985973738,94816508696237,94816031402750,94815554093278,94815076767820,94814599426377,94814122068948,94813644695534,94813167306135,94812689900750,94812212479380,94811735042025,94811257588684]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16224+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16225 := params 0
abbrev ray16225 := rays 0
def bank16225 : Fin 1 → Cell := oneBank p16225 ray16225
theorem signs16225 : ∀ j, Signs p16225 (bank16225 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16226 := params 1
abbrev ray16226 := rays 1
def bank16226 : Fin 1 → Cell := oneBank p16226 ray16226
theorem signs16226 : ∀ j, Signs p16226 (bank16226 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16227 := params 2
abbrev ray16227 := rays 2
def bank16227 : Fin 1 → Cell := oneBank p16227 ray16227
theorem signs16227 : ∀ j, Signs p16227 (bank16227 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16228 := params 3
abbrev ray16228 := rays 3
def bank16228 : Fin 1 → Cell := oneBank p16228 ray16228
theorem signs16228 : ∀ j, Signs p16228 (bank16228 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16229 := params 4
abbrev ray16229 := rays 4
def bank16229 : Fin 1 → Cell := oneBank p16229 ray16229
theorem signs16229 : ∀ j, Signs p16229 (bank16229 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16230 := params 5
abbrev ray16230 := rays 5
def bank16230 : Fin 1 → Cell := oneBank p16230 ray16230
theorem signs16230 : ∀ j, Signs p16230 (bank16230 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16231 := params 6
abbrev ray16231 := rays 6
def bank16231 : Fin 1 → Cell := oneBank p16231 ray16231
theorem signs16231 : ∀ j, Signs p16231 (bank16231 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16232 := params 7
abbrev ray16232 := rays 7
def bank16232 : Fin 1 → Cell := oneBank p16232 ray16232
theorem signs16232 : ∀ j, Signs p16232 (bank16232 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16233 := params 8
abbrev ray16233 := rays 8
def bank16233 : Fin 1 → Cell := oneBank p16233 ray16233
theorem signs16233 : ∀ j, Signs p16233 (bank16233 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16234 := params 9
abbrev ray16234 := rays 9
def bank16234 : Fin 1 → Cell := oneBank p16234 ray16234
theorem signs16234 : ∀ j, Signs p16234 (bank16234 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16235 := params 10
abbrev ray16235 := rays 10
def bank16235 : Fin 1 → Cell := oneBank p16235 ray16235
theorem signs16235 : ∀ j, Signs p16235 (bank16235 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16236 := params 11
abbrev ray16236 := rays 11
def bank16236 : Fin 1 → Cell := oneBank p16236 ray16236
theorem signs16236 : ∀ j, Signs p16236 (bank16236 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16237 := params 12
abbrev ray16237 := rays 12
def bank16237 : Fin 1 → Cell := oneBank p16237 ray16237
theorem signs16237 : ∀ j, Signs p16237 (bank16237 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16238 := params 13
abbrev ray16238 := rays 13
def bank16238 : Fin 1 → Cell := oneBank p16238 ray16238
theorem signs16238 : ∀ j, Signs p16238 (bank16238 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16239 := params 14
abbrev ray16239 := rays 14
def bank16239 : Fin 1 → Cell := oneBank p16239 ray16239
theorem signs16239 : ∀ j, Signs p16239 (bank16239 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16240 := params 15
abbrev ray16240 := rays 15
def bank16240 : Fin 1 → Cell := oneBank p16240 ray16240
theorem signs16240 : ∀ j, Signs p16240 (bank16240 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16241 := params 16
abbrev ray16241 := rays 16
def bank16241 : Fin 1 → Cell := oneBank p16241 ray16241
theorem signs16241 : ∀ j, Signs p16241 (bank16241 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16242 := params 17
abbrev ray16242 := rays 17
def bank16242 : Fin 1 → Cell := oneBank p16242 ray16242
theorem signs16242 : ∀ j, Signs p16242 (bank16242 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16243 := params 18
abbrev ray16243 := rays 18
def bank16243 : Fin 1 → Cell := oneBank p16243 ray16243
theorem signs16243 : ∀ j, Signs p16243 (bank16243 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16244 := params 19
abbrev ray16244 := rays 19
def bank16244 : Fin 1 → Cell := oneBank p16244 ray16244
theorem signs16244 : ∀ j, Signs p16244 (bank16244 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16245 := params 20
abbrev ray16245 := rays 20
def bank16245 : Fin 1 → Cell := oneBank p16245 ray16245
theorem signs16245 : ∀ j, Signs p16245 (bank16245 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16246 := params 21
abbrev ray16246 := rays 21
def bank16246 : Fin 1 → Cell := oneBank p16246 ray16246
theorem signs16246 : ∀ j, Signs p16246 (bank16246 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16247 := params 22
abbrev ray16247 := rays 22
def bank16247 : Fin 1 → Cell := oneBank p16247 ray16247
theorem signs16247 : ∀ j, Signs p16247 (bank16247 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16248 := params 23
abbrev ray16248 := rays 23
def bank16248 : Fin 1 → Cell := oneBank p16248 ray16248
theorem signs16248 : ∀ j, Signs p16248 (bank16248 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16249 := params 24
abbrev ray16249 := rays 24
def bank16249 : Fin 1 → Cell := oneBank p16249 ray16249
theorem signs16249 : ∀ j, Signs p16249 (bank16249 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16250 := params 25
abbrev ray16250 := rays 25
def bank16250 : Fin 1 → Cell := oneBank p16250 ray16250
theorem signs16250 : ∀ j, Signs p16250 (bank16250 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16251 := params 26
abbrev ray16251 := rays 26
def bank16251 : Fin 1 → Cell := oneBank p16251 ray16251
theorem signs16251 : ∀ j, Signs p16251 (bank16251 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16252 := params 27
abbrev ray16252 := rays 27
def bank16252 : Fin 1 → Cell := oneBank p16252 ray16252
theorem signs16252 : ∀ j, Signs p16252 (bank16252 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16253 := params 28
abbrev ray16253 := rays 28
def bank16253 : Fin 1 → Cell := oneBank p16253 ray16253
theorem signs16253 : ∀ j, Signs p16253 (bank16253 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16254 := params 29
abbrev ray16254 := rays 29
def bank16254 : Fin 1 → Cell := oneBank p16254 ray16254
theorem signs16254 : ∀ j, Signs p16254 (bank16254 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16255 := params 30
abbrev ray16255 := rays 30
def bank16255 : Fin 1 → Cell := oneBank p16255 ray16255
theorem signs16255 : ∀ j, Signs p16255 (bank16255 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16256 := params 31
abbrev ray16256 := rays 31
def bank16256 : Fin 1 → Cell := oneBank p16256 ray16256
theorem signs16256 : ∀ j, Signs p16256 (bank16256 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16225_16256
