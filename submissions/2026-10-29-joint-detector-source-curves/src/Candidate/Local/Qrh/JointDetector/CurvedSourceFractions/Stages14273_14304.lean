/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14273_14304
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95727009065359,95726563441900,95726117802275,95725672146484,95725226474527,95724780786405,95724335082117,95723889361664,95723443625046,95722997872263,95722552103315,95722106318202,95721660516925,95721214699484,95720768865878,95720323016108,95719877150175,95719431268078,95718985369818,95718539455394,95718093524807,95717647578057,95717201615144,95716755636069,95716309640831,95715863629431,95715417601869,95714971558145,95714525498259,95714079422211,95713633330002,95713187221631,95712741097099]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14272+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14273 := params 0
abbrev ray14273 := rays 0
def bank14273 : Fin 1 → Cell := oneBank p14273 ray14273
theorem signs14273 : ∀ j, Signs p14273 (bank14273 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14274 := params 1
abbrev ray14274 := rays 1
def bank14274 : Fin 1 → Cell := oneBank p14274 ray14274
theorem signs14274 : ∀ j, Signs p14274 (bank14274 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14275 := params 2
abbrev ray14275 := rays 2
def bank14275 : Fin 1 → Cell := oneBank p14275 ray14275
theorem signs14275 : ∀ j, Signs p14275 (bank14275 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14276 := params 3
abbrev ray14276 := rays 3
def bank14276 : Fin 1 → Cell := oneBank p14276 ray14276
theorem signs14276 : ∀ j, Signs p14276 (bank14276 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14277 := params 4
abbrev ray14277 := rays 4
def bank14277 : Fin 1 → Cell := oneBank p14277 ray14277
theorem signs14277 : ∀ j, Signs p14277 (bank14277 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14278 := params 5
abbrev ray14278 := rays 5
def bank14278 : Fin 1 → Cell := oneBank p14278 ray14278
theorem signs14278 : ∀ j, Signs p14278 (bank14278 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14279 := params 6
abbrev ray14279 := rays 6
def bank14279 : Fin 1 → Cell := oneBank p14279 ray14279
theorem signs14279 : ∀ j, Signs p14279 (bank14279 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14280 := params 7
abbrev ray14280 := rays 7
def bank14280 : Fin 1 → Cell := oneBank p14280 ray14280
theorem signs14280 : ∀ j, Signs p14280 (bank14280 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14281 := params 8
abbrev ray14281 := rays 8
def bank14281 : Fin 1 → Cell := oneBank p14281 ray14281
theorem signs14281 : ∀ j, Signs p14281 (bank14281 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14282 := params 9
abbrev ray14282 := rays 9
def bank14282 : Fin 1 → Cell := oneBank p14282 ray14282
theorem signs14282 : ∀ j, Signs p14282 (bank14282 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14283 := params 10
abbrev ray14283 := rays 10
def bank14283 : Fin 1 → Cell := oneBank p14283 ray14283
theorem signs14283 : ∀ j, Signs p14283 (bank14283 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14284 := params 11
abbrev ray14284 := rays 11
def bank14284 : Fin 1 → Cell := oneBank p14284 ray14284
theorem signs14284 : ∀ j, Signs p14284 (bank14284 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14285 := params 12
abbrev ray14285 := rays 12
def bank14285 : Fin 1 → Cell := oneBank p14285 ray14285
theorem signs14285 : ∀ j, Signs p14285 (bank14285 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14286 := params 13
abbrev ray14286 := rays 13
def bank14286 : Fin 1 → Cell := oneBank p14286 ray14286
theorem signs14286 : ∀ j, Signs p14286 (bank14286 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14287 := params 14
abbrev ray14287 := rays 14
def bank14287 : Fin 1 → Cell := oneBank p14287 ray14287
theorem signs14287 : ∀ j, Signs p14287 (bank14287 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14288 := params 15
abbrev ray14288 := rays 15
def bank14288 : Fin 1 → Cell := oneBank p14288 ray14288
theorem signs14288 : ∀ j, Signs p14288 (bank14288 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14289 := params 16
abbrev ray14289 := rays 16
def bank14289 : Fin 1 → Cell := oneBank p14289 ray14289
theorem signs14289 : ∀ j, Signs p14289 (bank14289 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14290 := params 17
abbrev ray14290 := rays 17
def bank14290 : Fin 1 → Cell := oneBank p14290 ray14290
theorem signs14290 : ∀ j, Signs p14290 (bank14290 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14291 := params 18
abbrev ray14291 := rays 18
def bank14291 : Fin 1 → Cell := oneBank p14291 ray14291
theorem signs14291 : ∀ j, Signs p14291 (bank14291 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14292 := params 19
abbrev ray14292 := rays 19
def bank14292 : Fin 1 → Cell := oneBank p14292 ray14292
theorem signs14292 : ∀ j, Signs p14292 (bank14292 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14293 := params 20
abbrev ray14293 := rays 20
def bank14293 : Fin 1 → Cell := oneBank p14293 ray14293
theorem signs14293 : ∀ j, Signs p14293 (bank14293 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14294 := params 21
abbrev ray14294 := rays 21
def bank14294 : Fin 1 → Cell := oneBank p14294 ray14294
theorem signs14294 : ∀ j, Signs p14294 (bank14294 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14295 := params 22
abbrev ray14295 := rays 22
def bank14295 : Fin 1 → Cell := oneBank p14295 ray14295
theorem signs14295 : ∀ j, Signs p14295 (bank14295 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14296 := params 23
abbrev ray14296 := rays 23
def bank14296 : Fin 1 → Cell := oneBank p14296 ray14296
theorem signs14296 : ∀ j, Signs p14296 (bank14296 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14297 := params 24
abbrev ray14297 := rays 24
def bank14297 : Fin 1 → Cell := oneBank p14297 ray14297
theorem signs14297 : ∀ j, Signs p14297 (bank14297 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14298 := params 25
abbrev ray14298 := rays 25
def bank14298 : Fin 1 → Cell := oneBank p14298 ray14298
theorem signs14298 : ∀ j, Signs p14298 (bank14298 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14299 := params 26
abbrev ray14299 := rays 26
def bank14299 : Fin 1 → Cell := oneBank p14299 ray14299
theorem signs14299 : ∀ j, Signs p14299 (bank14299 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14300 := params 27
abbrev ray14300 := rays 27
def bank14300 : Fin 1 → Cell := oneBank p14300 ray14300
theorem signs14300 : ∀ j, Signs p14300 (bank14300 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14301 := params 28
abbrev ray14301 := rays 28
def bank14301 : Fin 1 → Cell := oneBank p14301 ray14301
theorem signs14301 : ∀ j, Signs p14301 (bank14301 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14302 := params 29
abbrev ray14302 := rays 29
def bank14302 : Fin 1 → Cell := oneBank p14302 ray14302
theorem signs14302 : ∀ j, Signs p14302 (bank14302 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14303 := params 30
abbrev ray14303 := rays 30
def bank14303 : Fin 1 → Cell := oneBank p14303 ray14303
theorem signs14303 : ∀ j, Signs p14303 (bank14303 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14304 := params 31
abbrev ray14304 := rays 31
def bank14304 : Fin 1 → Cell := oneBank p14304 ray14304
theorem signs14304 : ∀ j, Signs p14304 (bank14304 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14273_14304
