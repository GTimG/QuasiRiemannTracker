/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09313_09344
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97717144096387,97716791586806,97716439056491,97716086505443,97715733933663,97715381341151,97715028727908,97714676093934,97714323439230,97713970763797,97713618067635,97713265350745,97712912613128,97712559854784,97712207075713,97711854275917,97711501455396,97711148614150,97710795752180,97710442869487,97710089966071,97709737041933,97709384097073,97709031131492,97708678145191,97708325138170,97707972110430,97707619061972,97707265992796,97706912902902,97706559792292,97706206660965,97705853508923]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9312+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9313 := params 0
abbrev ray9313 := rays 0
def bank9313 : Fin 2 → Cell := twoBank p9313 ray9313
theorem signs9313 : ∀ j, Signs p9313 (bank9313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9314 := params 1
abbrev ray9314 := rays 1
def bank9314 : Fin 2 → Cell := twoBank p9314 ray9314
theorem signs9314 : ∀ j, Signs p9314 (bank9314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9315 := params 2
abbrev ray9315 := rays 2
def bank9315 : Fin 2 → Cell := twoBank p9315 ray9315
theorem signs9315 : ∀ j, Signs p9315 (bank9315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9316 := params 3
abbrev ray9316 := rays 3
def bank9316 : Fin 2 → Cell := twoBank p9316 ray9316
theorem signs9316 : ∀ j, Signs p9316 (bank9316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9317 := params 4
abbrev ray9317 := rays 4
def bank9317 : Fin 2 → Cell := twoBank p9317 ray9317
theorem signs9317 : ∀ j, Signs p9317 (bank9317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9318 := params 5
abbrev ray9318 := rays 5
def bank9318 : Fin 2 → Cell := twoBank p9318 ray9318
theorem signs9318 : ∀ j, Signs p9318 (bank9318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9319 := params 6
abbrev ray9319 := rays 6
def bank9319 : Fin 2 → Cell := twoBank p9319 ray9319
theorem signs9319 : ∀ j, Signs p9319 (bank9319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9320 := params 7
abbrev ray9320 := rays 7
def bank9320 : Fin 2 → Cell := twoBank p9320 ray9320
theorem signs9320 : ∀ j, Signs p9320 (bank9320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9321 := params 8
abbrev ray9321 := rays 8
def bank9321 : Fin 2 → Cell := twoBank p9321 ray9321
theorem signs9321 : ∀ j, Signs p9321 (bank9321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9322 := params 9
abbrev ray9322 := rays 9
def bank9322 : Fin 2 → Cell := twoBank p9322 ray9322
theorem signs9322 : ∀ j, Signs p9322 (bank9322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9323 := params 10
abbrev ray9323 := rays 10
def bank9323 : Fin 2 → Cell := twoBank p9323 ray9323
theorem signs9323 : ∀ j, Signs p9323 (bank9323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9324 := params 11
abbrev ray9324 := rays 11
def bank9324 : Fin 2 → Cell := twoBank p9324 ray9324
theorem signs9324 : ∀ j, Signs p9324 (bank9324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9325 := params 12
abbrev ray9325 := rays 12
def bank9325 : Fin 2 → Cell := twoBank p9325 ray9325
theorem signs9325 : ∀ j, Signs p9325 (bank9325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9326 := params 13
abbrev ray9326 := rays 13
def bank9326 : Fin 2 → Cell := twoBank p9326 ray9326
theorem signs9326 : ∀ j, Signs p9326 (bank9326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9327 := params 14
abbrev ray9327 := rays 14
def bank9327 : Fin 2 → Cell := twoBank p9327 ray9327
theorem signs9327 : ∀ j, Signs p9327 (bank9327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9328 := params 15
abbrev ray9328 := rays 15
def bank9328 : Fin 2 → Cell := twoBank p9328 ray9328
theorem signs9328 : ∀ j, Signs p9328 (bank9328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9329 := params 16
abbrev ray9329 := rays 16
def bank9329 : Fin 2 → Cell := twoBank p9329 ray9329
theorem signs9329 : ∀ j, Signs p9329 (bank9329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9330 := params 17
abbrev ray9330 := rays 17
def bank9330 : Fin 2 → Cell := twoBank p9330 ray9330
theorem signs9330 : ∀ j, Signs p9330 (bank9330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9331 := params 18
abbrev ray9331 := rays 18
def bank9331 : Fin 2 → Cell := twoBank p9331 ray9331
theorem signs9331 : ∀ j, Signs p9331 (bank9331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9332 := params 19
abbrev ray9332 := rays 19
def bank9332 : Fin 2 → Cell := twoBank p9332 ray9332
theorem signs9332 : ∀ j, Signs p9332 (bank9332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9333 := params 20
abbrev ray9333 := rays 20
def bank9333 : Fin 2 → Cell := twoBank p9333 ray9333
theorem signs9333 : ∀ j, Signs p9333 (bank9333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9334 := params 21
abbrev ray9334 := rays 21
def bank9334 : Fin 2 → Cell := twoBank p9334 ray9334
theorem signs9334 : ∀ j, Signs p9334 (bank9334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9335 := params 22
abbrev ray9335 := rays 22
def bank9335 : Fin 2 → Cell := twoBank p9335 ray9335
theorem signs9335 : ∀ j, Signs p9335 (bank9335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9336 := params 23
abbrev ray9336 := rays 23
def bank9336 : Fin 2 → Cell := twoBank p9336 ray9336
theorem signs9336 : ∀ j, Signs p9336 (bank9336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9337 := params 24
abbrev ray9337 := rays 24
def bank9337 : Fin 2 → Cell := twoBank p9337 ray9337
theorem signs9337 : ∀ j, Signs p9337 (bank9337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9338 := params 25
abbrev ray9338 := rays 25
def bank9338 : Fin 2 → Cell := twoBank p9338 ray9338
theorem signs9338 : ∀ j, Signs p9338 (bank9338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9339 := params 26
abbrev ray9339 := rays 26
def bank9339 : Fin 2 → Cell := twoBank p9339 ray9339
theorem signs9339 : ∀ j, Signs p9339 (bank9339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9340 := params 27
abbrev ray9340 := rays 27
def bank9340 : Fin 2 → Cell := twoBank p9340 ray9340
theorem signs9340 : ∀ j, Signs p9340 (bank9340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9341 := params 28
abbrev ray9341 := rays 28
def bank9341 : Fin 2 → Cell := twoBank p9341 ray9341
theorem signs9341 : ∀ j, Signs p9341 (bank9341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9342 := params 29
abbrev ray9342 := rays 29
def bank9342 : Fin 2 → Cell := twoBank p9342 ray9342
theorem signs9342 : ∀ j, Signs p9342 (bank9342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9343 := params 30
abbrev ray9343 := rays 30
def bank9343 : Fin 2 → Cell := twoBank p9343 ray9343
theorem signs9343 : ∀ j, Signs p9343 (bank9343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9344 := params 31
abbrev ray9344 := rays 31
def bank9344 : Fin 2 → Cell := twoBank p9344 ray9344
theorem signs9344 : ∀ j, Signs p9344 (bank9344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09313_09344
