/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05313_05344
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98954034836765,98953770913670,98953506966778,98953242996090,98952979001607,98952714983329,98952450941258,98952186875395,98951922785741,98951658672296,98951394535062,98951130374039,98950866189229,98950601980632,98950337748250,98950073492083,98949809212132,98949544908399,98949280580884,98949016229588,98948751854512,98948487455657,98948223033025,98947958586616,98947694116431,98947429622471,98947165104736,98946900563228,98946635997948,98946371408897,98946106796076,98945842159485,98945577499126]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5312+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5313 := params 0
abbrev ray5313 := rays 0
def bank5313 : Fin 2 → Cell := twoBank p5313 ray5313
theorem signs5313 : ∀ j, Signs p5313 (bank5313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5314 := params 1
abbrev ray5314 := rays 1
def bank5314 : Fin 2 → Cell := twoBank p5314 ray5314
theorem signs5314 : ∀ j, Signs p5314 (bank5314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5315 := params 2
abbrev ray5315 := rays 2
def bank5315 : Fin 2 → Cell := twoBank p5315 ray5315
theorem signs5315 : ∀ j, Signs p5315 (bank5315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5316 := params 3
abbrev ray5316 := rays 3
def bank5316 : Fin 2 → Cell := twoBank p5316 ray5316
theorem signs5316 : ∀ j, Signs p5316 (bank5316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5317 := params 4
abbrev ray5317 := rays 4
def bank5317 : Fin 2 → Cell := twoBank p5317 ray5317
theorem signs5317 : ∀ j, Signs p5317 (bank5317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5318 := params 5
abbrev ray5318 := rays 5
def bank5318 : Fin 2 → Cell := twoBank p5318 ray5318
theorem signs5318 : ∀ j, Signs p5318 (bank5318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5319 := params 6
abbrev ray5319 := rays 6
def bank5319 : Fin 2 → Cell := twoBank p5319 ray5319
theorem signs5319 : ∀ j, Signs p5319 (bank5319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5320 := params 7
abbrev ray5320 := rays 7
def bank5320 : Fin 2 → Cell := twoBank p5320 ray5320
theorem signs5320 : ∀ j, Signs p5320 (bank5320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5321 := params 8
abbrev ray5321 := rays 8
def bank5321 : Fin 2 → Cell := twoBank p5321 ray5321
theorem signs5321 : ∀ j, Signs p5321 (bank5321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5322 := params 9
abbrev ray5322 := rays 9
def bank5322 : Fin 2 → Cell := twoBank p5322 ray5322
theorem signs5322 : ∀ j, Signs p5322 (bank5322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5323 := params 10
abbrev ray5323 := rays 10
def bank5323 : Fin 2 → Cell := twoBank p5323 ray5323
theorem signs5323 : ∀ j, Signs p5323 (bank5323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5324 := params 11
abbrev ray5324 := rays 11
def bank5324 : Fin 2 → Cell := twoBank p5324 ray5324
theorem signs5324 : ∀ j, Signs p5324 (bank5324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5325 := params 12
abbrev ray5325 := rays 12
def bank5325 : Fin 2 → Cell := twoBank p5325 ray5325
theorem signs5325 : ∀ j, Signs p5325 (bank5325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5326 := params 13
abbrev ray5326 := rays 13
def bank5326 : Fin 2 → Cell := twoBank p5326 ray5326
theorem signs5326 : ∀ j, Signs p5326 (bank5326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5327 := params 14
abbrev ray5327 := rays 14
def bank5327 : Fin 2 → Cell := twoBank p5327 ray5327
theorem signs5327 : ∀ j, Signs p5327 (bank5327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5328 := params 15
abbrev ray5328 := rays 15
def bank5328 : Fin 2 → Cell := twoBank p5328 ray5328
theorem signs5328 : ∀ j, Signs p5328 (bank5328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5329 := params 16
abbrev ray5329 := rays 16
def bank5329 : Fin 2 → Cell := twoBank p5329 ray5329
theorem signs5329 : ∀ j, Signs p5329 (bank5329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5330 := params 17
abbrev ray5330 := rays 17
def bank5330 : Fin 2 → Cell := twoBank p5330 ray5330
theorem signs5330 : ∀ j, Signs p5330 (bank5330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5331 := params 18
abbrev ray5331 := rays 18
def bank5331 : Fin 2 → Cell := twoBank p5331 ray5331
theorem signs5331 : ∀ j, Signs p5331 (bank5331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5332 := params 19
abbrev ray5332 := rays 19
def bank5332 : Fin 2 → Cell := twoBank p5332 ray5332
theorem signs5332 : ∀ j, Signs p5332 (bank5332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5333 := params 20
abbrev ray5333 := rays 20
def bank5333 : Fin 2 → Cell := twoBank p5333 ray5333
theorem signs5333 : ∀ j, Signs p5333 (bank5333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5334 := params 21
abbrev ray5334 := rays 21
def bank5334 : Fin 2 → Cell := twoBank p5334 ray5334
theorem signs5334 : ∀ j, Signs p5334 (bank5334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5335 := params 22
abbrev ray5335 := rays 22
def bank5335 : Fin 2 → Cell := twoBank p5335 ray5335
theorem signs5335 : ∀ j, Signs p5335 (bank5335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5336 := params 23
abbrev ray5336 := rays 23
def bank5336 : Fin 2 → Cell := twoBank p5336 ray5336
theorem signs5336 : ∀ j, Signs p5336 (bank5336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5337 := params 24
abbrev ray5337 := rays 24
def bank5337 : Fin 2 → Cell := twoBank p5337 ray5337
theorem signs5337 : ∀ j, Signs p5337 (bank5337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5338 := params 25
abbrev ray5338 := rays 25
def bank5338 : Fin 2 → Cell := twoBank p5338 ray5338
theorem signs5338 : ∀ j, Signs p5338 (bank5338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5339 := params 26
abbrev ray5339 := rays 26
def bank5339 : Fin 2 → Cell := twoBank p5339 ray5339
theorem signs5339 : ∀ j, Signs p5339 (bank5339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5340 := params 27
abbrev ray5340 := rays 27
def bank5340 : Fin 2 → Cell := twoBank p5340 ray5340
theorem signs5340 : ∀ j, Signs p5340 (bank5340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5341 := params 28
abbrev ray5341 := rays 28
def bank5341 : Fin 2 → Cell := twoBank p5341 ray5341
theorem signs5341 : ∀ j, Signs p5341 (bank5341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5342 := params 29
abbrev ray5342 := rays 29
def bank5342 : Fin 2 → Cell := twoBank p5342 ray5342
theorem signs5342 : ∀ j, Signs p5342 (bank5342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5343 := params 30
abbrev ray5343 := rays 30
def bank5343 : Fin 2 → Cell := twoBank p5343 ray5343
theorem signs5343 : ∀ j, Signs p5343 (bank5343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5344 := params 31
abbrev ray5344 := rays 31
def bank5344 : Fin 2 → Cell := twoBank p5344 ray5344
theorem signs5344 : ∀ j, Signs p5344 (bank5344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05313_05344
