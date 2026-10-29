/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05377_05408
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98937095823675,98936830379497,98936564911583,98936299419934,98936033904551,98935768365435,98935502802587,98935237216008,98934971605698,98934705971659,98934440313892,98934174632398,98933908927177,98933643198231,98933377445560,98933111669166,98932845869049,98932580045211,98932314197652,98932048326373,98931782431376,98931516512661,98931250570229,98930984604081,98930718614218,98930452600641,98930186563351,98929920502349,98929654417636,98929388309213,98929122177080,98928856021239,98928589841691]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5376+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5377 := params 0
abbrev ray5377 := rays 0
def bank5377 : Fin 2 → Cell := twoBank p5377 ray5377
theorem signs5377 : ∀ j, Signs p5377 (bank5377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5378 := params 1
abbrev ray5378 := rays 1
def bank5378 : Fin 2 → Cell := twoBank p5378 ray5378
theorem signs5378 : ∀ j, Signs p5378 (bank5378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5379 := params 2
abbrev ray5379 := rays 2
def bank5379 : Fin 2 → Cell := twoBank p5379 ray5379
theorem signs5379 : ∀ j, Signs p5379 (bank5379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5380 := params 3
abbrev ray5380 := rays 3
def bank5380 : Fin 2 → Cell := twoBank p5380 ray5380
theorem signs5380 : ∀ j, Signs p5380 (bank5380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5381 := params 4
abbrev ray5381 := rays 4
def bank5381 : Fin 2 → Cell := twoBank p5381 ray5381
theorem signs5381 : ∀ j, Signs p5381 (bank5381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5382 := params 5
abbrev ray5382 := rays 5
def bank5382 : Fin 2 → Cell := twoBank p5382 ray5382
theorem signs5382 : ∀ j, Signs p5382 (bank5382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5383 := params 6
abbrev ray5383 := rays 6
def bank5383 : Fin 2 → Cell := twoBank p5383 ray5383
theorem signs5383 : ∀ j, Signs p5383 (bank5383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5384 := params 7
abbrev ray5384 := rays 7
def bank5384 : Fin 2 → Cell := twoBank p5384 ray5384
theorem signs5384 : ∀ j, Signs p5384 (bank5384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5385 := params 8
abbrev ray5385 := rays 8
def bank5385 : Fin 2 → Cell := twoBank p5385 ray5385
theorem signs5385 : ∀ j, Signs p5385 (bank5385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5386 := params 9
abbrev ray5386 := rays 9
def bank5386 : Fin 2 → Cell := twoBank p5386 ray5386
theorem signs5386 : ∀ j, Signs p5386 (bank5386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5387 := params 10
abbrev ray5387 := rays 10
def bank5387 : Fin 2 → Cell := twoBank p5387 ray5387
theorem signs5387 : ∀ j, Signs p5387 (bank5387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5388 := params 11
abbrev ray5388 := rays 11
def bank5388 : Fin 2 → Cell := twoBank p5388 ray5388
theorem signs5388 : ∀ j, Signs p5388 (bank5388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5389 := params 12
abbrev ray5389 := rays 12
def bank5389 : Fin 2 → Cell := twoBank p5389 ray5389
theorem signs5389 : ∀ j, Signs p5389 (bank5389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5390 := params 13
abbrev ray5390 := rays 13
def bank5390 : Fin 2 → Cell := twoBank p5390 ray5390
theorem signs5390 : ∀ j, Signs p5390 (bank5390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5391 := params 14
abbrev ray5391 := rays 14
def bank5391 : Fin 2 → Cell := twoBank p5391 ray5391
theorem signs5391 : ∀ j, Signs p5391 (bank5391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5392 := params 15
abbrev ray5392 := rays 15
def bank5392 : Fin 2 → Cell := twoBank p5392 ray5392
theorem signs5392 : ∀ j, Signs p5392 (bank5392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5393 := params 16
abbrev ray5393 := rays 16
def bank5393 : Fin 2 → Cell := twoBank p5393 ray5393
theorem signs5393 : ∀ j, Signs p5393 (bank5393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5394 := params 17
abbrev ray5394 := rays 17
def bank5394 : Fin 2 → Cell := twoBank p5394 ray5394
theorem signs5394 : ∀ j, Signs p5394 (bank5394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5395 := params 18
abbrev ray5395 := rays 18
def bank5395 : Fin 2 → Cell := twoBank p5395 ray5395
theorem signs5395 : ∀ j, Signs p5395 (bank5395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5396 := params 19
abbrev ray5396 := rays 19
def bank5396 : Fin 2 → Cell := twoBank p5396 ray5396
theorem signs5396 : ∀ j, Signs p5396 (bank5396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5397 := params 20
abbrev ray5397 := rays 20
def bank5397 : Fin 2 → Cell := twoBank p5397 ray5397
theorem signs5397 : ∀ j, Signs p5397 (bank5397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5398 := params 21
abbrev ray5398 := rays 21
def bank5398 : Fin 2 → Cell := twoBank p5398 ray5398
theorem signs5398 : ∀ j, Signs p5398 (bank5398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5399 := params 22
abbrev ray5399 := rays 22
def bank5399 : Fin 2 → Cell := twoBank p5399 ray5399
theorem signs5399 : ∀ j, Signs p5399 (bank5399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5400 := params 23
abbrev ray5400 := rays 23
def bank5400 : Fin 2 → Cell := twoBank p5400 ray5400
theorem signs5400 : ∀ j, Signs p5400 (bank5400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5401 := params 24
abbrev ray5401 := rays 24
def bank5401 : Fin 2 → Cell := twoBank p5401 ray5401
theorem signs5401 : ∀ j, Signs p5401 (bank5401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5402 := params 25
abbrev ray5402 := rays 25
def bank5402 : Fin 2 → Cell := twoBank p5402 ray5402
theorem signs5402 : ∀ j, Signs p5402 (bank5402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5403 := params 26
abbrev ray5403 := rays 26
def bank5403 : Fin 2 → Cell := twoBank p5403 ray5403
theorem signs5403 : ∀ j, Signs p5403 (bank5403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5404 := params 27
abbrev ray5404 := rays 27
def bank5404 : Fin 2 → Cell := twoBank p5404 ray5404
theorem signs5404 : ∀ j, Signs p5404 (bank5404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5405 := params 28
abbrev ray5405 := rays 28
def bank5405 : Fin 2 → Cell := twoBank p5405 ray5405
theorem signs5405 : ∀ j, Signs p5405 (bank5405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5406 := params 29
abbrev ray5406 := rays 29
def bank5406 : Fin 2 → Cell := twoBank p5406 ray5406
theorem signs5406 : ∀ j, Signs p5406 (bank5406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5407 := params 30
abbrev ray5407 := rays 30
def bank5407 : Fin 2 → Cell := twoBank p5407 ray5407
theorem signs5407 : ∀ j, Signs p5407 (bank5407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5408 := params 31
abbrev ray5408 := rays 31
def bank5408 : Fin 2 → Cell := twoBank p5408 ray5408
theorem signs5408 : ∀ j, Signs p5408 (bank5408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05377_05408
