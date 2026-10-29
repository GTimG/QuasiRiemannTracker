/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05345_05376
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98945577499126,98945312815000,98945048107107,98944783375449,98944518620026,98944253840840,98943989037891,98943724211180,98943459360709,98943194486478,98942929588488,98942664666740,98942399721236,98942134751976,98941869758961,98941604742192,98941339701670,98941074637395,98940809549369,98940544437593,98940279302068,98940014142795,98939748959774,98939483753007,98939218522495,98938953268238,98938687990238,98938422688495,98938157363010,98937892013785,98937626640820,98937361244116,98937095823675]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5344+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5345 := params 0
abbrev ray5345 := rays 0
def bank5345 : Fin 2 → Cell := twoBank p5345 ray5345
theorem signs5345 : ∀ j, Signs p5345 (bank5345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5346 := params 1
abbrev ray5346 := rays 1
def bank5346 : Fin 2 → Cell := twoBank p5346 ray5346
theorem signs5346 : ∀ j, Signs p5346 (bank5346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5347 := params 2
abbrev ray5347 := rays 2
def bank5347 : Fin 2 → Cell := twoBank p5347 ray5347
theorem signs5347 : ∀ j, Signs p5347 (bank5347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5348 := params 3
abbrev ray5348 := rays 3
def bank5348 : Fin 2 → Cell := twoBank p5348 ray5348
theorem signs5348 : ∀ j, Signs p5348 (bank5348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5349 := params 4
abbrev ray5349 := rays 4
def bank5349 : Fin 2 → Cell := twoBank p5349 ray5349
theorem signs5349 : ∀ j, Signs p5349 (bank5349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5350 := params 5
abbrev ray5350 := rays 5
def bank5350 : Fin 2 → Cell := twoBank p5350 ray5350
theorem signs5350 : ∀ j, Signs p5350 (bank5350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5351 := params 6
abbrev ray5351 := rays 6
def bank5351 : Fin 2 → Cell := twoBank p5351 ray5351
theorem signs5351 : ∀ j, Signs p5351 (bank5351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5352 := params 7
abbrev ray5352 := rays 7
def bank5352 : Fin 2 → Cell := twoBank p5352 ray5352
theorem signs5352 : ∀ j, Signs p5352 (bank5352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5353 := params 8
abbrev ray5353 := rays 8
def bank5353 : Fin 2 → Cell := twoBank p5353 ray5353
theorem signs5353 : ∀ j, Signs p5353 (bank5353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5354 := params 9
abbrev ray5354 := rays 9
def bank5354 : Fin 2 → Cell := twoBank p5354 ray5354
theorem signs5354 : ∀ j, Signs p5354 (bank5354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5355 := params 10
abbrev ray5355 := rays 10
def bank5355 : Fin 2 → Cell := twoBank p5355 ray5355
theorem signs5355 : ∀ j, Signs p5355 (bank5355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5356 := params 11
abbrev ray5356 := rays 11
def bank5356 : Fin 2 → Cell := twoBank p5356 ray5356
theorem signs5356 : ∀ j, Signs p5356 (bank5356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5357 := params 12
abbrev ray5357 := rays 12
def bank5357 : Fin 2 → Cell := twoBank p5357 ray5357
theorem signs5357 : ∀ j, Signs p5357 (bank5357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5358 := params 13
abbrev ray5358 := rays 13
def bank5358 : Fin 2 → Cell := twoBank p5358 ray5358
theorem signs5358 : ∀ j, Signs p5358 (bank5358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5359 := params 14
abbrev ray5359 := rays 14
def bank5359 : Fin 2 → Cell := twoBank p5359 ray5359
theorem signs5359 : ∀ j, Signs p5359 (bank5359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5360 := params 15
abbrev ray5360 := rays 15
def bank5360 : Fin 2 → Cell := twoBank p5360 ray5360
theorem signs5360 : ∀ j, Signs p5360 (bank5360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5361 := params 16
abbrev ray5361 := rays 16
def bank5361 : Fin 2 → Cell := twoBank p5361 ray5361
theorem signs5361 : ∀ j, Signs p5361 (bank5361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5362 := params 17
abbrev ray5362 := rays 17
def bank5362 : Fin 2 → Cell := twoBank p5362 ray5362
theorem signs5362 : ∀ j, Signs p5362 (bank5362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5363 := params 18
abbrev ray5363 := rays 18
def bank5363 : Fin 2 → Cell := twoBank p5363 ray5363
theorem signs5363 : ∀ j, Signs p5363 (bank5363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5364 := params 19
abbrev ray5364 := rays 19
def bank5364 : Fin 2 → Cell := twoBank p5364 ray5364
theorem signs5364 : ∀ j, Signs p5364 (bank5364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5365 := params 20
abbrev ray5365 := rays 20
def bank5365 : Fin 2 → Cell := twoBank p5365 ray5365
theorem signs5365 : ∀ j, Signs p5365 (bank5365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5366 := params 21
abbrev ray5366 := rays 21
def bank5366 : Fin 2 → Cell := twoBank p5366 ray5366
theorem signs5366 : ∀ j, Signs p5366 (bank5366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5367 := params 22
abbrev ray5367 := rays 22
def bank5367 : Fin 2 → Cell := twoBank p5367 ray5367
theorem signs5367 : ∀ j, Signs p5367 (bank5367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5368 := params 23
abbrev ray5368 := rays 23
def bank5368 : Fin 2 → Cell := twoBank p5368 ray5368
theorem signs5368 : ∀ j, Signs p5368 (bank5368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5369 := params 24
abbrev ray5369 := rays 24
def bank5369 : Fin 2 → Cell := twoBank p5369 ray5369
theorem signs5369 : ∀ j, Signs p5369 (bank5369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5370 := params 25
abbrev ray5370 := rays 25
def bank5370 : Fin 2 → Cell := twoBank p5370 ray5370
theorem signs5370 : ∀ j, Signs p5370 (bank5370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5371 := params 26
abbrev ray5371 := rays 26
def bank5371 : Fin 2 → Cell := twoBank p5371 ray5371
theorem signs5371 : ∀ j, Signs p5371 (bank5371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5372 := params 27
abbrev ray5372 := rays 27
def bank5372 : Fin 2 → Cell := twoBank p5372 ray5372
theorem signs5372 : ∀ j, Signs p5372 (bank5372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5373 := params 28
abbrev ray5373 := rays 28
def bank5373 : Fin 2 → Cell := twoBank p5373 ray5373
theorem signs5373 : ∀ j, Signs p5373 (bank5373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5374 := params 29
abbrev ray5374 := rays 29
def bank5374 : Fin 2 → Cell := twoBank p5374 ray5374
theorem signs5374 : ∀ j, Signs p5374 (bank5374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5375 := params 30
abbrev ray5375 := rays 30
def bank5375 : Fin 2 → Cell := twoBank p5375 ray5375
theorem signs5375 : ∀ j, Signs p5375 (bank5375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5376 := params 31
abbrev ray5376 := rays 31
def bank5376 : Fin 2 → Cell := twoBank p5376 ray5376
theorem signs5376 : ∀ j, Signs p5376 (bank5376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05345_05376
