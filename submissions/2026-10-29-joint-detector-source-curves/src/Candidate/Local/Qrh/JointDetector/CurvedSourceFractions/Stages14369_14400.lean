/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14369_14400
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95684155519159,95683708344495,95683261153680,95682813946715,95682366723599,95681919484333,95681472228917,95681024957351,95680577669636,95680130365771,95679683045757,95679235709594,95678788357282,95678340988821,95677893604211,95677446203452,95676998786545,95676551353490,95676103904287,95675656438936,95675208957437,95674761459790,95674313945996,95673866416055,95673418869966,95672971307730,95672523729347,95672076134818,95671628524142,95671180897320,95670733254352,95670285595238,95669837919978]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14368+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14369 := params 0
abbrev ray14369 := rays 0
def bank14369 : Fin 1 → Cell := oneBank p14369 ray14369
theorem signs14369 : ∀ j, Signs p14369 (bank14369 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14370 := params 1
abbrev ray14370 := rays 1
def bank14370 : Fin 1 → Cell := oneBank p14370 ray14370
theorem signs14370 : ∀ j, Signs p14370 (bank14370 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14371 := params 2
abbrev ray14371 := rays 2
def bank14371 : Fin 1 → Cell := oneBank p14371 ray14371
theorem signs14371 : ∀ j, Signs p14371 (bank14371 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14372 := params 3
abbrev ray14372 := rays 3
def bank14372 : Fin 1 → Cell := oneBank p14372 ray14372
theorem signs14372 : ∀ j, Signs p14372 (bank14372 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14373 := params 4
abbrev ray14373 := rays 4
def bank14373 : Fin 1 → Cell := oneBank p14373 ray14373
theorem signs14373 : ∀ j, Signs p14373 (bank14373 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14374 := params 5
abbrev ray14374 := rays 5
def bank14374 : Fin 1 → Cell := oneBank p14374 ray14374
theorem signs14374 : ∀ j, Signs p14374 (bank14374 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14375 := params 6
abbrev ray14375 := rays 6
def bank14375 : Fin 1 → Cell := oneBank p14375 ray14375
theorem signs14375 : ∀ j, Signs p14375 (bank14375 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14376 := params 7
abbrev ray14376 := rays 7
def bank14376 : Fin 1 → Cell := oneBank p14376 ray14376
theorem signs14376 : ∀ j, Signs p14376 (bank14376 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14377 := params 8
abbrev ray14377 := rays 8
def bank14377 : Fin 1 → Cell := oneBank p14377 ray14377
theorem signs14377 : ∀ j, Signs p14377 (bank14377 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14378 := params 9
abbrev ray14378 := rays 9
def bank14378 : Fin 1 → Cell := oneBank p14378 ray14378
theorem signs14378 : ∀ j, Signs p14378 (bank14378 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14379 := params 10
abbrev ray14379 := rays 10
def bank14379 : Fin 1 → Cell := oneBank p14379 ray14379
theorem signs14379 : ∀ j, Signs p14379 (bank14379 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14380 := params 11
abbrev ray14380 := rays 11
def bank14380 : Fin 1 → Cell := oneBank p14380 ray14380
theorem signs14380 : ∀ j, Signs p14380 (bank14380 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14381 := params 12
abbrev ray14381 := rays 12
def bank14381 : Fin 1 → Cell := oneBank p14381 ray14381
theorem signs14381 : ∀ j, Signs p14381 (bank14381 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14382 := params 13
abbrev ray14382 := rays 13
def bank14382 : Fin 1 → Cell := oneBank p14382 ray14382
theorem signs14382 : ∀ j, Signs p14382 (bank14382 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14383 := params 14
abbrev ray14383 := rays 14
def bank14383 : Fin 1 → Cell := oneBank p14383 ray14383
theorem signs14383 : ∀ j, Signs p14383 (bank14383 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14384 := params 15
abbrev ray14384 := rays 15
def bank14384 : Fin 1 → Cell := oneBank p14384 ray14384
theorem signs14384 : ∀ j, Signs p14384 (bank14384 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14385 := params 16
abbrev ray14385 := rays 16
def bank14385 : Fin 1 → Cell := oneBank p14385 ray14385
theorem signs14385 : ∀ j, Signs p14385 (bank14385 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14386 := params 17
abbrev ray14386 := rays 17
def bank14386 : Fin 1 → Cell := oneBank p14386 ray14386
theorem signs14386 : ∀ j, Signs p14386 (bank14386 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14387 := params 18
abbrev ray14387 := rays 18
def bank14387 : Fin 1 → Cell := oneBank p14387 ray14387
theorem signs14387 : ∀ j, Signs p14387 (bank14387 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14388 := params 19
abbrev ray14388 := rays 19
def bank14388 : Fin 1 → Cell := oneBank p14388 ray14388
theorem signs14388 : ∀ j, Signs p14388 (bank14388 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14389 := params 20
abbrev ray14389 := rays 20
def bank14389 : Fin 1 → Cell := oneBank p14389 ray14389
theorem signs14389 : ∀ j, Signs p14389 (bank14389 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14390 := params 21
abbrev ray14390 := rays 21
def bank14390 : Fin 1 → Cell := oneBank p14390 ray14390
theorem signs14390 : ∀ j, Signs p14390 (bank14390 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14391 := params 22
abbrev ray14391 := rays 22
def bank14391 : Fin 1 → Cell := oneBank p14391 ray14391
theorem signs14391 : ∀ j, Signs p14391 (bank14391 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14392 := params 23
abbrev ray14392 := rays 23
def bank14392 : Fin 1 → Cell := oneBank p14392 ray14392
theorem signs14392 : ∀ j, Signs p14392 (bank14392 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14393 := params 24
abbrev ray14393 := rays 24
def bank14393 : Fin 1 → Cell := oneBank p14393 ray14393
theorem signs14393 : ∀ j, Signs p14393 (bank14393 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14394 := params 25
abbrev ray14394 := rays 25
def bank14394 : Fin 1 → Cell := oneBank p14394 ray14394
theorem signs14394 : ∀ j, Signs p14394 (bank14394 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14395 := params 26
abbrev ray14395 := rays 26
def bank14395 : Fin 1 → Cell := oneBank p14395 ray14395
theorem signs14395 : ∀ j, Signs p14395 (bank14395 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14396 := params 27
abbrev ray14396 := rays 27
def bank14396 : Fin 1 → Cell := oneBank p14396 ray14396
theorem signs14396 : ∀ j, Signs p14396 (bank14396 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14397 := params 28
abbrev ray14397 := rays 28
def bank14397 : Fin 1 → Cell := oneBank p14397 ray14397
theorem signs14397 : ∀ j, Signs p14397 (bank14397 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14398 := params 29
abbrev ray14398 := rays 29
def bank14398 : Fin 1 → Cell := oneBank p14398 ray14398
theorem signs14398 : ∀ j, Signs p14398 (bank14398 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14399 := params 30
abbrev ray14399 := rays 30
def bank14399 : Fin 1 → Cell := oneBank p14399 ray14399
theorem signs14399 : ∀ j, Signs p14399 (bank14399 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14400 := params 31
abbrev ray14400 := rays 31
def bank14400 : Fin 1 → Cell := oneBank p14400 ray14400
theorem signs14400 : ∀ j, Signs p14400 (bank14400 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14369_14400
