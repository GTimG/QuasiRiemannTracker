/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09345_09376
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97705853508923,97705500336166,97705147142695,97704793928510,97704440693612,97704087438001,97703734161678,97703380864644,97703027546899,97702674208444,97702320849279,97701967469405,97701614068823,97701260647533,97700907205536,97700553742832,97700200259422,97699846755307,97699493230487,97699139684963,97698786118735,97698432531804,97698078924171,97697725295836,97697371646800,97697017977063,97696664286626,97696310575490,97695956843655,97695603091122,97695249317891,97694895523963,97694541709339]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9344+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9345 := params 0
abbrev ray9345 := rays 0
def bank9345 : Fin 2 → Cell := twoBank p9345 ray9345
theorem signs9345 : ∀ j, Signs p9345 (bank9345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9346 := params 1
abbrev ray9346 := rays 1
def bank9346 : Fin 2 → Cell := twoBank p9346 ray9346
theorem signs9346 : ∀ j, Signs p9346 (bank9346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9347 := params 2
abbrev ray9347 := rays 2
def bank9347 : Fin 2 → Cell := twoBank p9347 ray9347
theorem signs9347 : ∀ j, Signs p9347 (bank9347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9348 := params 3
abbrev ray9348 := rays 3
def bank9348 : Fin 2 → Cell := twoBank p9348 ray9348
theorem signs9348 : ∀ j, Signs p9348 (bank9348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9349 := params 4
abbrev ray9349 := rays 4
def bank9349 : Fin 2 → Cell := twoBank p9349 ray9349
theorem signs9349 : ∀ j, Signs p9349 (bank9349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9350 := params 5
abbrev ray9350 := rays 5
def bank9350 : Fin 2 → Cell := twoBank p9350 ray9350
theorem signs9350 : ∀ j, Signs p9350 (bank9350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9351 := params 6
abbrev ray9351 := rays 6
def bank9351 : Fin 2 → Cell := twoBank p9351 ray9351
theorem signs9351 : ∀ j, Signs p9351 (bank9351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9352 := params 7
abbrev ray9352 := rays 7
def bank9352 : Fin 2 → Cell := twoBank p9352 ray9352
theorem signs9352 : ∀ j, Signs p9352 (bank9352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9353 := params 8
abbrev ray9353 := rays 8
def bank9353 : Fin 2 → Cell := twoBank p9353 ray9353
theorem signs9353 : ∀ j, Signs p9353 (bank9353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9354 := params 9
abbrev ray9354 := rays 9
def bank9354 : Fin 2 → Cell := twoBank p9354 ray9354
theorem signs9354 : ∀ j, Signs p9354 (bank9354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9355 := params 10
abbrev ray9355 := rays 10
def bank9355 : Fin 2 → Cell := twoBank p9355 ray9355
theorem signs9355 : ∀ j, Signs p9355 (bank9355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9356 := params 11
abbrev ray9356 := rays 11
def bank9356 : Fin 2 → Cell := twoBank p9356 ray9356
theorem signs9356 : ∀ j, Signs p9356 (bank9356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9357 := params 12
abbrev ray9357 := rays 12
def bank9357 : Fin 2 → Cell := twoBank p9357 ray9357
theorem signs9357 : ∀ j, Signs p9357 (bank9357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9358 := params 13
abbrev ray9358 := rays 13
def bank9358 : Fin 2 → Cell := twoBank p9358 ray9358
theorem signs9358 : ∀ j, Signs p9358 (bank9358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9359 := params 14
abbrev ray9359 := rays 14
def bank9359 : Fin 2 → Cell := twoBank p9359 ray9359
theorem signs9359 : ∀ j, Signs p9359 (bank9359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9360 := params 15
abbrev ray9360 := rays 15
def bank9360 : Fin 2 → Cell := twoBank p9360 ray9360
theorem signs9360 : ∀ j, Signs p9360 (bank9360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9361 := params 16
abbrev ray9361 := rays 16
def bank9361 : Fin 2 → Cell := twoBank p9361 ray9361
theorem signs9361 : ∀ j, Signs p9361 (bank9361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9362 := params 17
abbrev ray9362 := rays 17
def bank9362 : Fin 2 → Cell := twoBank p9362 ray9362
theorem signs9362 : ∀ j, Signs p9362 (bank9362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9363 := params 18
abbrev ray9363 := rays 18
def bank9363 : Fin 2 → Cell := twoBank p9363 ray9363
theorem signs9363 : ∀ j, Signs p9363 (bank9363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9364 := params 19
abbrev ray9364 := rays 19
def bank9364 : Fin 2 → Cell := twoBank p9364 ray9364
theorem signs9364 : ∀ j, Signs p9364 (bank9364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9365 := params 20
abbrev ray9365 := rays 20
def bank9365 : Fin 2 → Cell := twoBank p9365 ray9365
theorem signs9365 : ∀ j, Signs p9365 (bank9365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9366 := params 21
abbrev ray9366 := rays 21
def bank9366 : Fin 2 → Cell := twoBank p9366 ray9366
theorem signs9366 : ∀ j, Signs p9366 (bank9366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9367 := params 22
abbrev ray9367 := rays 22
def bank9367 : Fin 2 → Cell := twoBank p9367 ray9367
theorem signs9367 : ∀ j, Signs p9367 (bank9367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9368 := params 23
abbrev ray9368 := rays 23
def bank9368 : Fin 2 → Cell := twoBank p9368 ray9368
theorem signs9368 : ∀ j, Signs p9368 (bank9368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9369 := params 24
abbrev ray9369 := rays 24
def bank9369 : Fin 2 → Cell := twoBank p9369 ray9369
theorem signs9369 : ∀ j, Signs p9369 (bank9369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9370 := params 25
abbrev ray9370 := rays 25
def bank9370 : Fin 2 → Cell := twoBank p9370 ray9370
theorem signs9370 : ∀ j, Signs p9370 (bank9370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9371 := params 26
abbrev ray9371 := rays 26
def bank9371 : Fin 2 → Cell := twoBank p9371 ray9371
theorem signs9371 : ∀ j, Signs p9371 (bank9371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9372 := params 27
abbrev ray9372 := rays 27
def bank9372 : Fin 2 → Cell := twoBank p9372 ray9372
theorem signs9372 : ∀ j, Signs p9372 (bank9372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9373 := params 28
abbrev ray9373 := rays 28
def bank9373 : Fin 2 → Cell := twoBank p9373 ray9373
theorem signs9373 : ∀ j, Signs p9373 (bank9373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9374 := params 29
abbrev ray9374 := rays 29
def bank9374 : Fin 2 → Cell := twoBank p9374 ray9374
theorem signs9374 : ∀ j, Signs p9374 (bank9374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9375 := params 30
abbrev ray9375 := rays 30
def bank9375 : Fin 2 → Cell := twoBank p9375 ray9375
theorem signs9375 : ∀ j, Signs p9375 (bank9375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9376 := params 31
abbrev ray9376 := rays 31
def bank9376 : Fin 2 → Cell := twoBank p9376 ray9376
theorem signs9376 : ∀ j, Signs p9376 (bank9376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09345_09376
