/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10337_10368
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97345418548701,97345045110194,97344671651533,97344298172718,97343924673749,97343551154627,97343177615353,97342804055927,97342430476350,97342056876622,97341683256744,97341309616716,97340935956539,97340562276213,97340188575739,97339814855118,97339441114350,97339067353435,97338693572374,97338319771168,97337945949817,97337572108321,97337198246681,97336824364898,97336450462972,97336076540904,97335702598694,97335328636343,97334954653851,97334580651219,97334206628448,97333832585537,97333458522488]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10336+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10337 := params 0
abbrev ray10337 := rays 0
def bank10337 : Fin 2 → Cell := twoBank p10337 ray10337
theorem signs10337 : ∀ j, Signs p10337 (bank10337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10338 := params 1
abbrev ray10338 := rays 1
def bank10338 : Fin 2 → Cell := twoBank p10338 ray10338
theorem signs10338 : ∀ j, Signs p10338 (bank10338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10339 := params 2
abbrev ray10339 := rays 2
def bank10339 : Fin 2 → Cell := twoBank p10339 ray10339
theorem signs10339 : ∀ j, Signs p10339 (bank10339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10340 := params 3
abbrev ray10340 := rays 3
def bank10340 : Fin 2 → Cell := twoBank p10340 ray10340
theorem signs10340 : ∀ j, Signs p10340 (bank10340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10341 := params 4
abbrev ray10341 := rays 4
def bank10341 : Fin 2 → Cell := twoBank p10341 ray10341
theorem signs10341 : ∀ j, Signs p10341 (bank10341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10342 := params 5
abbrev ray10342 := rays 5
def bank10342 : Fin 2 → Cell := twoBank p10342 ray10342
theorem signs10342 : ∀ j, Signs p10342 (bank10342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10343 := params 6
abbrev ray10343 := rays 6
def bank10343 : Fin 2 → Cell := twoBank p10343 ray10343
theorem signs10343 : ∀ j, Signs p10343 (bank10343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10344 := params 7
abbrev ray10344 := rays 7
def bank10344 : Fin 2 → Cell := twoBank p10344 ray10344
theorem signs10344 : ∀ j, Signs p10344 (bank10344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10345 := params 8
abbrev ray10345 := rays 8
def bank10345 : Fin 2 → Cell := twoBank p10345 ray10345
theorem signs10345 : ∀ j, Signs p10345 (bank10345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10346 := params 9
abbrev ray10346 := rays 9
def bank10346 : Fin 2 → Cell := twoBank p10346 ray10346
theorem signs10346 : ∀ j, Signs p10346 (bank10346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10347 := params 10
abbrev ray10347 := rays 10
def bank10347 : Fin 2 → Cell := twoBank p10347 ray10347
theorem signs10347 : ∀ j, Signs p10347 (bank10347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10348 := params 11
abbrev ray10348 := rays 11
def bank10348 : Fin 2 → Cell := twoBank p10348 ray10348
theorem signs10348 : ∀ j, Signs p10348 (bank10348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10349 := params 12
abbrev ray10349 := rays 12
def bank10349 : Fin 2 → Cell := twoBank p10349 ray10349
theorem signs10349 : ∀ j, Signs p10349 (bank10349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10350 := params 13
abbrev ray10350 := rays 13
def bank10350 : Fin 2 → Cell := twoBank p10350 ray10350
theorem signs10350 : ∀ j, Signs p10350 (bank10350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10351 := params 14
abbrev ray10351 := rays 14
def bank10351 : Fin 2 → Cell := twoBank p10351 ray10351
theorem signs10351 : ∀ j, Signs p10351 (bank10351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10352 := params 15
abbrev ray10352 := rays 15
def bank10352 : Fin 2 → Cell := twoBank p10352 ray10352
theorem signs10352 : ∀ j, Signs p10352 (bank10352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10353 := params 16
abbrev ray10353 := rays 16
def bank10353 : Fin 2 → Cell := twoBank p10353 ray10353
theorem signs10353 : ∀ j, Signs p10353 (bank10353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10354 := params 17
abbrev ray10354 := rays 17
def bank10354 : Fin 2 → Cell := twoBank p10354 ray10354
theorem signs10354 : ∀ j, Signs p10354 (bank10354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10355 := params 18
abbrev ray10355 := rays 18
def bank10355 : Fin 2 → Cell := twoBank p10355 ray10355
theorem signs10355 : ∀ j, Signs p10355 (bank10355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10356 := params 19
abbrev ray10356 := rays 19
def bank10356 : Fin 2 → Cell := twoBank p10356 ray10356
theorem signs10356 : ∀ j, Signs p10356 (bank10356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10357 := params 20
abbrev ray10357 := rays 20
def bank10357 : Fin 2 → Cell := twoBank p10357 ray10357
theorem signs10357 : ∀ j, Signs p10357 (bank10357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10358 := params 21
abbrev ray10358 := rays 21
def bank10358 : Fin 2 → Cell := twoBank p10358 ray10358
theorem signs10358 : ∀ j, Signs p10358 (bank10358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10359 := params 22
abbrev ray10359 := rays 22
def bank10359 : Fin 2 → Cell := twoBank p10359 ray10359
theorem signs10359 : ∀ j, Signs p10359 (bank10359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10360 := params 23
abbrev ray10360 := rays 23
def bank10360 : Fin 2 → Cell := twoBank p10360 ray10360
theorem signs10360 : ∀ j, Signs p10360 (bank10360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10361 := params 24
abbrev ray10361 := rays 24
def bank10361 : Fin 2 → Cell := twoBank p10361 ray10361
theorem signs10361 : ∀ j, Signs p10361 (bank10361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10362 := params 25
abbrev ray10362 := rays 25
def bank10362 : Fin 2 → Cell := twoBank p10362 ray10362
theorem signs10362 : ∀ j, Signs p10362 (bank10362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10363 := params 26
abbrev ray10363 := rays 26
def bank10363 : Fin 2 → Cell := twoBank p10363 ray10363
theorem signs10363 : ∀ j, Signs p10363 (bank10363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10364 := params 27
abbrev ray10364 := rays 27
def bank10364 : Fin 2 → Cell := twoBank p10364 ray10364
theorem signs10364 : ∀ j, Signs p10364 (bank10364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10365 := params 28
abbrev ray10365 := rays 28
def bank10365 : Fin 2 → Cell := twoBank p10365 ray10365
theorem signs10365 : ∀ j, Signs p10365 (bank10365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10366 := params 29
abbrev ray10366 := rays 29
def bank10366 : Fin 2 → Cell := twoBank p10366 ray10366
theorem signs10366 : ∀ j, Signs p10366 (bank10366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10367 := params 30
abbrev ray10367 := rays 30
def bank10367 : Fin 2 → Cell := twoBank p10367 ray10367
theorem signs10367 : ∀ j, Signs p10367 (bank10367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10368 := params 31
abbrev ray10368 := rays 31
def bank10368 : Fin 2 → Cell := twoBank p10368 ray10368
theorem signs10368 : ∀ j, Signs p10368 (bank10368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10337_10368
