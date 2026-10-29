/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08321_08352
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98056520817657,98056189183385,98055857527747,98055525850745,98055194152379,98054862432649,98054530691557,98054198929103,98053867145287,98053535340111,98053203513575,98052871665679,98052539796425,98052207905813,98051875993843,98051544060517,98051212105835,98050880129797,98050548132405,98050216113659,98049884073560,98049552012108,98049219929304,98048887825149,98048555699643,98048223552788,98047891384583,98047559195030,98047226984129,98046894751881,98046562498286,98046230223345,98045897927059]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8320+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8321 := params 0
abbrev ray8321 := rays 0
def bank8321 : Fin 2 → Cell := twoBank p8321 ray8321
theorem signs8321 : ∀ j, Signs p8321 (bank8321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8322 := params 1
abbrev ray8322 := rays 1
def bank8322 : Fin 2 → Cell := twoBank p8322 ray8322
theorem signs8322 : ∀ j, Signs p8322 (bank8322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8323 := params 2
abbrev ray8323 := rays 2
def bank8323 : Fin 2 → Cell := twoBank p8323 ray8323
theorem signs8323 : ∀ j, Signs p8323 (bank8323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8324 := params 3
abbrev ray8324 := rays 3
def bank8324 : Fin 2 → Cell := twoBank p8324 ray8324
theorem signs8324 : ∀ j, Signs p8324 (bank8324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8325 := params 4
abbrev ray8325 := rays 4
def bank8325 : Fin 2 → Cell := twoBank p8325 ray8325
theorem signs8325 : ∀ j, Signs p8325 (bank8325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8326 := params 5
abbrev ray8326 := rays 5
def bank8326 : Fin 2 → Cell := twoBank p8326 ray8326
theorem signs8326 : ∀ j, Signs p8326 (bank8326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8327 := params 6
abbrev ray8327 := rays 6
def bank8327 : Fin 2 → Cell := twoBank p8327 ray8327
theorem signs8327 : ∀ j, Signs p8327 (bank8327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8328 := params 7
abbrev ray8328 := rays 7
def bank8328 : Fin 2 → Cell := twoBank p8328 ray8328
theorem signs8328 : ∀ j, Signs p8328 (bank8328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8329 := params 8
abbrev ray8329 := rays 8
def bank8329 : Fin 2 → Cell := twoBank p8329 ray8329
theorem signs8329 : ∀ j, Signs p8329 (bank8329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8330 := params 9
abbrev ray8330 := rays 9
def bank8330 : Fin 2 → Cell := twoBank p8330 ray8330
theorem signs8330 : ∀ j, Signs p8330 (bank8330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8331 := params 10
abbrev ray8331 := rays 10
def bank8331 : Fin 2 → Cell := twoBank p8331 ray8331
theorem signs8331 : ∀ j, Signs p8331 (bank8331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8332 := params 11
abbrev ray8332 := rays 11
def bank8332 : Fin 2 → Cell := twoBank p8332 ray8332
theorem signs8332 : ∀ j, Signs p8332 (bank8332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8333 := params 12
abbrev ray8333 := rays 12
def bank8333 : Fin 2 → Cell := twoBank p8333 ray8333
theorem signs8333 : ∀ j, Signs p8333 (bank8333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8334 := params 13
abbrev ray8334 := rays 13
def bank8334 : Fin 2 → Cell := twoBank p8334 ray8334
theorem signs8334 : ∀ j, Signs p8334 (bank8334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8335 := params 14
abbrev ray8335 := rays 14
def bank8335 : Fin 2 → Cell := twoBank p8335 ray8335
theorem signs8335 : ∀ j, Signs p8335 (bank8335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8336 := params 15
abbrev ray8336 := rays 15
def bank8336 : Fin 2 → Cell := twoBank p8336 ray8336
theorem signs8336 : ∀ j, Signs p8336 (bank8336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8337 := params 16
abbrev ray8337 := rays 16
def bank8337 : Fin 2 → Cell := twoBank p8337 ray8337
theorem signs8337 : ∀ j, Signs p8337 (bank8337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8338 := params 17
abbrev ray8338 := rays 17
def bank8338 : Fin 2 → Cell := twoBank p8338 ray8338
theorem signs8338 : ∀ j, Signs p8338 (bank8338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8339 := params 18
abbrev ray8339 := rays 18
def bank8339 : Fin 2 → Cell := twoBank p8339 ray8339
theorem signs8339 : ∀ j, Signs p8339 (bank8339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8340 := params 19
abbrev ray8340 := rays 19
def bank8340 : Fin 2 → Cell := twoBank p8340 ray8340
theorem signs8340 : ∀ j, Signs p8340 (bank8340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8341 := params 20
abbrev ray8341 := rays 20
def bank8341 : Fin 2 → Cell := twoBank p8341 ray8341
theorem signs8341 : ∀ j, Signs p8341 (bank8341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8342 := params 21
abbrev ray8342 := rays 21
def bank8342 : Fin 2 → Cell := twoBank p8342 ray8342
theorem signs8342 : ∀ j, Signs p8342 (bank8342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8343 := params 22
abbrev ray8343 := rays 22
def bank8343 : Fin 2 → Cell := twoBank p8343 ray8343
theorem signs8343 : ∀ j, Signs p8343 (bank8343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8344 := params 23
abbrev ray8344 := rays 23
def bank8344 : Fin 2 → Cell := twoBank p8344 ray8344
theorem signs8344 : ∀ j, Signs p8344 (bank8344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8345 := params 24
abbrev ray8345 := rays 24
def bank8345 : Fin 2 → Cell := twoBank p8345 ray8345
theorem signs8345 : ∀ j, Signs p8345 (bank8345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8346 := params 25
abbrev ray8346 := rays 25
def bank8346 : Fin 2 → Cell := twoBank p8346 ray8346
theorem signs8346 : ∀ j, Signs p8346 (bank8346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8347 := params 26
abbrev ray8347 := rays 26
def bank8347 : Fin 2 → Cell := twoBank p8347 ray8347
theorem signs8347 : ∀ j, Signs p8347 (bank8347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8348 := params 27
abbrev ray8348 := rays 27
def bank8348 : Fin 2 → Cell := twoBank p8348 ray8348
theorem signs8348 : ∀ j, Signs p8348 (bank8348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8349 := params 28
abbrev ray8349 := rays 28
def bank8349 : Fin 2 → Cell := twoBank p8349 ray8349
theorem signs8349 : ∀ j, Signs p8349 (bank8349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8350 := params 29
abbrev ray8350 := rays 29
def bank8350 : Fin 2 → Cell := twoBank p8350 ray8350
theorem signs8350 : ∀ j, Signs p8350 (bank8350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8351 := params 30
abbrev ray8351 := rays 30
def bank8351 : Fin 2 → Cell := twoBank p8351 ray8351
theorem signs8351 : ∀ j, Signs p8351 (bank8351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8352 := params 31
abbrev ray8352 := rays 31
def bank8352 : Fin 2 → Cell := twoBank p8352 ray8352
theorem signs8352 : ∀ j, Signs p8352 (bank8352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08321_08352
