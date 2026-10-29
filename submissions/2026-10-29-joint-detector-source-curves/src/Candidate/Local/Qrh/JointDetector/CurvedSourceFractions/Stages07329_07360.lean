/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07329_07360
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98374865609627,98374555515287,98374245398872,98373935260383,98373625099821,98373314917186,98373004712479,98372694485701,98372384236853,98372073965936,98371763672950,98371453357896,98371143020774,98370832661586,98370522280332,98370211877013,98369901451630,98369591004183,98369280534674,98368970043103,98368659529470,98368348993777,98368038436024,98367727856212,98367417254342,98367106630415,98366795984431,98366485316391,98366174626296,98365863914146,98365553179943,98365242423687,98364931645379]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7328+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7329 := params 0
abbrev ray7329 := rays 0
def bank7329 : Fin 2 → Cell := twoBank p7329 ray7329
theorem signs7329 : ∀ j, Signs p7329 (bank7329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7330 := params 1
abbrev ray7330 := rays 1
def bank7330 : Fin 2 → Cell := twoBank p7330 ray7330
theorem signs7330 : ∀ j, Signs p7330 (bank7330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7331 := params 2
abbrev ray7331 := rays 2
def bank7331 : Fin 2 → Cell := twoBank p7331 ray7331
theorem signs7331 : ∀ j, Signs p7331 (bank7331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7332 := params 3
abbrev ray7332 := rays 3
def bank7332 : Fin 2 → Cell := twoBank p7332 ray7332
theorem signs7332 : ∀ j, Signs p7332 (bank7332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7333 := params 4
abbrev ray7333 := rays 4
def bank7333 : Fin 2 → Cell := twoBank p7333 ray7333
theorem signs7333 : ∀ j, Signs p7333 (bank7333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7334 := params 5
abbrev ray7334 := rays 5
def bank7334 : Fin 2 → Cell := twoBank p7334 ray7334
theorem signs7334 : ∀ j, Signs p7334 (bank7334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7335 := params 6
abbrev ray7335 := rays 6
def bank7335 : Fin 2 → Cell := twoBank p7335 ray7335
theorem signs7335 : ∀ j, Signs p7335 (bank7335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7336 := params 7
abbrev ray7336 := rays 7
def bank7336 : Fin 2 → Cell := twoBank p7336 ray7336
theorem signs7336 : ∀ j, Signs p7336 (bank7336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7337 := params 8
abbrev ray7337 := rays 8
def bank7337 : Fin 2 → Cell := twoBank p7337 ray7337
theorem signs7337 : ∀ j, Signs p7337 (bank7337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7338 := params 9
abbrev ray7338 := rays 9
def bank7338 : Fin 2 → Cell := twoBank p7338 ray7338
theorem signs7338 : ∀ j, Signs p7338 (bank7338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7339 := params 10
abbrev ray7339 := rays 10
def bank7339 : Fin 2 → Cell := twoBank p7339 ray7339
theorem signs7339 : ∀ j, Signs p7339 (bank7339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7340 := params 11
abbrev ray7340 := rays 11
def bank7340 : Fin 2 → Cell := twoBank p7340 ray7340
theorem signs7340 : ∀ j, Signs p7340 (bank7340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7341 := params 12
abbrev ray7341 := rays 12
def bank7341 : Fin 2 → Cell := twoBank p7341 ray7341
theorem signs7341 : ∀ j, Signs p7341 (bank7341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7342 := params 13
abbrev ray7342 := rays 13
def bank7342 : Fin 2 → Cell := twoBank p7342 ray7342
theorem signs7342 : ∀ j, Signs p7342 (bank7342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7343 := params 14
abbrev ray7343 := rays 14
def bank7343 : Fin 2 → Cell := twoBank p7343 ray7343
theorem signs7343 : ∀ j, Signs p7343 (bank7343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7344 := params 15
abbrev ray7344 := rays 15
def bank7344 : Fin 2 → Cell := twoBank p7344 ray7344
theorem signs7344 : ∀ j, Signs p7344 (bank7344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7345 := params 16
abbrev ray7345 := rays 16
def bank7345 : Fin 2 → Cell := twoBank p7345 ray7345
theorem signs7345 : ∀ j, Signs p7345 (bank7345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7346 := params 17
abbrev ray7346 := rays 17
def bank7346 : Fin 2 → Cell := twoBank p7346 ray7346
theorem signs7346 : ∀ j, Signs p7346 (bank7346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7347 := params 18
abbrev ray7347 := rays 18
def bank7347 : Fin 2 → Cell := twoBank p7347 ray7347
theorem signs7347 : ∀ j, Signs p7347 (bank7347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7348 := params 19
abbrev ray7348 := rays 19
def bank7348 : Fin 2 → Cell := twoBank p7348 ray7348
theorem signs7348 : ∀ j, Signs p7348 (bank7348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7349 := params 20
abbrev ray7349 := rays 20
def bank7349 : Fin 2 → Cell := twoBank p7349 ray7349
theorem signs7349 : ∀ j, Signs p7349 (bank7349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7350 := params 21
abbrev ray7350 := rays 21
def bank7350 : Fin 2 → Cell := twoBank p7350 ray7350
theorem signs7350 : ∀ j, Signs p7350 (bank7350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7351 := params 22
abbrev ray7351 := rays 22
def bank7351 : Fin 2 → Cell := twoBank p7351 ray7351
theorem signs7351 : ∀ j, Signs p7351 (bank7351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7352 := params 23
abbrev ray7352 := rays 23
def bank7352 : Fin 2 → Cell := twoBank p7352 ray7352
theorem signs7352 : ∀ j, Signs p7352 (bank7352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7353 := params 24
abbrev ray7353 := rays 24
def bank7353 : Fin 2 → Cell := twoBank p7353 ray7353
theorem signs7353 : ∀ j, Signs p7353 (bank7353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7354 := params 25
abbrev ray7354 := rays 25
def bank7354 : Fin 2 → Cell := twoBank p7354 ray7354
theorem signs7354 : ∀ j, Signs p7354 (bank7354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7355 := params 26
abbrev ray7355 := rays 26
def bank7355 : Fin 2 → Cell := twoBank p7355 ray7355
theorem signs7355 : ∀ j, Signs p7355 (bank7355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7356 := params 27
abbrev ray7356 := rays 27
def bank7356 : Fin 2 → Cell := twoBank p7356 ray7356
theorem signs7356 : ∀ j, Signs p7356 (bank7356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7357 := params 28
abbrev ray7357 := rays 28
def bank7357 : Fin 2 → Cell := twoBank p7357 ray7357
theorem signs7357 : ∀ j, Signs p7357 (bank7357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7358 := params 29
abbrev ray7358 := rays 29
def bank7358 : Fin 2 → Cell := twoBank p7358 ray7358
theorem signs7358 : ∀ j, Signs p7358 (bank7358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7359 := params 30
abbrev ray7359 := rays 30
def bank7359 : Fin 2 → Cell := twoBank p7359 ray7359
theorem signs7359 : ∀ j, Signs p7359 (bank7359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7360 := params 31
abbrev ray7360 := rays 31
def bank7360 : Fin 2 → Cell := twoBank p7360 ray7360
theorem signs7360 : ∀ j, Signs p7360 (bank7360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07329_07360
