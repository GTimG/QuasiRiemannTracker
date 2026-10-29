/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12321_12352
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96565520652503,96565108192839,96564695713955,96564283215852,96563870698530,96563458161989,96563045606230,96562633031253,96562220437059,96561807823648,96561395191021,96560982539177,96560569868118,96560157177843,96559744468354,96559331739650,96558918991732,96558506224600,96558093438255,96557680632697,96557267807927,96556854963945,96556442100752,96556029218347,96555616316732,96555203395906,96554790455870,96554377496625,96553964518171,96553551520508,96553138503637,96552725467558,96552312412272]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12320+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12321 := params 0
abbrev ray12321 := rays 0
def bank12321 : Fin 2 → Cell := twoBank p12321 ray12321
theorem signs12321 : ∀ j, Signs p12321 (bank12321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12322 := params 1
abbrev ray12322 := rays 1
def bank12322 : Fin 2 → Cell := twoBank p12322 ray12322
theorem signs12322 : ∀ j, Signs p12322 (bank12322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12323 := params 2
abbrev ray12323 := rays 2
def bank12323 : Fin 2 → Cell := twoBank p12323 ray12323
theorem signs12323 : ∀ j, Signs p12323 (bank12323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12324 := params 3
abbrev ray12324 := rays 3
def bank12324 : Fin 2 → Cell := twoBank p12324 ray12324
theorem signs12324 : ∀ j, Signs p12324 (bank12324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12325 := params 4
abbrev ray12325 := rays 4
def bank12325 : Fin 2 → Cell := twoBank p12325 ray12325
theorem signs12325 : ∀ j, Signs p12325 (bank12325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12326 := params 5
abbrev ray12326 := rays 5
def bank12326 : Fin 2 → Cell := twoBank p12326 ray12326
theorem signs12326 : ∀ j, Signs p12326 (bank12326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12327 := params 6
abbrev ray12327 := rays 6
def bank12327 : Fin 2 → Cell := twoBank p12327 ray12327
theorem signs12327 : ∀ j, Signs p12327 (bank12327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12328 := params 7
abbrev ray12328 := rays 7
def bank12328 : Fin 2 → Cell := twoBank p12328 ray12328
theorem signs12328 : ∀ j, Signs p12328 (bank12328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12329 := params 8
abbrev ray12329 := rays 8
def bank12329 : Fin 2 → Cell := twoBank p12329 ray12329
theorem signs12329 : ∀ j, Signs p12329 (bank12329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12330 := params 9
abbrev ray12330 := rays 9
def bank12330 : Fin 2 → Cell := twoBank p12330 ray12330
theorem signs12330 : ∀ j, Signs p12330 (bank12330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12331 := params 10
abbrev ray12331 := rays 10
def bank12331 : Fin 2 → Cell := twoBank p12331 ray12331
theorem signs12331 : ∀ j, Signs p12331 (bank12331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12332 := params 11
abbrev ray12332 := rays 11
def bank12332 : Fin 2 → Cell := twoBank p12332 ray12332
theorem signs12332 : ∀ j, Signs p12332 (bank12332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12333 := params 12
abbrev ray12333 := rays 12
def bank12333 : Fin 2 → Cell := twoBank p12333 ray12333
theorem signs12333 : ∀ j, Signs p12333 (bank12333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12334 := params 13
abbrev ray12334 := rays 13
def bank12334 : Fin 2 → Cell := twoBank p12334 ray12334
theorem signs12334 : ∀ j, Signs p12334 (bank12334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12335 := params 14
abbrev ray12335 := rays 14
def bank12335 : Fin 2 → Cell := twoBank p12335 ray12335
theorem signs12335 : ∀ j, Signs p12335 (bank12335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12336 := params 15
abbrev ray12336 := rays 15
def bank12336 : Fin 2 → Cell := twoBank p12336 ray12336
theorem signs12336 : ∀ j, Signs p12336 (bank12336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12337 := params 16
abbrev ray12337 := rays 16
def bank12337 : Fin 2 → Cell := twoBank p12337 ray12337
theorem signs12337 : ∀ j, Signs p12337 (bank12337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12338 := params 17
abbrev ray12338 := rays 17
def bank12338 : Fin 2 → Cell := twoBank p12338 ray12338
theorem signs12338 : ∀ j, Signs p12338 (bank12338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12339 := params 18
abbrev ray12339 := rays 18
def bank12339 : Fin 2 → Cell := twoBank p12339 ray12339
theorem signs12339 : ∀ j, Signs p12339 (bank12339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12340 := params 19
abbrev ray12340 := rays 19
def bank12340 : Fin 2 → Cell := twoBank p12340 ray12340
theorem signs12340 : ∀ j, Signs p12340 (bank12340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12341 := params 20
abbrev ray12341 := rays 20
def bank12341 : Fin 2 → Cell := twoBank p12341 ray12341
theorem signs12341 : ∀ j, Signs p12341 (bank12341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12342 := params 21
abbrev ray12342 := rays 21
def bank12342 : Fin 2 → Cell := twoBank p12342 ray12342
theorem signs12342 : ∀ j, Signs p12342 (bank12342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12343 := params 22
abbrev ray12343 := rays 22
def bank12343 : Fin 2 → Cell := twoBank p12343 ray12343
theorem signs12343 : ∀ j, Signs p12343 (bank12343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12344 := params 23
abbrev ray12344 := rays 23
def bank12344 : Fin 2 → Cell := twoBank p12344 ray12344
theorem signs12344 : ∀ j, Signs p12344 (bank12344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12345 := params 24
abbrev ray12345 := rays 24
def bank12345 : Fin 2 → Cell := twoBank p12345 ray12345
theorem signs12345 : ∀ j, Signs p12345 (bank12345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12346 := params 25
abbrev ray12346 := rays 25
def bank12346 : Fin 2 → Cell := twoBank p12346 ray12346
theorem signs12346 : ∀ j, Signs p12346 (bank12346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12347 := params 26
abbrev ray12347 := rays 26
def bank12347 : Fin 2 → Cell := twoBank p12347 ray12347
theorem signs12347 : ∀ j, Signs p12347 (bank12347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12348 := params 27
abbrev ray12348 := rays 27
def bank12348 : Fin 2 → Cell := twoBank p12348 ray12348
theorem signs12348 : ∀ j, Signs p12348 (bank12348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12349 := params 28
abbrev ray12349 := rays 28
def bank12349 : Fin 2 → Cell := twoBank p12349 ray12349
theorem signs12349 : ∀ j, Signs p12349 (bank12349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12350 := params 29
abbrev ray12350 := rays 29
def bank12350 : Fin 2 → Cell := twoBank p12350 ray12350
theorem signs12350 : ∀ j, Signs p12350 (bank12350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12351 := params 30
abbrev ray12351 := rays 30
def bank12351 : Fin 2 → Cell := twoBank p12351 ray12351
theorem signs12351 : ∀ j, Signs p12351 (bank12351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12352 := params 31
abbrev ray12352 := rays 31
def bank12352 : Fin 2 → Cell := twoBank p12352 ray12352
theorem signs12352 : ∀ j, Signs p12352 (bank12352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12321_12352
