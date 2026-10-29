/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02337_02368
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99629424054114,99629235765256,99629047449156,99628859105816,99628670735236,99628482337419,99628293912365,99628105460076,99627916980554,99627728473800,99627539939815,99627351378600,99627162790157,99626974174488,99626785531593,99626596861474,99626408164133,99626219439571,99626030687789,99625841908789,99625653102572,99625464269139,99625275408492,99625086520632,99624897605561,99624708663280,99624519693790,99624330697093,99624141673190,99623952622082,99623763543771,99623574438258,99623385305545]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2336+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2337 := params 0
abbrev ray2337 := rays 0
def bank2337 : Fin 2 → Cell := twoBank p2337 ray2337
theorem signs2337 : ∀ j, Signs p2337 (bank2337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2338 := params 1
abbrev ray2338 := rays 1
def bank2338 : Fin 2 → Cell := twoBank p2338 ray2338
theorem signs2338 : ∀ j, Signs p2338 (bank2338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2339 := params 2
abbrev ray2339 := rays 2
def bank2339 : Fin 2 → Cell := twoBank p2339 ray2339
theorem signs2339 : ∀ j, Signs p2339 (bank2339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2340 := params 3
abbrev ray2340 := rays 3
def bank2340 : Fin 2 → Cell := twoBank p2340 ray2340
theorem signs2340 : ∀ j, Signs p2340 (bank2340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2341 := params 4
abbrev ray2341 := rays 4
def bank2341 : Fin 2 → Cell := twoBank p2341 ray2341
theorem signs2341 : ∀ j, Signs p2341 (bank2341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2342 := params 5
abbrev ray2342 := rays 5
def bank2342 : Fin 2 → Cell := twoBank p2342 ray2342
theorem signs2342 : ∀ j, Signs p2342 (bank2342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2343 := params 6
abbrev ray2343 := rays 6
def bank2343 : Fin 2 → Cell := twoBank p2343 ray2343
theorem signs2343 : ∀ j, Signs p2343 (bank2343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2344 := params 7
abbrev ray2344 := rays 7
def bank2344 : Fin 2 → Cell := twoBank p2344 ray2344
theorem signs2344 : ∀ j, Signs p2344 (bank2344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2345 := params 8
abbrev ray2345 := rays 8
def bank2345 : Fin 2 → Cell := twoBank p2345 ray2345
theorem signs2345 : ∀ j, Signs p2345 (bank2345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2346 := params 9
abbrev ray2346 := rays 9
def bank2346 : Fin 2 → Cell := twoBank p2346 ray2346
theorem signs2346 : ∀ j, Signs p2346 (bank2346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2347 := params 10
abbrev ray2347 := rays 10
def bank2347 : Fin 2 → Cell := twoBank p2347 ray2347
theorem signs2347 : ∀ j, Signs p2347 (bank2347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2348 := params 11
abbrev ray2348 := rays 11
def bank2348 : Fin 2 → Cell := twoBank p2348 ray2348
theorem signs2348 : ∀ j, Signs p2348 (bank2348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2349 := params 12
abbrev ray2349 := rays 12
def bank2349 : Fin 2 → Cell := twoBank p2349 ray2349
theorem signs2349 : ∀ j, Signs p2349 (bank2349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2350 := params 13
abbrev ray2350 := rays 13
def bank2350 : Fin 2 → Cell := twoBank p2350 ray2350
theorem signs2350 : ∀ j, Signs p2350 (bank2350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2351 := params 14
abbrev ray2351 := rays 14
def bank2351 : Fin 2 → Cell := twoBank p2351 ray2351
theorem signs2351 : ∀ j, Signs p2351 (bank2351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2352 := params 15
abbrev ray2352 := rays 15
def bank2352 : Fin 2 → Cell := twoBank p2352 ray2352
theorem signs2352 : ∀ j, Signs p2352 (bank2352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2353 := params 16
abbrev ray2353 := rays 16
def bank2353 : Fin 2 → Cell := twoBank p2353 ray2353
theorem signs2353 : ∀ j, Signs p2353 (bank2353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2354 := params 17
abbrev ray2354 := rays 17
def bank2354 : Fin 2 → Cell := twoBank p2354 ray2354
theorem signs2354 : ∀ j, Signs p2354 (bank2354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2355 := params 18
abbrev ray2355 := rays 18
def bank2355 : Fin 2 → Cell := twoBank p2355 ray2355
theorem signs2355 : ∀ j, Signs p2355 (bank2355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2356 := params 19
abbrev ray2356 := rays 19
def bank2356 : Fin 2 → Cell := twoBank p2356 ray2356
theorem signs2356 : ∀ j, Signs p2356 (bank2356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2357 := params 20
abbrev ray2357 := rays 20
def bank2357 : Fin 2 → Cell := twoBank p2357 ray2357
theorem signs2357 : ∀ j, Signs p2357 (bank2357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2358 := params 21
abbrev ray2358 := rays 21
def bank2358 : Fin 2 → Cell := twoBank p2358 ray2358
theorem signs2358 : ∀ j, Signs p2358 (bank2358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2359 := params 22
abbrev ray2359 := rays 22
def bank2359 : Fin 2 → Cell := twoBank p2359 ray2359
theorem signs2359 : ∀ j, Signs p2359 (bank2359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2360 := params 23
abbrev ray2360 := rays 23
def bank2360 : Fin 2 → Cell := twoBank p2360 ray2360
theorem signs2360 : ∀ j, Signs p2360 (bank2360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2361 := params 24
abbrev ray2361 := rays 24
def bank2361 : Fin 2 → Cell := twoBank p2361 ray2361
theorem signs2361 : ∀ j, Signs p2361 (bank2361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2362 := params 25
abbrev ray2362 := rays 25
def bank2362 : Fin 2 → Cell := twoBank p2362 ray2362
theorem signs2362 : ∀ j, Signs p2362 (bank2362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2363 := params 26
abbrev ray2363 := rays 26
def bank2363 : Fin 2 → Cell := twoBank p2363 ray2363
theorem signs2363 : ∀ j, Signs p2363 (bank2363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2364 := params 27
abbrev ray2364 := rays 27
def bank2364 : Fin 2 → Cell := twoBank p2364 ray2364
theorem signs2364 : ∀ j, Signs p2364 (bank2364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2365 := params 28
abbrev ray2365 := rays 28
def bank2365 : Fin 2 → Cell := twoBank p2365 ray2365
theorem signs2365 : ∀ j, Signs p2365 (bank2365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2366 := params 29
abbrev ray2366 := rays 29
def bank2366 : Fin 2 → Cell := twoBank p2366 ray2366
theorem signs2366 : ∀ j, Signs p2366 (bank2366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2367 := params 30
abbrev ray2367 := rays 30
def bank2367 : Fin 2 → Cell := twoBank p2367 ray2367
theorem signs2367 : ∀ j, Signs p2367 (bank2367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2368 := params 31
abbrev ray2368 := rays 31
def bank2368 : Fin 2 → Cell := twoBank p2368 ray2368
theorem signs2368 : ∀ j, Signs p2368 (bank2368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02337_02368
