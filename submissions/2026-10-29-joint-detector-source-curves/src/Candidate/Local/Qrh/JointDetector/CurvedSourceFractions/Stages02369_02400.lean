/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02369_02400
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99623385305545,99623196145633,99623006958523,99622817744217,99622628502716,99622439234022,99622249938136,99622060615059,99621871264793,99621681887339,99621492482698,99621303050872,99621113591862,99620924105670,99620734592297,99620545051744,99620355484013,99620165889105,99619976267021,99619786617763,99619596941332,99619407237730,99619217506958,99619027749017,99618837963909,99618648151635,99618458312196,99618268445594,99618078551830,99617888630906,99617698682823,99617508707582,99617318705185]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2368+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2369 := params 0
abbrev ray2369 := rays 0
def bank2369 : Fin 2 → Cell := twoBank p2369 ray2369
theorem signs2369 : ∀ j, Signs p2369 (bank2369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2370 := params 1
abbrev ray2370 := rays 1
def bank2370 : Fin 2 → Cell := twoBank p2370 ray2370
theorem signs2370 : ∀ j, Signs p2370 (bank2370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2371 := params 2
abbrev ray2371 := rays 2
def bank2371 : Fin 2 → Cell := twoBank p2371 ray2371
theorem signs2371 : ∀ j, Signs p2371 (bank2371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2372 := params 3
abbrev ray2372 := rays 3
def bank2372 : Fin 2 → Cell := twoBank p2372 ray2372
theorem signs2372 : ∀ j, Signs p2372 (bank2372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2373 := params 4
abbrev ray2373 := rays 4
def bank2373 : Fin 2 → Cell := twoBank p2373 ray2373
theorem signs2373 : ∀ j, Signs p2373 (bank2373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2374 := params 5
abbrev ray2374 := rays 5
def bank2374 : Fin 2 → Cell := twoBank p2374 ray2374
theorem signs2374 : ∀ j, Signs p2374 (bank2374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2375 := params 6
abbrev ray2375 := rays 6
def bank2375 : Fin 2 → Cell := twoBank p2375 ray2375
theorem signs2375 : ∀ j, Signs p2375 (bank2375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2376 := params 7
abbrev ray2376 := rays 7
def bank2376 : Fin 2 → Cell := twoBank p2376 ray2376
theorem signs2376 : ∀ j, Signs p2376 (bank2376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2377 := params 8
abbrev ray2377 := rays 8
def bank2377 : Fin 2 → Cell := twoBank p2377 ray2377
theorem signs2377 : ∀ j, Signs p2377 (bank2377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2378 := params 9
abbrev ray2378 := rays 9
def bank2378 : Fin 2 → Cell := twoBank p2378 ray2378
theorem signs2378 : ∀ j, Signs p2378 (bank2378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2379 := params 10
abbrev ray2379 := rays 10
def bank2379 : Fin 2 → Cell := twoBank p2379 ray2379
theorem signs2379 : ∀ j, Signs p2379 (bank2379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2380 := params 11
abbrev ray2380 := rays 11
def bank2380 : Fin 2 → Cell := twoBank p2380 ray2380
theorem signs2380 : ∀ j, Signs p2380 (bank2380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2381 := params 12
abbrev ray2381 := rays 12
def bank2381 : Fin 2 → Cell := twoBank p2381 ray2381
theorem signs2381 : ∀ j, Signs p2381 (bank2381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2382 := params 13
abbrev ray2382 := rays 13
def bank2382 : Fin 2 → Cell := twoBank p2382 ray2382
theorem signs2382 : ∀ j, Signs p2382 (bank2382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2383 := params 14
abbrev ray2383 := rays 14
def bank2383 : Fin 2 → Cell := twoBank p2383 ray2383
theorem signs2383 : ∀ j, Signs p2383 (bank2383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2384 := params 15
abbrev ray2384 := rays 15
def bank2384 : Fin 2 → Cell := twoBank p2384 ray2384
theorem signs2384 : ∀ j, Signs p2384 (bank2384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2385 := params 16
abbrev ray2385 := rays 16
def bank2385 : Fin 2 → Cell := twoBank p2385 ray2385
theorem signs2385 : ∀ j, Signs p2385 (bank2385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2386 := params 17
abbrev ray2386 := rays 17
def bank2386 : Fin 2 → Cell := twoBank p2386 ray2386
theorem signs2386 : ∀ j, Signs p2386 (bank2386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2387 := params 18
abbrev ray2387 := rays 18
def bank2387 : Fin 2 → Cell := twoBank p2387 ray2387
theorem signs2387 : ∀ j, Signs p2387 (bank2387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2388 := params 19
abbrev ray2388 := rays 19
def bank2388 : Fin 2 → Cell := twoBank p2388 ray2388
theorem signs2388 : ∀ j, Signs p2388 (bank2388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2389 := params 20
abbrev ray2389 := rays 20
def bank2389 : Fin 2 → Cell := twoBank p2389 ray2389
theorem signs2389 : ∀ j, Signs p2389 (bank2389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2390 := params 21
abbrev ray2390 := rays 21
def bank2390 : Fin 2 → Cell := twoBank p2390 ray2390
theorem signs2390 : ∀ j, Signs p2390 (bank2390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2391 := params 22
abbrev ray2391 := rays 22
def bank2391 : Fin 2 → Cell := twoBank p2391 ray2391
theorem signs2391 : ∀ j, Signs p2391 (bank2391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2392 := params 23
abbrev ray2392 := rays 23
def bank2392 : Fin 2 → Cell := twoBank p2392 ray2392
theorem signs2392 : ∀ j, Signs p2392 (bank2392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2393 := params 24
abbrev ray2393 := rays 24
def bank2393 : Fin 2 → Cell := twoBank p2393 ray2393
theorem signs2393 : ∀ j, Signs p2393 (bank2393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2394 := params 25
abbrev ray2394 := rays 25
def bank2394 : Fin 2 → Cell := twoBank p2394 ray2394
theorem signs2394 : ∀ j, Signs p2394 (bank2394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2395 := params 26
abbrev ray2395 := rays 26
def bank2395 : Fin 2 → Cell := twoBank p2395 ray2395
theorem signs2395 : ∀ j, Signs p2395 (bank2395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2396 := params 27
abbrev ray2396 := rays 27
def bank2396 : Fin 2 → Cell := twoBank p2396 ray2396
theorem signs2396 : ∀ j, Signs p2396 (bank2396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2397 := params 28
abbrev ray2397 := rays 28
def bank2397 : Fin 2 → Cell := twoBank p2397 ray2397
theorem signs2397 : ∀ j, Signs p2397 (bank2397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2398 := params 29
abbrev ray2398 := rays 29
def bank2398 : Fin 2 → Cell := twoBank p2398 ray2398
theorem signs2398 : ∀ j, Signs p2398 (bank2398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2399 := params 30
abbrev ray2399 := rays 30
def bank2399 : Fin 2 → Cell := twoBank p2399 ray2399
theorem signs2399 : ∀ j, Signs p2399 (bank2399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2400 := params 31
abbrev ray2400 := rays 31
def bank2400 : Fin 2 → Cell := twoBank p2400 ray2400
theorem signs2400 : ∀ j, Signs p2400 (bank2400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02369_02400
