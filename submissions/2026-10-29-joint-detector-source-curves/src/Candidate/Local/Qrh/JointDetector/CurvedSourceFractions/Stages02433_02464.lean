/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02433_02464
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99611224298195,99611033400412,99610842475519,99610651523518,99610460544410,99610269538197,99610078504880,99609887444460,99609696356938,99609505242316,99609314100596,99609122931778,99608931735865,99608740512857,99608549262756,99608357985563,99608166681280,99607975349908,99607783991448,99607592605901,99607401193270,99607209753555,99607018286758,99606826792880,99606635271922,99606443723886,99606252148773,99606060546585,99605868917323,99605677260988,99605485577582,99605293867106,99605102129561]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2432+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2433 := params 0
abbrev ray2433 := rays 0
def bank2433 : Fin 2 → Cell := twoBank p2433 ray2433
theorem signs2433 : ∀ j, Signs p2433 (bank2433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2434 := params 1
abbrev ray2434 := rays 1
def bank2434 : Fin 2 → Cell := twoBank p2434 ray2434
theorem signs2434 : ∀ j, Signs p2434 (bank2434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2435 := params 2
abbrev ray2435 := rays 2
def bank2435 : Fin 2 → Cell := twoBank p2435 ray2435
theorem signs2435 : ∀ j, Signs p2435 (bank2435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2436 := params 3
abbrev ray2436 := rays 3
def bank2436 : Fin 2 → Cell := twoBank p2436 ray2436
theorem signs2436 : ∀ j, Signs p2436 (bank2436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2437 := params 4
abbrev ray2437 := rays 4
def bank2437 : Fin 2 → Cell := twoBank p2437 ray2437
theorem signs2437 : ∀ j, Signs p2437 (bank2437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2438 := params 5
abbrev ray2438 := rays 5
def bank2438 : Fin 2 → Cell := twoBank p2438 ray2438
theorem signs2438 : ∀ j, Signs p2438 (bank2438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2439 := params 6
abbrev ray2439 := rays 6
def bank2439 : Fin 2 → Cell := twoBank p2439 ray2439
theorem signs2439 : ∀ j, Signs p2439 (bank2439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2440 := params 7
abbrev ray2440 := rays 7
def bank2440 : Fin 2 → Cell := twoBank p2440 ray2440
theorem signs2440 : ∀ j, Signs p2440 (bank2440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2441 := params 8
abbrev ray2441 := rays 8
def bank2441 : Fin 2 → Cell := twoBank p2441 ray2441
theorem signs2441 : ∀ j, Signs p2441 (bank2441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2442 := params 9
abbrev ray2442 := rays 9
def bank2442 : Fin 2 → Cell := twoBank p2442 ray2442
theorem signs2442 : ∀ j, Signs p2442 (bank2442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2443 := params 10
abbrev ray2443 := rays 10
def bank2443 : Fin 2 → Cell := twoBank p2443 ray2443
theorem signs2443 : ∀ j, Signs p2443 (bank2443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2444 := params 11
abbrev ray2444 := rays 11
def bank2444 : Fin 2 → Cell := twoBank p2444 ray2444
theorem signs2444 : ∀ j, Signs p2444 (bank2444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2445 := params 12
abbrev ray2445 := rays 12
def bank2445 : Fin 2 → Cell := twoBank p2445 ray2445
theorem signs2445 : ∀ j, Signs p2445 (bank2445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2446 := params 13
abbrev ray2446 := rays 13
def bank2446 : Fin 2 → Cell := twoBank p2446 ray2446
theorem signs2446 : ∀ j, Signs p2446 (bank2446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2447 := params 14
abbrev ray2447 := rays 14
def bank2447 : Fin 2 → Cell := twoBank p2447 ray2447
theorem signs2447 : ∀ j, Signs p2447 (bank2447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2448 := params 15
abbrev ray2448 := rays 15
def bank2448 : Fin 2 → Cell := twoBank p2448 ray2448
theorem signs2448 : ∀ j, Signs p2448 (bank2448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2449 := params 16
abbrev ray2449 := rays 16
def bank2449 : Fin 2 → Cell := twoBank p2449 ray2449
theorem signs2449 : ∀ j, Signs p2449 (bank2449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2450 := params 17
abbrev ray2450 := rays 17
def bank2450 : Fin 2 → Cell := twoBank p2450 ray2450
theorem signs2450 : ∀ j, Signs p2450 (bank2450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2451 := params 18
abbrev ray2451 := rays 18
def bank2451 : Fin 2 → Cell := twoBank p2451 ray2451
theorem signs2451 : ∀ j, Signs p2451 (bank2451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2452 := params 19
abbrev ray2452 := rays 19
def bank2452 : Fin 2 → Cell := twoBank p2452 ray2452
theorem signs2452 : ∀ j, Signs p2452 (bank2452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2453 := params 20
abbrev ray2453 := rays 20
def bank2453 : Fin 2 → Cell := twoBank p2453 ray2453
theorem signs2453 : ∀ j, Signs p2453 (bank2453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2454 := params 21
abbrev ray2454 := rays 21
def bank2454 : Fin 2 → Cell := twoBank p2454 ray2454
theorem signs2454 : ∀ j, Signs p2454 (bank2454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2455 := params 22
abbrev ray2455 := rays 22
def bank2455 : Fin 2 → Cell := twoBank p2455 ray2455
theorem signs2455 : ∀ j, Signs p2455 (bank2455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2456 := params 23
abbrev ray2456 := rays 23
def bank2456 : Fin 2 → Cell := twoBank p2456 ray2456
theorem signs2456 : ∀ j, Signs p2456 (bank2456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2457 := params 24
abbrev ray2457 := rays 24
def bank2457 : Fin 2 → Cell := twoBank p2457 ray2457
theorem signs2457 : ∀ j, Signs p2457 (bank2457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2458 := params 25
abbrev ray2458 := rays 25
def bank2458 : Fin 2 → Cell := twoBank p2458 ray2458
theorem signs2458 : ∀ j, Signs p2458 (bank2458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2459 := params 26
abbrev ray2459 := rays 26
def bank2459 : Fin 2 → Cell := twoBank p2459 ray2459
theorem signs2459 : ∀ j, Signs p2459 (bank2459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2460 := params 27
abbrev ray2460 := rays 27
def bank2460 : Fin 2 → Cell := twoBank p2460 ray2460
theorem signs2460 : ∀ j, Signs p2460 (bank2460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2461 := params 28
abbrev ray2461 := rays 28
def bank2461 : Fin 2 → Cell := twoBank p2461 ray2461
theorem signs2461 : ∀ j, Signs p2461 (bank2461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2462 := params 29
abbrev ray2462 := rays 29
def bank2462 : Fin 2 → Cell := twoBank p2462 ray2462
theorem signs2462 : ∀ j, Signs p2462 (bank2462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2463 := params 30
abbrev ray2463 := rays 30
def bank2463 : Fin 2 → Cell := twoBank p2463 ray2463
theorem signs2463 : ∀ j, Signs p2463 (bank2463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2464 := params 31
abbrev ray2464 := rays 31
def bank2464 : Fin 2 → Cell := twoBank p2464 ray2464
theorem signs2464 : ∀ j, Signs p2464 (bank2464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02433_02464
