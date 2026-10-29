/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02465_02496
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99605102129561,99604910364949,99604718573271,99604526754529,99604334908724,99604143035857,99603951135930,99603759208944,99603567254900,99603375273800,99603183265645,99602991230436,99602799168175,99602607078863,99602414962501,99602222819091,99602030648635,99601838451133,99601646226587,99601453974998,99601261696368,99601069390698,99600877057989,99600684698243,99600492311461,99600299897645,99600107456796,99599914988915,99599722494003,99599529972062,99599337423094,99599144847099,99598952244079]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2464+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2465 := params 0
abbrev ray2465 := rays 0
def bank2465 : Fin 2 → Cell := twoBank p2465 ray2465
theorem signs2465 : ∀ j, Signs p2465 (bank2465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2466 := params 1
abbrev ray2466 := rays 1
def bank2466 : Fin 2 → Cell := twoBank p2466 ray2466
theorem signs2466 : ∀ j, Signs p2466 (bank2466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2467 := params 2
abbrev ray2467 := rays 2
def bank2467 : Fin 2 → Cell := twoBank p2467 ray2467
theorem signs2467 : ∀ j, Signs p2467 (bank2467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2468 := params 3
abbrev ray2468 := rays 3
def bank2468 : Fin 2 → Cell := twoBank p2468 ray2468
theorem signs2468 : ∀ j, Signs p2468 (bank2468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2469 := params 4
abbrev ray2469 := rays 4
def bank2469 : Fin 2 → Cell := twoBank p2469 ray2469
theorem signs2469 : ∀ j, Signs p2469 (bank2469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2470 := params 5
abbrev ray2470 := rays 5
def bank2470 : Fin 2 → Cell := twoBank p2470 ray2470
theorem signs2470 : ∀ j, Signs p2470 (bank2470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2471 := params 6
abbrev ray2471 := rays 6
def bank2471 : Fin 2 → Cell := twoBank p2471 ray2471
theorem signs2471 : ∀ j, Signs p2471 (bank2471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2472 := params 7
abbrev ray2472 := rays 7
def bank2472 : Fin 2 → Cell := twoBank p2472 ray2472
theorem signs2472 : ∀ j, Signs p2472 (bank2472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2473 := params 8
abbrev ray2473 := rays 8
def bank2473 : Fin 2 → Cell := twoBank p2473 ray2473
theorem signs2473 : ∀ j, Signs p2473 (bank2473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2474 := params 9
abbrev ray2474 := rays 9
def bank2474 : Fin 2 → Cell := twoBank p2474 ray2474
theorem signs2474 : ∀ j, Signs p2474 (bank2474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2475 := params 10
abbrev ray2475 := rays 10
def bank2475 : Fin 2 → Cell := twoBank p2475 ray2475
theorem signs2475 : ∀ j, Signs p2475 (bank2475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2476 := params 11
abbrev ray2476 := rays 11
def bank2476 : Fin 2 → Cell := twoBank p2476 ray2476
theorem signs2476 : ∀ j, Signs p2476 (bank2476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2477 := params 12
abbrev ray2477 := rays 12
def bank2477 : Fin 2 → Cell := twoBank p2477 ray2477
theorem signs2477 : ∀ j, Signs p2477 (bank2477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2478 := params 13
abbrev ray2478 := rays 13
def bank2478 : Fin 2 → Cell := twoBank p2478 ray2478
theorem signs2478 : ∀ j, Signs p2478 (bank2478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2479 := params 14
abbrev ray2479 := rays 14
def bank2479 : Fin 2 → Cell := twoBank p2479 ray2479
theorem signs2479 : ∀ j, Signs p2479 (bank2479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2480 := params 15
abbrev ray2480 := rays 15
def bank2480 : Fin 2 → Cell := twoBank p2480 ray2480
theorem signs2480 : ∀ j, Signs p2480 (bank2480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2481 := params 16
abbrev ray2481 := rays 16
def bank2481 : Fin 2 → Cell := twoBank p2481 ray2481
theorem signs2481 : ∀ j, Signs p2481 (bank2481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2482 := params 17
abbrev ray2482 := rays 17
def bank2482 : Fin 2 → Cell := twoBank p2482 ray2482
theorem signs2482 : ∀ j, Signs p2482 (bank2482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2483 := params 18
abbrev ray2483 := rays 18
def bank2483 : Fin 2 → Cell := twoBank p2483 ray2483
theorem signs2483 : ∀ j, Signs p2483 (bank2483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2484 := params 19
abbrev ray2484 := rays 19
def bank2484 : Fin 2 → Cell := twoBank p2484 ray2484
theorem signs2484 : ∀ j, Signs p2484 (bank2484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2485 := params 20
abbrev ray2485 := rays 20
def bank2485 : Fin 2 → Cell := twoBank p2485 ray2485
theorem signs2485 : ∀ j, Signs p2485 (bank2485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2486 := params 21
abbrev ray2486 := rays 21
def bank2486 : Fin 2 → Cell := twoBank p2486 ray2486
theorem signs2486 : ∀ j, Signs p2486 (bank2486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2487 := params 22
abbrev ray2487 := rays 22
def bank2487 : Fin 2 → Cell := twoBank p2487 ray2487
theorem signs2487 : ∀ j, Signs p2487 (bank2487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2488 := params 23
abbrev ray2488 := rays 23
def bank2488 : Fin 2 → Cell := twoBank p2488 ray2488
theorem signs2488 : ∀ j, Signs p2488 (bank2488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2489 := params 24
abbrev ray2489 := rays 24
def bank2489 : Fin 2 → Cell := twoBank p2489 ray2489
theorem signs2489 : ∀ j, Signs p2489 (bank2489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2490 := params 25
abbrev ray2490 := rays 25
def bank2490 : Fin 2 → Cell := twoBank p2490 ray2490
theorem signs2490 : ∀ j, Signs p2490 (bank2490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2491 := params 26
abbrev ray2491 := rays 26
def bank2491 : Fin 2 → Cell := twoBank p2491 ray2491
theorem signs2491 : ∀ j, Signs p2491 (bank2491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2492 := params 27
abbrev ray2492 := rays 27
def bank2492 : Fin 2 → Cell := twoBank p2492 ray2492
theorem signs2492 : ∀ j, Signs p2492 (bank2492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2493 := params 28
abbrev ray2493 := rays 28
def bank2493 : Fin 2 → Cell := twoBank p2493 ray2493
theorem signs2493 : ∀ j, Signs p2493 (bank2493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2494 := params 29
abbrev ray2494 := rays 29
def bank2494 : Fin 2 → Cell := twoBank p2494 ray2494
theorem signs2494 : ∀ j, Signs p2494 (bank2494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2495 := params 30
abbrev ray2495 := rays 30
def bank2495 : Fin 2 → Cell := twoBank p2495 ray2495
theorem signs2495 : ∀ j, Signs p2495 (bank2495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2496 := params 31
abbrev ray2496 := rays 31
def bank2496 : Fin 2 → Cell := twoBank p2496 ray2496
theorem signs2496 : ∀ j, Signs p2496 (bank2496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02465_02496
