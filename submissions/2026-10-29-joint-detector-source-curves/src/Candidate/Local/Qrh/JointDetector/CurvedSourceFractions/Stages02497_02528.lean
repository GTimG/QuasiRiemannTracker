/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02497_02528
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99598952244079,99598759614036,99598566956970,99598374272883,99598181561777,99597988823652,99597796058511,99597603266354,99597410447183,99597217600999,99597024727804,99596831827599,99596638900385,99596445946164,99596252964937,99596059956705,99595866921470,99595673859233,99595480769995,99595287653758,99595094510523,99594901340292,99594708143065,99594514918845,99594321667632,99594128389428,99593935084234,99593741752052,99593548392883,99593355006728,99593161593589,99592968153467,99592774686363]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2496+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2497 := params 0
abbrev ray2497 := rays 0
def bank2497 : Fin 2 → Cell := twoBank p2497 ray2497
theorem signs2497 : ∀ j, Signs p2497 (bank2497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2498 := params 1
abbrev ray2498 := rays 1
def bank2498 : Fin 2 → Cell := twoBank p2498 ray2498
theorem signs2498 : ∀ j, Signs p2498 (bank2498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2499 := params 2
abbrev ray2499 := rays 2
def bank2499 : Fin 2 → Cell := twoBank p2499 ray2499
theorem signs2499 : ∀ j, Signs p2499 (bank2499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2500 := params 3
abbrev ray2500 := rays 3
def bank2500 : Fin 2 → Cell := twoBank p2500 ray2500
theorem signs2500 : ∀ j, Signs p2500 (bank2500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2501 := params 4
abbrev ray2501 := rays 4
def bank2501 : Fin 2 → Cell := twoBank p2501 ray2501
theorem signs2501 : ∀ j, Signs p2501 (bank2501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2502 := params 5
abbrev ray2502 := rays 5
def bank2502 : Fin 2 → Cell := twoBank p2502 ray2502
theorem signs2502 : ∀ j, Signs p2502 (bank2502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2503 := params 6
abbrev ray2503 := rays 6
def bank2503 : Fin 2 → Cell := twoBank p2503 ray2503
theorem signs2503 : ∀ j, Signs p2503 (bank2503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2504 := params 7
abbrev ray2504 := rays 7
def bank2504 : Fin 2 → Cell := twoBank p2504 ray2504
theorem signs2504 : ∀ j, Signs p2504 (bank2504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2505 := params 8
abbrev ray2505 := rays 8
def bank2505 : Fin 2 → Cell := twoBank p2505 ray2505
theorem signs2505 : ∀ j, Signs p2505 (bank2505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2506 := params 9
abbrev ray2506 := rays 9
def bank2506 : Fin 2 → Cell := twoBank p2506 ray2506
theorem signs2506 : ∀ j, Signs p2506 (bank2506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2507 := params 10
abbrev ray2507 := rays 10
def bank2507 : Fin 2 → Cell := twoBank p2507 ray2507
theorem signs2507 : ∀ j, Signs p2507 (bank2507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2508 := params 11
abbrev ray2508 := rays 11
def bank2508 : Fin 2 → Cell := twoBank p2508 ray2508
theorem signs2508 : ∀ j, Signs p2508 (bank2508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2509 := params 12
abbrev ray2509 := rays 12
def bank2509 : Fin 2 → Cell := twoBank p2509 ray2509
theorem signs2509 : ∀ j, Signs p2509 (bank2509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2510 := params 13
abbrev ray2510 := rays 13
def bank2510 : Fin 2 → Cell := twoBank p2510 ray2510
theorem signs2510 : ∀ j, Signs p2510 (bank2510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2511 := params 14
abbrev ray2511 := rays 14
def bank2511 : Fin 2 → Cell := twoBank p2511 ray2511
theorem signs2511 : ∀ j, Signs p2511 (bank2511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2512 := params 15
abbrev ray2512 := rays 15
def bank2512 : Fin 2 → Cell := twoBank p2512 ray2512
theorem signs2512 : ∀ j, Signs p2512 (bank2512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2513 := params 16
abbrev ray2513 := rays 16
def bank2513 : Fin 2 → Cell := twoBank p2513 ray2513
theorem signs2513 : ∀ j, Signs p2513 (bank2513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2514 := params 17
abbrev ray2514 := rays 17
def bank2514 : Fin 2 → Cell := twoBank p2514 ray2514
theorem signs2514 : ∀ j, Signs p2514 (bank2514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2515 := params 18
abbrev ray2515 := rays 18
def bank2515 : Fin 2 → Cell := twoBank p2515 ray2515
theorem signs2515 : ∀ j, Signs p2515 (bank2515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2516 := params 19
abbrev ray2516 := rays 19
def bank2516 : Fin 2 → Cell := twoBank p2516 ray2516
theorem signs2516 : ∀ j, Signs p2516 (bank2516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2517 := params 20
abbrev ray2517 := rays 20
def bank2517 : Fin 2 → Cell := twoBank p2517 ray2517
theorem signs2517 : ∀ j, Signs p2517 (bank2517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2518 := params 21
abbrev ray2518 := rays 21
def bank2518 : Fin 2 → Cell := twoBank p2518 ray2518
theorem signs2518 : ∀ j, Signs p2518 (bank2518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2519 := params 22
abbrev ray2519 := rays 22
def bank2519 : Fin 2 → Cell := twoBank p2519 ray2519
theorem signs2519 : ∀ j, Signs p2519 (bank2519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2520 := params 23
abbrev ray2520 := rays 23
def bank2520 : Fin 2 → Cell := twoBank p2520 ray2520
theorem signs2520 : ∀ j, Signs p2520 (bank2520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2521 := params 24
abbrev ray2521 := rays 24
def bank2521 : Fin 2 → Cell := twoBank p2521 ray2521
theorem signs2521 : ∀ j, Signs p2521 (bank2521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2522 := params 25
abbrev ray2522 := rays 25
def bank2522 : Fin 2 → Cell := twoBank p2522 ray2522
theorem signs2522 : ∀ j, Signs p2522 (bank2522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2523 := params 26
abbrev ray2523 := rays 26
def bank2523 : Fin 2 → Cell := twoBank p2523 ray2523
theorem signs2523 : ∀ j, Signs p2523 (bank2523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2524 := params 27
abbrev ray2524 := rays 27
def bank2524 : Fin 2 → Cell := twoBank p2524 ray2524
theorem signs2524 : ∀ j, Signs p2524 (bank2524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2525 := params 28
abbrev ray2525 := rays 28
def bank2525 : Fin 2 → Cell := twoBank p2525 ray2525
theorem signs2525 : ∀ j, Signs p2525 (bank2525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2526 := params 29
abbrev ray2526 := rays 29
def bank2526 : Fin 2 → Cell := twoBank p2526 ray2526
theorem signs2526 : ∀ j, Signs p2526 (bank2526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2527 := params 30
abbrev ray2527 := rays 30
def bank2527 : Fin 2 → Cell := twoBank p2527 ray2527
theorem signs2527 : ∀ j, Signs p2527 (bank2527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2528 := params 31
abbrev ray2528 := rays 31
def bank2528 : Fin 2 → Cell := twoBank p2528 ray2528
theorem signs2528 : ∀ j, Signs p2528 (bank2528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02497_02528
